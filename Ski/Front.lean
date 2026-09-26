import Lean
import Ski.Compile
open Term

/-!
# SKIjack's front end, for the core SKIlark's kernel is written in

`skijack` reads a source file, lowers its case forms and compiles each
declaration (`skijack/expand.py`).  This file does the same in Lean, for
the part of the language `skilark.joy.compiled` emits, so that the
kernel's source enters the development as the text `skijack` compiled
(`Ski/Source.lean`) and not as a hand transcription.

## The language

One declaration per line; `--` starts a comment to the end of the line.

    T === C1 f… | C2 f… | …        a type: constructors with field types
    f x1 … xn = e                  an equation
    f := e                         a definition
    e ::= name | e e | (e) | e |> { C b… e; … }

A case branch names a constructor and binds exactly as many binders as
the constructor has fields, so the parser reads branches with the arities
of the types declared above it.

## The passes

- `lex` splits a line into tokens, over code points.
- `parseFile` parses every line (`pExpr` and its siblings), with fuel
  proportional to the line's tokens, so every function is total and
  structural.
- `dExpr` lowers each case to its scrutinee applied to one continuation
  per constructor, **in declaration order**, each continuation the λ over
  that branch's binders (`_lower_case`).  A case whose branches do not
  cover one type's constructors exactly once is refused, as `skijack`
  refuses it.  Binders are numbered in source order, parameters first;
  an equation whose body names itself is recursive, with its
  self-reference the variable `0`.
- `compileFile` compiles every declaration: a constructor to `ctorO`, an
  equation to `compDef` or `compRec` (`Ski/Compile.lean`), once every
  global it names is compiled, as `skijack` expands globals to closed
  terms before abstraction.

Names are lists of code points; `nm! "wPop"` writes one.
-/

/-- A name, as its characters' code points. -/
abbrev Nm := List Nat

open Lean Elab Term in
/-- `nm! "wPop"`: a name written as a string literal, elaborated to its code
    points. -/
elab:max "nm! " s:str : term => return toExpr (s.getString.toList.map Char.toNat)

namespace Front

-- ---------------------------------------------------------------------------
-- Lexing
-- ---------------------------------------------------------------------------

inductive Tok
  | ident (s : Nm)
  | defTy
  | eq
  | assign
  | bar
  | pipe
  | lbrace
  | rbrace
  | semi
  | lparen
  | rparen
  deriving DecidableEq, Repr

/-- Letters, digits, `_` and `'`. -/
def identChar (c : Nat) : Bool :=
  (48 ≤ c && c ≤ 57) || (65 ≤ c && c ≤ 90) || (97 ≤ c && c ≤ 122) || c == 95 || c == 39

/-- End the identifier being read, if any. -/
def flush (acc : List Nat) (ts : List Tok) : List Tok :=
  if acc.isEmpty then ts else Tok.ident acc.reverse :: ts

/-- The tokens of one line; `acc` is the identifier being read, reversed. -/
def lex : List Nat → List Nat → Option (List Tok)
  | [], acc => some (flush acc [])
  | 45 :: 45 :: _, acc => some (flush acc [])
  | 61 :: 61 :: 61 :: r, acc => (flush acc [.defTy] ++ ·) <$> lex r []
  | 58 :: 61 :: r, acc => (flush acc [.assign] ++ ·) <$> lex r []
  | 124 :: 62 :: r, acc => (flush acc [.pipe] ++ ·) <$> lex r []
  | 124 :: r, acc => (flush acc [.bar] ++ ·) <$> lex r []
  | 61 :: r, acc => (flush acc [.eq] ++ ·) <$> lex r []
  | 123 :: r, acc => (flush acc [.lbrace] ++ ·) <$> lex r []
  | 125 :: r, acc => (flush acc [.rbrace] ++ ·) <$> lex r []
  | 59 :: r, acc => (flush acc [.semi] ++ ·) <$> lex r []
  | 40 :: r, acc => (flush acc [.lparen] ++ ·) <$> lex r []
  | 41 :: r, acc => (flush acc [.rparen] ++ ·) <$> lex r []
  | c :: r, acc =>
    if identChar c then lex r (c :: acc)
    else if c == 32 || c == 9 || c == 13 then (flush acc [] ++ ·) <$> lex r []
    else none

/-- The lines of a text; `cur` is the line being read, reversed. -/
def lines : List Nat → List Nat → List (List Nat)
  | [], cur => [cur.reverse]
  | 10 :: r, cur => cur.reverse :: lines r []
  | c :: r, cur => lines r (c :: cur)

-- ---------------------------------------------------------------------------
-- Syntax
-- ---------------------------------------------------------------------------

mutual
  inductive Expr
    | name (n : Nm)
    | app (f a : Expr)
    | case (e : Expr) (bs : Branches)
  /-- Case branches, in source order: constructor, binders, body. -/
  inductive Branches
    | nil
    | cons (c : Nm) (xs : List Nm) (body : Expr) (rest : Branches)
end

/-- A type: its name and its constructors with their arities, in
    declaration order. -/
structure TypeDecl where
  name : Nm
  ctors : List (Nm × Nat)

/-- An equation `f x… = e`, or a definition `f := e` with no parameters. -/
structure Eqn where
  name : Nm
  params : List Nm
  body : Expr

inductive Decl
  | ty (d : TypeDecl)
  | eqn (e : Eqn)

-- ---------------------------------------------------------------------------
-- Parsing
-- ---------------------------------------------------------------------------

/-- The constructors of a type declaration: groups of identifiers
    separated by `|`, each a constructor and its fields. -/
def parseCtors : List Tok → List Nm → List (Nm × Nat) → Option (List (Nm × Nat))
  | [], cur, out =>
    match cur.reverse with
    | c :: fs => some (out.reverse ++ [(c, fs.length)])
    | [] => none
  | .bar :: r, cur, out =>
    match cur.reverse with
    | c :: fs => parseCtors r [] ((c, fs.length) :: out)
    | [] => none
  | .ident x :: r, cur, out => parseCtors r (x :: cur) out
  | _, _, _ => none

/-- Exactly `k` binders. -/
def takeIdents : Nat → List Tok → Option (List Nm × List Tok)
  | 0, ts => some ([], ts)
  | k + 1, .ident x :: r =>
    match takeIdents k r with
    | some (xs, r') => some (x :: xs, r')
    | none => none
  | _ + 1, _ => none

mutual
  /-- `e ::= app ('|>' '{' branches '}')*` -/
  def pExpr (ar : Nm → Option Nat) : Nat → List Tok → Option (Expr × List Tok)
    | 0, _ => none
    | f + 1, ts =>
      match pApp ar f ts with
      | some (e, r) => pCases ar f e r
      | none => none
  def pCases (ar : Nm → Option Nat) : Nat → Expr → List Tok → Option (Expr × List Tok)
    | 0, _, _ => none
    | f + 1, e, .pipe :: .lbrace :: r =>
      match pBranches ar f r with
      | some (bs, r') => pCases ar f (.case e bs) r'
      | none => none
    | _ + 1, e, r => some (e, r)
  /-- `app ::= atom atom*` -/
  def pApp (ar : Nm → Option Nat) : Nat → List Tok → Option (Expr × List Tok)
    | 0, _ => none
    | f + 1, ts =>
      match pAtom ar f ts with
      | some (a, r) => pMore ar f a r
      | none => none
  def pMore (ar : Nm → Option Nat) : Nat → Expr → List Tok → Option (Expr × List Tok)
    | 0, _, _ => none
    | f + 1, e, ts =>
      match pAtom ar f ts with
      | some (a, r) => pMore ar f (.app e a) r
      | none => some (e, ts)
  /-- `atom ::= name | '(' e ')'` -/
  def pAtom (ar : Nm → Option Nat) : Nat → List Tok → Option (Expr × List Tok)
    | 0, _ => none
    | _ + 1, .ident x :: r => some (.name x, r)
    | f + 1, .lparen :: r =>
      match pExpr ar f r with
      | some (e, .rparen :: r') => some (e, r')
      | _ => none
    | _ + 1, _ => none
  /-- `branches ::= C b^arity(C) e (';' …)* '}'` -/
  def pBranches (ar : Nm → Option Nat) : Nat → List Tok → Option (Branches × List Tok)
    | 0, _ => none
    | f + 1, .ident c :: r =>
      match ar c with
      | none => none
      | some k =>
        match takeIdents k r with
        | none => none
        | some (xs, r1) =>
          match pExpr ar f r1 with
          | some (body, .semi :: r2) =>
            match pBranches ar f r2 with
            | some (bs, r3) => some (.cons c xs body bs, r3)
            | none => none
          | some (body, .rbrace :: r2) => some (.cons c xs body .nil, r2)
          | _ => none
    | _ + 1, _ => none
end

/-- A constructor's arity, from the types declared so far. -/
def arity (tys : List TypeDecl) (c : Nm) : Option Nat :=
  match tys.find? (fun d => d.ctors.any (fun p => p.1 == c)) with
  | some d => (d.ctors.find? (fun p => p.1 == c)).map (·.2)
  | none => none

/-- An equation's name and parameters, up to `=`; or a definition's name, up
    to `:=`. -/
def pHead : List Tok → List Nm → Option (List Nm × List Tok)
  | .eq :: r, acc => some (acc.reverse, r)
  | .assign :: r, [] => some ([], r)
  | .ident x :: r, acc => pHead r (x :: acc)
  | _, _ => none

/-- One line: nothing, a type, or an equation whose body is all the rest. -/
def parseLine (tys : List TypeDecl) : List Tok → Option (Option Decl)
  | [] => some none
  | .ident n :: .defTy :: r => (fun cs => some (.ty ⟨n, cs⟩)) <$> parseCtors r [] []
  | .ident n :: r =>
    match pHead r [] with
    | none => none
    | some (ps, body) =>
      match pExpr (arity tys) (4 * body.length + 4) body with
      | some (e, []) => some (some (.eqn ⟨n, ps, e⟩))
      | _ => none
  | _ => none

def parseLines : List (List Nat) → List TypeDecl → Option (List Decl)
  | [], _ => some []
  | l :: ls, tys =>
    match lex l [] with
    | none => none
    | some ts =>
      match parseLine tys ts with
      | none => none
      | some none => parseLines ls tys
      | some (some (.ty d)) => (.ty d :: ·) <$> parseLines ls (tys ++ [d])
      | some (some d) => (d :: ·) <$> parseLines ls tys

/-- **The parser.**  A text, as code points, to its declarations. -/
def parseFile (src : List Nat) : Option (List Decl) := parseLines (lines src []) []

-- ---------------------------------------------------------------------------
-- Desugaring: case lowering, and binders numbered
-- ---------------------------------------------------------------------------

/-- `Src` with globals by name (`Ski/Compile.lean`). -/
inductive CSrc
  | glob (n : Nm)
  | var (x : Nat)
  | app (f a : CSrc)
  | lam (x : Nat) (b : CSrc)
  deriving DecidableEq, Repr

/-- Globals resolved to closed terms. -/
def CSrc.resolve (env : Nm → Term) : CSrc → Src
  | .glob n => .glob (env n)
  | .var x => .var x
  | .app f a => .app (f.resolve env) (a.resolve env)
  | .lam x b => .lam x (b.resolve env)

/-- The globals a term names. -/
def CSrc.globs : CSrc → List Nm
  | .glob n => [n]
  | .var _ => []
  | .app f a => f.globs ++ a.globs
  | .lam _ b => b.globs

/-- Binders numbered from `i`, innermost first. -/
def bindFrom : List Nm → Nat → List (Nm × Nat) → List (Nm × Nat)
  | [], _, sc => sc
  | x :: xs, i, sc => bindFrom xs (i + 1) ((x, i) :: sc)

/-- `λ i. λ i+1. … body`, `k` binders. -/
def lamChain (i : Nat) : Nat → CSrc → CSrc
  | 0, b => b
  | k + 1, b => .lam i (lamChain (i + 1) k b)

/-- No name twice. -/
def nodup : List Nm → Bool
  | [] => true
  | x :: xs => !(xs.contains x) && nodup xs

/-- The continuations of a case in declaration order, if its branches are
    one type's constructors, each exactly once. -/
def caseOrder (tys : List TypeDecl) (arms : List (Nm × CSrc)) : Option (List CSrc) :=
  match arms with
  | [] => none
  | (c, _) :: _ =>
    match tys.find? (fun d => d.ctors.any (fun p => p.1 == c)) with
    | none => none
    | some d =>
      if arms.all (fun a => d.ctors.any (fun p => p.1 == a.1)) &&
          nodup (arms.map (·.1)) && arms.length == d.ctors.length then
        d.ctors.mapM (fun p => (arms.find? (fun a => a.1 == p.1)).map (·.2))
      else none

mutual
  /-- Lower an expression in scope `sc`, numbering new binders from `k`;
      returns the next free number. -/
  def dExpr (tys : List TypeDecl) (sc : List (Nm × Nat)) : Expr → Nat → Option (CSrc × Nat)
    | .name n, k =>
      match sc.lookup n with
      | some x => some (.var x, k)
      | none => some (.glob n, k)
    | .app f a, k =>
      match dExpr tys sc f k with
      | none => none
      | some (f', k1) =>
        match dExpr tys sc a k1 with
        | none => none
        | some (a', k2) => some (.app f' a', k2)
    | .case e bs, k =>
      match dExpr tys sc e k with
      | none => none
      | some (e', k1) =>
        match dBranches tys sc bs k1 with
        | none => none
        | some (arms, k2) =>
          match caseOrder tys arms with
          | none => none
          | some ks => some (ks.foldl CSrc.app e', k2)
  def dBranches (tys : List TypeDecl) (sc : List (Nm × Nat)) :
      Branches → Nat → Option (List (Nm × CSrc) × Nat)
    | .nil, k => some ([], k)
    | .cons c xs body rest, k =>
      match dExpr tys (bindFrom xs k sc) body (k + xs.length) with
      | none => none
      | some (b, k1) =>
        match dBranches tys sc rest k1 with
        | none => none
        | some (r, k2) => some ((c, lamChain k xs.length b) :: r, k2)
end

/-- An equation, lowered: its formals, its self-reference if recursive,
    and its body. -/
structure FEqn where
  params : List Nat
  self : Option Nat
  body : CSrc
  deriving DecidableEq, Repr

/-- **Lower an equation.**  Parameters are `0 … n-1`; if the body names the
    equation, it is recursive, its self-reference is `0` and its
    parameters `1 … n`. -/
def dEqn (tys : List TypeDecl) (e : Eqn) : Option FEqn :=
  let k := e.params.length
  match dExpr tys (bindFrom e.params 0 []) e.body k with
  | none => none
  | some (b0, _) =>
    if b0.globs.contains e.name then
      match dExpr tys (bindFrom e.params 1 [(e.name, 0)]) e.body (k + 1) with
      | none => none
      | some (b1, _) => some ⟨(List.range k).map (· + 1), some 0, b1⟩
    else some ⟨List.range k, none, b0⟩

/-- The types and equations of a file, in order. -/
def types : List Decl → List TypeDecl
  | [] => []
  | .ty d :: ds => d :: types ds
  | .eqn _ :: ds => types ds

def eqns : List Decl → List Eqn
  | [] => []
  | .ty _ :: ds => eqns ds
  | .eqn e :: ds => e :: eqns ds

/-- A file's equation, lowered. -/
def fileEqn (src : List Nat) (n : Nm) : Option FEqn :=
  match parseFile src with
  | none => none
  | some ds =>
    match (eqns ds).find? (fun e => e.name == n) with
    | none => none
    | some e => dEqn (types ds) e

-- ---------------------------------------------------------------------------
-- Compiling a file
-- ---------------------------------------------------------------------------

/-- A lowered equation, compiled with its globals resolved by `env`. -/
def FEqn.compile (env : Nm → Term) (e : FEqn) : Term :=
  match e.self with
  | some s => toTerm (compRec s e.params (e.body.resolve env))
  | none => toTerm (compDef e.params (e.body.resolve env))

/-- A type's constructors, compiled. -/
def ctorTerms (d : TypeDecl) : List (Nm × Term) :=
  List.zipWith (fun j p => (p.1, toTerm (ctorO p.2 j d.ctors.length)))
    (List.range d.ctors.length) d.ctors

/-- Compile each pending equation whose globals are all compiled; keep the
    rest pending. -/
def pass (done : List (Nm × Term)) : List (Nm × FEqn) → List (Nm × FEqn) × List (Nm × Term)
  | [] => ([], done)
  | (n, e) :: es =>
    if e.body.globs.all fun g => (done.lookup g).isSome then
      pass (done ++ [(n, e.compile fun g => (done.lookup g).getD K)]) es
    else
      let r := pass done es
      ((n, e) :: r.1, r.2)

def passes : Nat → List (Nm × Term) → List (Nm × FEqn) → List (Nm × Term)
  | 0, done, _ => done
  | k + 1, done, es =>
    let r := pass done es
    passes k r.2 r.1

/-- **Compile a file**: every constructor, and every equation whose globals
    are defined, each to the closed term `skijack` would emit. -/
def compileFile (src : List Nat) : Option (List (Nm × Term)) :=
  match parseFile src with
  | none => none
  | some ds =>
    let tys := types ds
    match (eqns ds).mapM (fun e => (dEqn tys e).map fun fe => (e.name, fe)) with
    | none => none
    | some es => some (passes (es.length + 1) ((tys.map ctorTerms).flatten) es)

/-- A name's term in a compiled file. -/
def termOf (file : Option (List (Nm × Term))) (n : Nm) : Option Term :=
  file.bind (·.lookup n)

-- ---------------------------------------------------------------------------
-- Case lowering refuses what `skijack` refuses, and follows declaration order
-- ---------------------------------------------------------------------------

/-- A case missing a constructor's branch is refused. -/
theorem refuses_incomplete :
    (fileEqn (nm! "t === A | B\nf x = x |> { A x }") (nm! "f")).isNone = true := by
  decide +kernel

/-- A case whose branches name two types' constructors is refused. -/
theorem refuses_mixed :
    (fileEqn (nm! "t === A | B\nu === C\nf x = x |> { A x; C x }") (nm! "f")).isNone = true := by
  decide +kernel

/-- A case with a constructor's branch twice is refused. -/
theorem refuses_repeated :
    (fileEqn (nm! "t === A | B\nf x = x |> { A x; A x; B x }") (nm! "f")).isNone = true := by
  decide +kernel

/-- Branches written in any order lower in declaration order: `B y` is
    written first and becomes the second continuation. -/
theorem lowers_in_declaration_order :
    fileEqn (nm! "t === A | B\nf x y = x |> { B y; A x }") (nm! "f") =
      some ⟨[0, 1], none, .app (.app (.var 0) (.var 0)) (.var 1)⟩ := by
  decide +kernel

end Front
