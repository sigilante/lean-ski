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

SKIjack's level 0, as `SPEC.md` §1–§5 and `skijack/parser.py`,
`skijack/lexicon.py` and `skijack/expand.py` define it:

    T === C1 f… | C2 f… | …         a type: constructors with field types
    f : T -> T …                    a signature, read and ignored
    f x1 … xn = e                   an equation
    f := e                          a definition
    c p… := { equation… }           a core: parameters prepended to each
    e ::= name | e e | (e) | e |> { C b… e; … } | \x.e | [e e …] | n@e

in either lexicon, ASCII or Unicode (`≡ ≔ ▹ → λ ⊑ ⍝`, and the Tier 1
glyphs `∘ ⇄ ⋈ Υ` for `B C W Y`), one lexicon per file, as `skijack`
reads it.  A newline ends a declaration except inside brackets.  A case
branch binds as many binders as its constructor has fields, read from
every type the file declares.  A cell `[a b c]` is `pair a (pair b c)`;
an axis pick `n@e` is the chain of `hd` and `tl` Nock's numbering gives.
Names resolve as `skijack` resolves them: a binder, then `S`, `K`, `I`
(always the ISA), then a sibling equation of the enclosing core, then a
program-level name (constructors, equations, definitions and the prelude
`pair hd tl nil cons zero suc`, which a program may redefine), then Tier
1 (`B C W Y`).  A core's equation is `core.eq`, and its bare name when no
other core defines it; an interpreter core's name is its `loop`.

Not read, and refused: macros (`:=*`), quotation and everything of level
1 (`< >`, `|-`, `?^`, `ns{`, fuel), qualified names, bare numbers.  A
program with an unresolved name, mutual recursion, or a name defined
twice is refused whole, as `skijack` refuses it.

## The passes

- `lexA` and `lexU` split a text into tokens, over code points, in the
  ASCII and Unicode lexicons.
- `parseWith` parses every declaration (`pExpr` and its siblings), with
  fuel proportional to the tokens, so every function is total and
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
  | num (n : Nat)
  | axis (n : Nat)
  | defTy
  | eq
  | assign
  | bar
  | pipe
  | arrow
  | colon
  | lam
  | dot
  | lbrace
  | rbrace
  | semi
  | lparen
  | rparen
  | lbrack
  | rbrack
  | nl
  deriving DecidableEq, Repr

def isLetter (c : Nat) : Bool := (65 ≤ c && c ≤ 90) || (97 ≤ c && c ≤ 122) || c == 95
def isDigit (c : Nat) : Bool := 48 ≤ c && c ≤ 57

/-- What the lexer is in the middle of. -/
inductive Mode
  | none
  | ident (acc : List Nat)
  | num (n : Nat)
  | comment

def flushM : Mode → List Tok
  | .ident acc => [.ident acc.reverse]
  | .num n => [.num n]
  | _ => []

/-- A letter, digit, `_` or `'`, in the middle of reading `m`. -/
def lexWord (c : Nat) : Mode → Option (List Tok × Mode)
  | .ident acc =>
    if isLetter c || isDigit c || c == 39 then some ([], .ident (c :: acc)) else none
  | .num n =>
    if isDigit c then some ([], .num (10 * n + (c - 48)))
    else if isLetter c then some ([.num n], .ident [c])
    else none
  | _ =>
    if isLetter c then some ([], .ident [c])
    else if isDigit c then some ([], .num (c - 48))
    else none

/-- The ASCII lexicon, maximal munch (`skijack/lexicon.py`). -/
def lexA : List Nat → Mode → List Tok → Option (List Tok)
  | [], m, acc => some ((flushM m).reverse ++ acc).reverse
  | c :: r, .comment, acc => if c == 10 then lexA r .none (.nl :: acc) else lexA r .comment acc
  | 45 :: 45 :: r, m, acc => lexA r .comment ((flushM m).reverse ++ acc)
  | 58 :: 61 :: 42 :: _, _, _ => none
  | 58 :: 61 :: 33 :: _, _, _ => none
  | 61 :: 61 :: 61 :: r, m, acc => lexA r .none ([.defTy] ++ (flushM m).reverse ++ acc)
  | 124 :: 62 :: r, m, acc => lexA r .none ([.pipe] ++ (flushM m).reverse ++ acc)
  | 124 :: 45 :: _, _, _ => none
  | 58 :: 61 :: r, m, acc => lexA r .none ([.assign] ++ (flushM m).reverse ++ acc)
  | 61 :: 62 :: _, _, _ => none
  | 45 :: 62 :: r, m, acc => lexA r .none ([.arrow] ++ (flushM m).reverse ++ acc)
  | 58 :: r, m, acc => lexA r .none ([.colon] ++ (flushM m).reverse ++ acc)
  | 61 :: r, m, acc => lexA r .none ([.eq] ++ (flushM m).reverse ++ acc)
  | 124 :: r, m, acc => lexA r .none ([.bar] ++ (flushM m).reverse ++ acc)
  | 92 :: r, m, acc => lexA r .none ([.lam] ++ (flushM m).reverse ++ acc)
  | 46 :: r, m, acc => lexA r .none ([.dot] ++ (flushM m).reverse ++ acc)
  | 59 :: r, m, acc => lexA r .none ([.semi] ++ (flushM m).reverse ++ acc)
  | 40 :: r, m, acc => lexA r .none ([.lparen] ++ (flushM m).reverse ++ acc)
  | 41 :: r, m, acc => lexA r .none ([.rparen] ++ (flushM m).reverse ++ acc)
  | 91 :: r, m, acc => lexA r .none ([.lbrack] ++ (flushM m).reverse ++ acc)
  | 93 :: r, m, acc => lexA r .none ([.rbrack] ++ (flushM m).reverse ++ acc)
  | 123 :: r, m, acc => lexA r .none ([.lbrace] ++ (flushM m).reverse ++ acc)
  | 125 :: r, m, acc => lexA r .none ([.rbrace] ++ (flushM m).reverse ++ acc)
  | 64 :: r, .num n, acc => lexA r .none (.axis n :: acc)
  | 10 :: r, m, acc => lexA r .none ([.nl] ++ (flushM m).reverse ++ acc)
  | c :: r, m, acc =>
    if c == 32 || c == 9 || c == 13 then lexA r .none ((flushM m).reverse ++ acc)
    else
      match lexWord c m with
      | some (ts, m') => lexA r m' (ts.reverse ++ acc)
      | none => none

/-- The Unicode lexicon: its own spellings, the Tier 1 glyphs, and
    subscript digits inside an identifier. -/
def lexU : List Nat → Mode → List Tok → Option (List Tok)
  | [], m, acc => some ((flushM m).reverse ++ acc).reverse
  | c :: r, .comment, acc => if c == 10 then lexU r .none (.nl :: acc) else lexU r .comment acc
  | 9053 :: r, m, acc => lexU r .comment ((flushM m).reverse ++ acc)
  | 8788 :: 42 :: _, _, _ => none
  | 8788 :: 33 :: _, _, _ => none
  | 8801 :: r, m, acc => lexU r .none ([.defTy] ++ (flushM m).reverse ++ acc)
  | 9657 :: r, m, acc => lexU r .none ([.pipe] ++ (flushM m).reverse ++ acc)
  | 8788 :: r, m, acc => lexU r .none ([.assign] ++ (flushM m).reverse ++ acc)
  | 8594 :: r, m, acc => lexU r .none ([.arrow] ++ (flushM m).reverse ++ acc)
  | 58 :: r, m, acc => lexU r .none ([.colon] ++ (flushM m).reverse ++ acc)
  | 61 :: r, m, acc => lexU r .none ([.eq] ++ (flushM m).reverse ++ acc)
  | 124 :: r, m, acc => lexU r .none ([.bar] ++ (flushM m).reverse ++ acc)
  | 955 :: r, m, acc => lexU r .none ([.lam] ++ (flushM m).reverse ++ acc)
  | 46 :: r, m, acc => lexU r .none ([.dot] ++ (flushM m).reverse ++ acc)
  | 59 :: r, m, acc => lexU r .none ([.semi] ++ (flushM m).reverse ++ acc)
  | 40 :: r, m, acc => lexU r .none ([.lparen] ++ (flushM m).reverse ++ acc)
  | 41 :: r, m, acc => lexU r .none ([.rparen] ++ (flushM m).reverse ++ acc)
  | 91 :: r, m, acc => lexU r .none ([.lbrack] ++ (flushM m).reverse ++ acc)
  | 93 :: r, m, acc => lexU r .none ([.rbrack] ++ (flushM m).reverse ++ acc)
  | 123 :: r, m, acc => lexU r .none ([.lbrace] ++ (flushM m).reverse ++ acc)
  | 125 :: r, m, acc => lexU r .none ([.rbrace] ++ (flushM m).reverse ++ acc)
  | 8728 :: r, m, acc => lexU r .none ([.ident [66]] ++ (flushM m).reverse ++ acc)
  | 8644 :: r, m, acc => lexU r .none ([.ident [67]] ++ (flushM m).reverse ++ acc)
  | 8904 :: r, m, acc => lexU r .none ([.ident [87]] ++ (flushM m).reverse ++ acc)
  | 933 :: r, m, acc => lexU r .none ([.ident [89]] ++ (flushM m).reverse ++ acc)
  | 8799 :: r, m, acc => lexU r .none ([.ident [69, 81]] ++ (flushM m).reverse ++ acc)
  | 8849 :: r, .num n, acc => lexU r .none (.axis n :: acc)
  | 10 :: r, m, acc => lexU r .none ([.nl] ++ (flushM m).reverse ++ acc)
  | c :: r, m, acc =>
    if c == 32 || c == 9 || c == 13 then lexU r .none ((flushM m).reverse ++ acc)
    else if 8320 ≤ c && c ≤ 8329 then
      match m with
      | .ident a => lexU r (.ident ((c - 8320 + 48) :: a)) acc
      | _ => none
    else
      match lexWord c m with
      | some (ts, m') => lexU r m' (ts.reverse ++ acc)
      | none => none

-- ---------------------------------------------------------------------------
-- Syntax
-- ---------------------------------------------------------------------------

mutual
  inductive Expr
    | name (n : Nm)
    | app (f a : Expr)
    | case (e : Expr) (bs : Branches)
    | lam (x : Nm) (b : Expr)
    | cell (items : Items)
    | pick (n : Nat) (e : Expr)
  /-- Case branches, in source order: constructor, binders, body. -/
  inductive Branches
    | nil
    | cons (c : Nm) (xs : List Nm) (body : Expr) (rest : Branches)
  /-- A cell's items. -/
  inductive Items
    | nil
    | cons (e : Expr) (rest : Items)
end

/-- A type: its name and its constructors with their arities, in
    declaration order. -/
structure TypeDecl where
  name : Nm
  ctors : List (Nm × Nat)

/-- An equation `f x… = e`, a definition `f := e` with no parameters, or
    a core's equation: then `name` is `core.f`, `bare` is `f`, `params`
    starts with the core's, and `sibs` are the core's equations. -/
structure Eqn where
  name : Nm
  bare : Nm
  params : List Nm
  body : Expr
  core : Option Nm
  sibs : List Nm

inductive Decl
  | ty (d : TypeDecl)
  | sig
  | eqn (e : Eqn)
  | core (name : Nm) (params : List Nm) (eqs : List (Nm × List Nm × Expr))

-- ---------------------------------------------------------------------------
-- Parsing
-- ---------------------------------------------------------------------------

/-- Newlines are invisible inside brackets. -/
def sk : Bool → List Tok → List Tok
  | true, .nl :: r => sk true r
  | _, ts => ts

def atomStart : Tok → Bool
  | .ident _ | .lparen | .lbrack | .axis _ | .lam | .num _ => true
  | _ => false

/-- The constructors of a type declaration, to the end of the line. -/
def parseCtors : List Tok → List Nm → List (Nm × Nat) → Option (List (Nm × Nat) × List Tok)
  | [], cur, out =>
    match cur.reverse with
    | c :: fs => some (out.reverse ++ [(c, fs.length)], [])
    | [] => none
  | .nl :: r, cur, out =>
    match cur.reverse with
    | c :: fs => some (out.reverse ++ [(c, fs.length)], .nl :: r)
    | [] => none
  | .bar :: r, cur, out =>
    match cur.reverse with
    | c :: fs => parseCtors r [] ((c, fs.length) :: out)
    | [] => none
  | .ident x :: r, cur, out => parseCtors r (x :: cur) out
  | _, _, _ => none

/-- Pass one: every type the file declares, wherever.  The scan goes on
    after each `===`: a constructor list never holds another `===`. -/
def collectTypes : List Tok → List TypeDecl → Option (List TypeDecl)
  | [], acc => some acc.reverse
  | .ident n :: .defTy :: r, acc =>
    match parseCtors r [] [] with
    | some (cs, _) => collectTypes r (⟨n, cs⟩ :: acc)
    | none => none
  | _ :: r, acc => collectTypes r acc

/-- Exactly `k` binders. -/
def takeIdents (d : Bool) : Nat → List Tok → Option (List Nm × List Tok)
  | 0, ts => some ([], ts)
  | k + 1, ts =>
    match sk d ts with
    | .ident x :: r =>
      match takeIdents d k r with
      | some (xs, r') => some (x :: xs, r')
      | none => none
    | _ => none

/-- The binary digits of an axis below its leading one: `false` for the
    head, `true` for the tail. -/
def axisSteps (n : Nat) : List Bool :=
  ((Nat.toDigits 2 n).drop 1).map (· == '1')

mutual
  /-- `e ::= app ('|>' '{' branches '}')*` -/
  def pExpr (ar : Nm → Option Nat) (d : Bool) : Nat → List Tok → Option (Expr × List Tok)
    | 0, _ => none
    | f + 1, ts =>
      match pApp ar d f ts with
      | some (e, r) => pCases ar d f e r
      | none => none
  def pCases (ar : Nm → Option Nat) (d : Bool) : Nat → Expr → List Tok → Option (Expr × List Tok)
    | 0, _, _ => none
    | f + 1, e, ts =>
      match sk d ts with
      | .pipe :: r =>
        match sk true r with
        | .lbrace :: r1 =>
          match pBranches ar f r1 with
          | some (bs, r2) => pCases ar d f (.case e bs) r2
          | none => none
        | _ => none
      | _ => some (e, ts)
  /-- `app ::= atom atom*` -/
  def pApp (ar : Nm → Option Nat) (d : Bool) : Nat → List Tok → Option (Expr × List Tok)
    | 0, _ => none
    | f + 1, ts =>
      match pAtom ar d f ts with
      | some (a, r) => pMore ar d f a r
      | none => none
  def pMore (ar : Nm → Option Nat) (d : Bool) : Nat → Expr → List Tok → Option (Expr × List Tok)
    | 0, _, _ => none
    | f + 1, e, ts =>
      match sk d ts with
      | t :: r =>
        if atomStart t then
          match pAtom ar d f (t :: r) with
          | some (a, r') => pMore ar d f (.app e a) r'
          | none => none
        else some (e, ts)
      | [] => some (e, [])
  /-- `atom ::= name | '(' e ')' | '[' atom atom+ ']' | n@atom | \x.e` -/
  def pAtom (ar : Nm → Option Nat) (d : Bool) : Nat → List Tok → Option (Expr × List Tok)
    | 0, _ => none
    | f + 1, ts =>
      match sk d ts with
      | .ident _ :: .dot :: .ident _ :: _ => none
      | .ident x :: r => some (.name x, r)
      | .lparen :: r =>
        match pExpr ar true f r with
        | some (e, r') =>
          match sk true r' with
          | .rparen :: r'' => some (e, r'')
          | _ => none
        | none => none
      | .lbrack :: r =>
        match pItems ar f r with
        | some (.cons a (.cons b rest), r') =>
          match sk true r' with
          | .rbrack :: r'' => some (.cell (.cons a (.cons b rest)), r'')
          | _ => none
        | _ => none
      | .axis n :: r =>
        match pAtom ar d f r with
        | some (e, r') => some (.pick n e, r')
        | none => none
      | .lam :: r =>
        match sk d r with
        | .ident x :: r1 =>
          match sk d r1 with
          | .dot :: r2 =>
            match pExpr ar d f r2 with
            | some (e, r3) => some (.lam x e, r3)
            | none => none
          | _ => none
        | _ => none
      | _ => none
  /-- A cell's items, atoms, newlines invisible. -/
  def pItems (ar : Nm → Option Nat) : Nat → List Tok → Option (Items × List Tok)
    | 0, _ => none
    | f + 1, ts =>
      match sk true ts with
      | t :: r =>
        if atomStart t then
          match pAtom ar true f (t :: r) with
          | some (a, r') =>
            match pItems ar f r' with
            | some (rest, r'') => some (.cons a rest, r'')
            | none => none
          | none => none
        else some (.nil, t :: r)
      | [] => some (.nil, [])
  /-- `branches ::= C b^arity(C) e (';' …)* '}'`, newlines invisible. -/
  def pBranches (ar : Nm → Option Nat) : Nat → List Tok → Option (Branches × List Tok)
    | 0, _ => none
    | f + 1, ts =>
      match sk true ts with
      | .ident c :: r =>
        match ar c with
        | none => none
        | some k =>
          match takeIdents true k r with
          | none => none
          | some (xs, r1) =>
            match pExpr ar true f r1 with
            | some (body, r2) =>
              match sk true r2 with
              | .semi :: r3 =>
                match pBranches ar f r3 with
                | some (bs, r4) => some (.cons c xs body bs, r4)
                | none => none
              | .rbrace :: r3 => some (.cons c xs body .nil, r3)
              | _ => none
            | none => none
      | _ => none
end

/-- A constructor's arity, from every type the file declares. -/
def arity (tys : List TypeDecl) (c : Nm) : Option Nat :=
  match tys.find? (fun d => d.ctors.any (fun p => p.1 == c)) with
  | some d => (d.ctors.find? (fun p => p.1 == c)).map (·.2)
  | none => none

/-- A declaration's leading names, up to its operator. -/
def pNames : List Tok → List Nm → Option (List Nm × List Tok)
  | .ident x :: r, acc => pNames r (x :: acc)
  | ts, acc => if acc.isEmpty then none else some (acc.reverse, ts)

/-- A declaration ends at a newline or the end. -/
def endDecl : List Tok → Bool
  | [] => true
  | .nl :: _ => true
  | _ => false

/-- A signature's types, `T (-> T)*`, to the end of the line. -/
def pSig : List Tok → Option (List Tok)
  | .ident _ :: .arrow :: r => pSig r
  | .ident _ :: r => if endDecl r then some r else none
  | _ => none

/-- A core's equations, `name binder* = e`, each ending at a newline or
    the closing brace. -/
def pCoreEqs (ar : Nm → Option Nat) : Nat → List Tok → Option (List (Nm × List Nm × Expr) × List Tok)
  | 0, _ => none
  | _ + 1, .rbrace :: r => some ([], r)
  | f + 1, .nl :: r => pCoreEqs ar f r
  | f + 1, ts =>
    match pNames ts [] with
    | some (n :: ps, .eq :: r) =>
      match pExpr ar false f r with
      | some (e, r') =>
        match r' with
        | .nl :: r'' =>
          match pCoreEqs ar f r'' with
          | some (eqs, rest) => some ((n, ps, e) :: eqs, rest)
          | none => none
        | .rbrace :: r'' => some ([(n, ps, e)], r'')
        | _ => none
      | none => none
    | _ => none

/-- One declaration. -/
def pDecl (ar : Nm → Option Nat) (f : Nat) (ts : List Tok) : Option (Decl × List Tok) :=
  match pNames ts [] with
  | some ([n], .defTy :: r) =>
    match parseCtors r [] [] with
    | some (cs, rest) => some (.ty ⟨n, cs⟩, rest)
    | none => none
  | some ([_], .colon :: r) =>
    match pSig r with
    | some rest => some (.sig, rest)
    | none => none
  | some (n :: ps, .assign :: .lbrace :: r) =>
    match pCoreEqs ar f r with
    | some (eqs, rest) => if endDecl rest then some (.core n ps eqs, rest) else none
    | none => none
  | some ([n], .assign :: r) =>
    match pExpr ar false f r with
    | some (e, rest) =>
      if endDecl rest then some (.eqn ⟨n, n, [], e, none, []⟩, rest) else none
    | none => none
  | some (n :: ps, .eq :: r) =>
    match pExpr ar false f r with
    | some (e, rest) =>
      if endDecl rest then some (.eqn ⟨n, n, ps, e, none, []⟩, rest) else none
    | none => none
  | _ => none

def pDecls (ar : Nm → Option Nat) : Nat → List Tok → Option (List Decl)
  | 0, _ => none
  | _ + 1, [] => some []
  | f + 1, .nl :: r => pDecls ar f r
  | f + 1, ts =>
    match pDecl ar (4 * ts.length + 4) ts with
    | some (d, r) => (d :: ·) <$> pDecls ar f r
    | none => none

/-- **The parser.**  A text, as code points, in the ASCII (`u = false`) or
    Unicode lexicon, to its declarations. -/
def parseWith (u : Bool) (src : List Nat) : Option (List Decl) :=
  match (if u then lexU src .none [] else lexA src .none []) with
  | none => none
  | some ts =>
    match collectTypes ts [] with
    | none => none
    | some tys => pDecls (arity tys) (ts.length + 1) ts

def parseFile (src : List Nat) : Option (List Decl) := parseWith false src

-- ---------------------------------------------------------------------------
-- Desugaring: case lowering, λ, cells and picks, binders numbered
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

/-- The ISA's names: `S`, `K`, `I`. -/
def isISA (n : Nm) : Bool := n == [83] || n == [75] || n == [73]

/-- A name as a core's equation resolves it: a sibling first, but never
    over the ISA. -/
def Eqn.qual (e : Eqn) (n : Nm) : Nm :=
  if isISA n then n
  else
    match e.core with
    | some c => if e.sibs.contains n then c ++ [46] ++ n else n
    | none => n

/-- `pair a (pair b …)`, the right-nested cell. -/
def pairC (q : Nm → Nm) : List CSrc → CSrc
  | [] => .glob []
  | [a] => a
  | a :: r => .app (.app (.glob (q (nm! "pair"))) a) (pairC q r)

/-- The `hd`/`tl` chain of an axis, the first step innermost. -/
def pickC (q : Nm → Nm) (e : CSrc) : List Bool → CSrc
  | [] => e
  | b :: bs => pickC q (.app (.glob (q (if b then nm! "tl" else nm! "hd"))) e) bs

mutual
  /-- Lower an expression in scope `sc`, numbering new binders from `k`;
      returns the next free number. -/
  def dExpr (tys : List TypeDecl) (q : Nm → Nm) (sc : List (Nm × Nat)) :
      Expr → Nat → Option (CSrc × Nat)
    | .name n, k =>
      match sc.lookup n with
      | some x => some (.var x, k)
      | none => some (.glob (q n), k)
    | .app f a, k =>
      match dExpr tys q sc f k with
      | none => none
      | some (f', k1) =>
        match dExpr tys q sc a k1 with
        | none => none
        | some (a', k2) => some (.app f' a', k2)
    | .case e bs, k =>
      match dExpr tys q sc e k with
      | none => none
      | some (e', k1) =>
        match dBranches tys q sc bs k1 with
        | none => none
        | some (arms, k2) =>
          match caseOrder tys arms with
          | none => none
          | some ks => some (ks.foldl CSrc.app e', k2)
    | .lam x b, k =>
      match dExpr tys q ((x, k) :: sc) b (k + 1) with
      | none => none
      | some (b', k1) => some (.lam k b', k1)
    | .cell items, k =>
      match dItems tys q sc items k with
      | none => none
      | some (cs, k1) => some (pairC q cs, k1)
    | .pick n e, k =>
      if n == 0 then none
      else
        match dExpr tys q sc e k with
        | none => none
        | some (e', k1) => some (pickC q e' (axisSteps n), k1)
  def dBranches (tys : List TypeDecl) (q : Nm → Nm) (sc : List (Nm × Nat)) :
      Branches → Nat → Option (List (Nm × CSrc) × Nat)
    | .nil, k => some ([], k)
    | .cons c xs body rest, k =>
      match dExpr tys q (bindFrom xs k sc) body (k + xs.length) with
      | none => none
      | some (b, k1) =>
        match dBranches tys q sc rest k1 with
        | none => none
        | some (r, k2) => some ((c, lamChain k xs.length b) :: r, k2)
  def dItems (tys : List TypeDecl) (q : Nm → Nm) (sc : List (Nm × Nat)) :
      Items → Nat → Option (List CSrc × Nat)
    | .nil, k => some ([], k)
    | .cons e rest, k =>
      match dExpr tys q sc e k with
      | none => none
      | some (e', k1) =>
        match dItems tys q sc rest k1 with
        | none => none
        | some (r, k2) => some (e' :: r, k2)
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
  match dExpr tys e.qual (bindFrom e.params 0 []) e.body k with
  | none => none
  | some (b0, _) =>
    if b0.globs.contains e.name then
      match dExpr tys e.qual (bindFrom e.params 1 [(e.bare, 0)]) e.body (k + 1) with
      | none => none
      | some (b1, _) => some ⟨(List.range k).map (· + 1), some 0, b1⟩
    else some ⟨List.range k, none, b0⟩

/-- The types and equations of a file, in order; a core's equations with
    its parameters prepended and its siblings noted. -/
def types : List Decl → List TypeDecl
  | [] => []
  | .ty d :: ds => d :: types ds
  | _ :: ds => types ds

def coreEqns (c : Nm) (ps : List Nm) (eqs : List (Nm × List Nm × Expr)) : List Eqn :=
  eqs.map fun (n, qs, b) => ⟨c ++ [46] ++ n, n, ps ++ qs, b, some c, eqs.map (·.1)⟩

def eqns : List Decl → List Eqn
  | [] => []
  | .eqn e :: ds => e :: eqns ds
  | .core c ps eqs :: ds => coreEqns c ps eqs ++ eqns ds
  | _ :: ds => eqns ds

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

/-- The ISA, always. -/
def isaTerms : List (Nm × Term) := [([83], S), ([75], K), ([73], I)]

/-- Tier 1: `B C W Y`, as `skijack` expands them (`Y` is `Ycomb`). -/
def tier1Terms : List (Nm × Term) :=
  [([66], S ⬝ (K ⬝ S) ⬝ K),
   ([67], S ⬝ (S ⬝ (K ⬝ S) ⬝ (S ⬝ (K ⬝ K) ⬝ S)) ⬝ (K ⬝ K)),
   ([87], S ⬝ S ⬝ (K ⬝ I)),
   ([89], Ycomb)]

/-- The prelude (`skijack/expand.py`): the Scott pair and its projections,
    lists and numerals, lowered. -/
def prelude : List (Nm × FEqn) :=
  [(nm! "pair", ⟨[0, 1, 2], none, .app (.app (.var 2) (.var 0)) (.var 1)⟩),
   (nm! "hd", ⟨[0], none, .app (.var 0) (.glob [75])⟩),
   (nm! "tl", ⟨[0], none, .app (.var 0) (.app (.glob [75]) (.glob [73]))⟩),
   (nm! "nil", ⟨[0, 1], none, .var 0⟩),
   (nm! "cons", ⟨[0, 1, 2, 3], none, .app (.app (.var 3) (.var 0)) (.var 1)⟩),
   (nm! "zero", ⟨[0, 1], none, .var 0⟩),
   (nm! "suc", ⟨[0, 1, 2], none, .app (.var 2) (.var 0)⟩)]

/-- A global as the file resolves it: the ISA, then the program, then
    Tier 1. -/
def resolveIn (done : List (Nm × Term)) (g : Nm) : Option Term :=
  match isaTerms.lookup g with
  | some t => some t
  | none =>
    match done.lookup g with
    | some t => some t
    | none => tier1Terms.lookup g

/-- Compile each pending equation whose globals all resolve; keep the rest
    pending. -/
def pass (done : List (Nm × Term)) : List (Nm × FEqn) → List (Nm × FEqn) × List (Nm × Term)
  | [] => ([], done)
  | (n, e) :: es =>
    if e.body.globs.all fun g => (resolveIn done g).isSome then
      pass (done ++ [(n, e.compile fun g => (resolveIn done g).getD K)]) es
    else
      let r := pass done es
      ((n, e) :: r.1, r.2)

def passes : Nat → List (Nm × Term) → List (Nm × FEqn) → List (Nm × FEqn) × List (Nm × Term)
  | 0, done, es => (es, done)
  | k + 1, done, es =>
    let r := pass done es
    passes k r.2 r.1

/-- A file's globals to compile: its equations lowered, the prelude it does
    not redefine, and each interpreter core's name for its `loop`. -/
def fileFEqns (ds : List Decl) : Option (List (Nm × FEqn)) :=
  let tys := types ds
  let es := eqns ds
  let defined := (tys.map fun d => d.ctors.map (·.1)).flatten ++
    (es.filter fun e => e.core.isNone).map (·.name)
  match es.mapM (fun e => (dEqn tys e).map fun fe => (e.name, fe)) with
  | none => none
  | some fes =>
    let loops := (ds.filterMap fun d =>
      match d with
      | .core c _ eqs =>
        if eqs.any (fun p => p.1 == nm! "loop") && !defined.contains c then
          some (c, (⟨[], none, .glob (c ++ [46] ++ nm! "loop")⟩ : FEqn))
        else none
      | _ => none)
    if nodup defined then
      some ((prelude.filter fun p => !defined.contains p.1) ++ fes ++ loops)
    else none

/-- **Compile a file**, in the ASCII (`u = false`) or Unicode lexicon:
    every constructor and every equation to the closed term `skijack`
    emits, a core's equation also under its bare name when no other core
    defines it.  A file with a name defined twice, an unresolved name or
    mutual recursion is refused. -/
def compileWith (u : Bool) (src : List Nat) : Option (List (Nm × Term)) :=
  match parseWith u src with
  | none => none
  | some ds =>
    match fileFEqns ds with
    | none => none
    | some fes =>
      let r := passes (fes.length + 1) ((types ds).map ctorTerms).flatten fes
      if r.1.isEmpty then
        let es := eqns ds
        let bare := es.filterMap fun e =>
          if e.core.isSome && (es.filter fun e' => e'.core.isSome && e'.bare == e.bare).length == 1
          then (r.2.lookup e.name).map fun t => (e.bare, t) else none
        some (bare ++ r.2)
      else none

/-- The environment a file's equations were compiled in: its compiled
    program-level names and `core.eq`s, without the bare aliases. -/
def compiledEnv (u : Bool) (src : List Nat) : List (Nm × Term) :=
  match parseWith u src with
  | none => []
  | some ds =>
    match fileFEqns ds with
    | none => []
    | some fes => (passes (fes.length + 1) ((types ds).map ctorTerms).flatten fes).2

def compileFile (src : List Nat) : Option (List (Nm × Term)) := compileWith false src

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
