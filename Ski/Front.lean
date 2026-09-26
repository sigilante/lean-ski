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
    m p… :=* e                      a macro, expanded at each use
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

Not read, and refused: quotation and everything of level 1 (`< >`, `|-`,
`?^`, `ns{`, fuel), qualified names, bare numbers, and an applied
capturing macro (`:=!`).  A program with an unresolved name, mutual
recursion, a name defined twice, a macro applied to too few arguments,
a macro that does not reach a fixpoint, or an expression nested deeper
than 256 is refused whole, as `skijack` refuses it.

## The passes

- `lexA` and `lexU` split a text into tokens, over code points, in the
  ASCII and Unicode lexicons.
- `parseWith` parses every declaration (`pExpr` and its siblings), with
  fuel proportional to the tokens, so every function is total and
  structural.
- `expandE` expands macros in each equation and definition before
  anything else, as `expand_macros` does: capture-avoiding substitution
  (`substE`) with `skijack`'s fresh names, λ and case binders shadowing a
  macro, and its three limits.
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
  terms before abstraction.  It computes them by `ctorOF`, `compDefF` and
  `compRecF`, proved equal and linear to evaluate in the kernel.

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
  | macro
  | cmacro
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
  | 58 :: 61 :: 42 :: r, m, acc => lexA r .none ([.macro] ++ (flushM m).reverse ++ acc)
  | 58 :: 61 :: 33 :: r, m, acc => lexA r .none ([.cmacro] ++ (flushM m).reverse ++ acc)
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
  | 8788 :: 42 :: r, m, acc => lexU r .none ([.macro] ++ (flushM m).reverse ++ acc)
  | 8788 :: 33 :: r, m, acc => lexU r .none ([.cmacro] ++ (flushM m).reverse ++ acc)
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
  /-- `name params :=* body`, or `:=!` when `capturing`. -/
  | macro (name : Nm) (params : List Nm) (body : Expr) (capturing : Bool)

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
  | some (n :: ps, .macro :: r) =>
    match pExpr ar false f r with
    | some (e, rest) => if endDecl rest then some (.macro n ps e false, rest) else none
    | none => none
  | some (n :: ps, .cmacro :: r) =>
    match pExpr ar false f r with
    | some (e, rest) => if endDecl rest then some (.macro n ps e true, rest) else none
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
-- Macros (`skijack/expand.py`, pass 1)
-- ---------------------------------------------------------------------------

/-- A macro: its parameters, its body, and whether it was declared
    capturing (`:=!`). -/
structure Macro where
  params : List Nm
  body : Expr
  capturing : Bool

mutual
  /-- The names free in an expression; a case branch's constructor counts. -/
  def freeE : Expr → List Nm
    | .name n => [n]
    | .app f a => freeE f ++ freeE a
    | .case e bs => freeE e ++ freeB bs
    | .lam x b => (freeE b).filter (· != x)
    | .cell items => freeI items
    | .pick _ e => freeE e
  def freeB : Branches → List Nm
    | .nil => []
    | .cons c xs body rest => c :: (freeE body).filter (fun y => !xs.contains y) ++ freeB rest
  def freeI : Items → List Nm
    | .nil => []
    | .cons e rest => freeE e ++ freeI rest
end

mutual
  /-- Nesting depth: the fuel substitution needs. -/
  def depthE : Expr → Nat
    | .name _ => 0
    | .app f a => max (depthE f) (depthE a) + 1
    | .case e bs => max (depthE e) (depthB bs) + 1
    | .lam _ b => depthE b + 1
    | .cell items => depthI items + 1
    | .pick _ e => depthE e + 1
  def depthB : Branches → Nat
    | .nil => 0
    | .cons _ _ body rest => max (depthE body) (depthB rest)
  def depthI : Items → Nat
    | .nil => 0
    | .cons e rest => max (depthE e) (depthI rest)
end

/-- Each branch body through `g`, which sees and may rename the branch's
    binders, threading a state. -/
def Branches.traverse {σ : Type} (g : σ → List Nm → Expr → Option (List Nm × Expr × σ)) :
    Branches → σ → Option (Branches × σ)
  | .nil, st => some (.nil, st)
  | .cons c xs body rest, st =>
    match g st xs body with
    | none => none
    | some (xs', body', st1) =>
      match Branches.traverse g rest st1 with
      | none => none
      | some (rest', st2) => some (.cons c xs' body' rest', st2)

/-- Each item through `g`, threading a state. -/
def Items.traverse {σ : Type} (g : σ → Expr → Option (Expr × σ)) :
    Items → σ → Option (Items × σ)
  | .nil, st => some (.nil, st)
  | .cons e rest, st =>
    match g st e with
    | none => none
    | some (e', st1) =>
      match Items.traverse g rest st1 with
      | none => none
      | some (rest', st2) => some (.cons e' rest', st2)

/-- A number's decimal digits, as code points. -/
def decimal (i : Nat) : Nm := (Nat.toDigits 10 i).map Char.toNat

/-- `base`, `base0`, `base1`, …: the first not taken (`_fresh`).  Among
    `taken.length + 1` distinct candidates one is free. -/
def freshFrom (base : Nm) (taken : List Nm) : Nat → Nat → Nm
  | 0, _ => base
  | f + 1, i =>
    if taken.contains (base ++ decimal i) then freshFrom base taken f (i + 1)
    else base ++ decimal i

def fresh (base : Nm) (taken : List Nm) : Nm :=
  if taken.contains base then freshFrom base taken (taken.length + 1) 0 else base

/-- A dictionary from pairs: the last pair for a key wins, as Python's
    `dict(zip(…))`. -/
def dictOf : List (Nm × Expr) → List (Nm × Expr) :=
  List.foldl (fun acc p => acc.filter (·.1 != p.1) ++ [p]) []

/-- **Capture-avoiding substitution** (`substitute`): a binder that would
    capture a name free in a substituted expression is renamed to
    `fresh (binder ++ "_") …` first (`_rename_binders`).  The fuel is the
    expression's depth plus one; renaming preserves depth. -/
def substE : Nat → List (Nm × Expr) → Expr → Option Expr
  | 0, _, _ => none
  | f + 1, sub, e =>
    if sub.isEmpty then some e
    else
      let rn : Nm → Expr → Option (Nm × Expr) := fun b body =>
        let fb := freeE body
        let danger := (sub.filter fun p => p.1 != b && fb.contains p.1).flatMap fun p => freeE p.2
        if danger.contains b then
          let fr := fresh (b ++ [95]) (danger ++ fb ++ sub.map (·.1))
          (substE f [(b, .name fr)] body).map fun body' => (fr, body')
        else some (b, body)
      match e with
      | .name n => some ((sub.lookup n).getD (.name n))
      | .app a b =>
        match substE f sub a, substE f sub b with
        | some a', some b' => some (.app a' b')
        | _, _ => none
      | .cell items =>
        (items.traverse (fun _ x => (substE f sub x).map fun x' => (x', ())) ()).map
          fun r => .cell r.1
      | .pick n x => (substE f sub x).map (.pick n)
      | .lam x b =>
        match rn x b with
        | none => none
        | some (x', b') => (substE f (sub.filter (·.1 != x')) b').map (.lam x')
      | .case sc bs =>
        let g : Unit → List Nm → Expr → Option (List Nm × Expr × Unit) := fun _ xs body =>
          match xs.foldlM (fun (acc : List Nm × Expr) b =>
              (rn b acc.2).map fun r => (acc.1 ++ [r.1], r.2)) ([], body) with
          | none => none
          | some (nb, body') =>
            (substE f (sub.filter fun p => !nb.contains p.1) body').map fun b'' => (nb, b'', ())
        match bs.traverse g () with
        | none => none
        | some (bs', _) => (substE f sub sc).map fun sc' => .case sc' bs'

/-- An application's head and its arguments, in order. -/
def spine : Expr → Expr × List Expr
  | .app f a => let r := spine f; (r.1, r.2 ++ [a])
  | e => (e, [])

/-- **Macro expansion to a fixpoint** (`expand_macros`), with `skijack`'s
    three limits: nesting `depth` at most 256, nested unfoldings `unfold`
    at most 100, and 200 000 substitutions in all (`budget`, threaded).  A
    macro with parameters must be applied to all of them; a capturing
    macro may not be applied; λ and case binders shadow macros.  Each call
    spends one fuel and adds one to `depth` or `unfold`, so from fuel 400 a
    limit is always reached before the fuel runs out. -/
def expandE : Nat → List (Nm × Macro) → Nat → Nat → Nat → Expr → Option (Expr × Nat)
  | 0, _, _, _, _, _ => none
  | f + 1, ms, depth, unfold, budget, e =>
    if 256 < depth || 100 < unfold || budget == 0 then none
    else
      let plain : Expr → Expr → Option (Expr × Nat) := fun g a =>
        match expandE f ms (depth + 1) unfold budget g with
        | none => none
        | some (g', b1) =>
          match expandE f ms (depth + 1) unfold b1 a with
          | none => none
          | some (a', b2) => some (.app g' a', b2)
      match e with
      | .name n =>
        match ms.lookup n with
        | some m =>
          if m.params.isEmpty then expandE f ms depth (unfold + 1) (budget - 1) m.body else none
        | none => some (e, budget)
      | .app g a =>
        match spine (.app g a) with
        | (.name n, args) =>
          match ms.lookup n with
          | some m =>
            if m.capturing then none
            else if args.length < m.params.length then none
            else
              match args.foldlM (fun (acc : List Expr × Nat) x =>
                  (expandE f ms (depth + 1) unfold acc.2 x).map fun r => (acc.1 ++ [r.1], r.2))
                  ([], budget) with
              | none => none
              | some (args', b1) =>
                match substE (depthE m.body + 1) (dictOf (m.params.zip args')) m.body with
                | none => none
                | some body =>
                  match expandE f ms depth (unfold + 1) (b1 - 1) body with
                  | none => none
                  | some (out, b2) => some ((args'.drop m.params.length).foldl .app out, b2)
          | none => plain g a
        | _ => plain g a
      | .cell items =>
        (items.traverse (fun bu x => expandE f ms (depth + 1) unfold bu x) budget).map
          fun r => (.cell r.1, r.2)
      | .pick n x => (expandE f ms (depth + 1) unfold budget x).map fun r => (.pick n r.1, r.2)
      | .lam x b =>
        (expandE f (ms.filter (·.1 != x)) (depth + 1) unfold budget b).map
          fun r => (.lam x r.1, r.2)
      | .case sc bs =>
        let g : Nat → List Nm → Expr → Option (List Nm × Expr × Nat) := fun bu xs body =>
          (expandE f (ms.filter fun p => !xs.contains p.1) (depth + 1) unfold bu body).map
            fun r => (xs, r.1, r.2)
        match bs.traverse g budget with
        | none => none
        | some (bs', b1) =>
          (expandE f ms (depth + 1) unfold b1 sc).map fun r => (.case r.1 bs', r.2)

/-- A file's macros, the last declaration of a name winning. -/
def macrosOf (ds : List Decl) : List (Nm × Macro) :=
  (ds.filterMap fun d =>
    match d with
    | .macro n ps b c => some (n, (⟨ps, b, c⟩ : Macro))
    | _ => none).reverse

/-- An equation's body with its file's macros expanded, from a fresh
    budget, as `skijack` expands each equation and definition. -/
def Eqn.expand (ms : List (Nm × Macro)) (e : Eqn) : Option Eqn :=
  (expandE 400 ms 0 0 200000 e.body).map fun r => { e with body := r.1 }

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
    | some e =>
      match e.expand (macrosOf ds) with
      | none => none
      | some e' => dEqn (types ds) e'

-- ---------------------------------------------------------------------------
-- Compiling a file
-- ---------------------------------------------------------------------------

/-- A lowered equation, compiled with its globals resolved by `env`. -/
def FEqn.compile (env : Nm → Term) (e : FEqn) : Term :=
  match e.self with
  | some s => toTerm (compRec s e.params (e.body.resolve env))
  | none => toTerm (compDef e.params (e.body.resolve env))

/-- `FEqn.compile` by `absNF`, which the kernel evaluates fast. -/
def FEqn.compileF (env : Nm → Term) (e : FEqn) : Term :=
  match e.self with
  | some s => toTerm (compRecF s e.params (e.body.resolve env))
  | none => toTerm (compDefF e.params (e.body.resolve env))

theorem FEqn.compileF_eq (env : Nm → Term) (e : FEqn) : e.compileF env = e.compile env := by
  unfold FEqn.compileF FEqn.compile
  cases e.self with
  | some s => exact congrArg toTerm (compRecF_eq _ _ _)
  | none => exact congrArg toTerm (compDefF_eq _ _)

/-- A type's constructors, compiled (by `ctorOF`, which is `ctorO`). -/
def ctorTerms (d : TypeDecl) : List (Nm × Term) :=
  List.zipWith (fun j p => (p.1, toTerm (ctorOF p.2 j d.ctors.length)))
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
      pass (done ++ [(n, e.compileF fun g => (resolveIn done g).getD K)]) es
    else
      let r := pass done es
      ((n, e) :: r.1, r.2)

def passes : Nat → List (Nm × Term) → List (Nm × FEqn) → List (Nm × FEqn) × List (Nm × Term)
  | 0, done, es => (es, done)
  | k + 1, done, es =>
    let r := pass done es
    passes k r.2 r.1

/-- A file's globals to compile: its equations, macros expanded, lowered; the prelude it does
    not redefine, and each interpreter core's name for its `loop`. -/
def fileFEqns (ds : List Decl) : Option (List (Nm × FEqn)) :=
  let tys := types ds
  let es := eqns ds
  let defined := (tys.map fun d => d.ctors.map (·.1)).flatten ++
    (es.filter fun e => e.core.isNone).map (·.name)
  let ms := macrosOf ds
  match es.mapM (fun e => (e.expand ms).bind fun e' => (dEqn tys e').map fun fe => (e.name, fe)) with
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

/-- A term's postfix codes before `rest`: `0 1 2` for `S K I`, and `3` for
    an application, after its function's and its argument's codes. -/
def postC : Term → List Nat → List Nat
  | S, rest => 0 :: rest
  | K, rest => 1 :: rest
  | I, rest => 2 :: rest
  | f ⬝ a, rest => postC f (postC a (3 :: rest))

/-- Codes packed 25 to a number in base 6, each code plus one, least
    significant first: the compact form the generated checks give
    `skijack`'s terms in.  `k` counts the codes in the chunk `cur`, whose
    next digit weighs `p`. -/
def packGo : List Nat → Nat → Nat → Nat → List Nat → List Nat
  | [], k, cur, _, acc => (if k == 0 then acc else cur :: acc).reverse
  | c :: r, k, cur, p, acc =>
    if k + 1 == 25 then packGo r 0 0 1 ((cur + (c + 1) * p) :: acc)
    else packGo r (k + 1) (cur + (c + 1) * p) (p * 6) acc

/-- A term's packed codes. -/
def codeOf (t : Term) : List Nat := packGo (postC t []) 0 0 1 []

/-- The first entry for `n` taken out of `es`: its codes, and the rest. -/
def takeEntry (n : Nm) : List (Nm × List Nat) → Option (List Nat × List (Nm × List Nat))
  | [] => none
  | (m, c) :: r =>
    if n == m then some (c, r) else (takeEntry n r).map fun q => (q.1, (m, c) :: q.2)

/-- Each compiled term has the codes `es` gives its name, and each entry of
    `es` is used once.  One pass over the compiled file: the kernel does not
    share a repeated `compileWith`, so a lookup per name would compile the
    file once per name. -/
def agreeEnv : List (Nm × Term) → List (Nm × List Nat) → Bool
  | [], es => es.isEmpty
  | (n, t) :: r, es =>
    match takeEntry n es with
    | some q => codeOf t == q.1 && agreeEnv r q.2
    | none => false

/-- `agreeEnv` for a file that may not compile. -/
def agrees (file : Option (List (Nm × Term))) (es : List (Nm × List Nat)) : Bool :=
  match file with
  | some env => agreeEnv env es
  | none => false

theorem lookup_cons_self {β : Type} (n : Nm) (d : β) (r : List (Nm × β)) :
    ((n, d) :: r).lookup n = some d := by
  rw [List.lookup_cons, show (n == n) = true from beq_iff_eq.mpr rfl]

theorem lookup_cons_ne {β : Type} {n m : Nm} (h : n ≠ m) (d : β) (r : List (Nm × β)) :
    ((m, d) :: r).lookup n = r.lookup n := by
  rw [List.lookup_cons, beq_false_of_ne h]

theorem takeEntry_lookup : ∀ {es : List (Nm × List Nat)} {n : Nm} {c : List Nat}
    {es' : List (Nm × List Nat)}, takeEntry n es = some (c, es') →
    es.lookup n = some c ∧ ∀ k, k ≠ n → es'.lookup k = es.lookup k
  | [], _, _, _, h => by cases h
  | (m, d) :: r, n, c, es', h => by
    by_cases e : n = m
    · subst e
      have h' : takeEntry n ((n, d) :: r) = some (d, r) := by
        show (if (n == n) = true then some (d, r) else _) = _
        rw [if_pos (beq_iff_eq.mpr rfl)]
      rw [h'] at h
      cases h
      exact ⟨lookup_cons_self n d r, fun k hk => (lookup_cons_ne hk d r).symm⟩
    · have hne : ¬ (n == m) = true := fun hb => e (beq_iff_eq.mp hb)
      have h' : takeEntry n ((m, d) :: r) = (takeEntry n r).map fun q => (q.1, (m, d) :: q.2) := by
        show (if (n == m) = true then some (d, r) else _) = _
        rw [if_neg hne]
      rw [h'] at h
      cases hr : takeEntry n r with
      | none => rw [hr] at h; cases h
      | some q =>
        cases q with
        | mk c0 r' =>
          rw [hr] at h
          have h2 : (some (c0, (m, d) :: r') : Option (List Nat × List (Nm × List Nat))) =
              some (c, es') := h
          cases h2
          have ih := takeEntry_lookup hr
          refine ⟨by rw [lookup_cons_ne e]; exact ih.1, fun k hk => ?_⟩
          by_cases ekm : k = m
          · subst ekm; rw [lookup_cons_self, lookup_cons_self]
          · rw [lookup_cons_ne ekm, lookup_cons_ne ekm]; exact ih.2 k hk

theorem agreeEnv_cons (m : Nm) (t : Term) (r : List (Nm × Term)) (es : List (Nm × List Nat)) :
    agreeEnv ((m, t) :: r) es =
      match takeEntry m es with
      | some q => (codeOf t == q.1 && agreeEnv r q.2)
      | none => false := rfl

/-- What `agreeEnv` checks: every name of `es` compiles, to a term with the
    codes `es` gives it. -/
theorem agreeEnv_lookup : ∀ {env : List (Nm × Term)} {es : List (Nm × List Nat)}
    {n : Nm} {c : List Nat}, agreeEnv env es = true → es.lookup n = some c →
    ∃ t, env.lookup n = some t ∧ codeOf t = c
  | [], es, n, c, h, hl => by
    cases es with
    | nil => cases hl
    | cons _ _ => cases h
  | (m, t) :: r, es, n, c, h, hl => by
    rw [agreeEnv_cons] at h
    cases ht : takeEntry m es with
    | none => rw [ht] at h; cases h
    | some q =>
      cases q with
      | mk c0 es' =>
        rw [ht] at h
        have hb : (codeOf t == c0 && agreeEnv r es') = true := h
        rw [Bool.and_eq_true] at hb
        have hcode : codeOf t = c0 := beq_iff_eq.mp hb.1
        have hq := takeEntry_lookup ht
        by_cases e : n = m
        · subst e
          rw [hq.1] at hl
          cases hl
          exact ⟨t, lookup_cons_self n t r, hcode⟩
        · have hl' : es'.lookup n = some c := by rw [hq.2 n e]; exact hl
          match agreeEnv_lookup hb.2 hl' with
          | ⟨t', ht', hc'⟩ => exact ⟨t', by rw [lookup_cons_ne e]; exact ht', hc'⟩

/-- And conversely: every compiled name is one of `es`, with its codes. -/
theorem agreeEnv_lookup_rev : ∀ {env : List (Nm × Term)} {es : List (Nm × List Nat)}
    {n : Nm} {t : Term}, agreeEnv env es = true → env.lookup n = some t →
    es.lookup n = some (codeOf t)
  | [], _, _, _, _, hl => by cases hl
  | (m, u) :: r, es, n, t, h, hl => by
    rw [agreeEnv_cons] at h
    cases ht : takeEntry m es with
    | none => rw [ht] at h; cases h
    | some q =>
      cases q with
      | mk c0 es' =>
        rw [ht] at h
        have hb : (codeOf u == c0 && agreeEnv r es') = true := h
        rw [Bool.and_eq_true] at hb
        have hcode : codeOf u = c0 := beq_iff_eq.mp hb.1
        have hq := takeEntry_lookup ht
        by_cases e : n = m
        · subst e
          rw [lookup_cons_self] at hl
          cases hl
          rw [hq.1, hcode]
        · rw [lookup_cons_ne e] at hl
          rw [← hq.2 n e]
          exact agreeEnv_lookup_rev hb.2 hl

/-- What `agrees` checks: every name of `es` compiles, to a term with the
    codes `es` gives it, and every compiled name is one of `es`. -/
theorem agrees_termOf {file : Option (List (Nm × Term))} {es : List (Nm × List Nat)}
    (h : agrees file es = true) {n : Nm} {c : List Nat} (hl : es.lookup n = some c) :
    ∃ t, file.bind (·.lookup n) = some t ∧ codeOf t = c := by
  cases file with
  | none => cases h
  | some env => exact agreeEnv_lookup h hl

theorem agrees_termOf_rev {file : Option (List (Nm × Term))} {es : List (Nm × List Nat)}
    (h : agrees file es = true) {n : Nm} {t : Term} (ht : file.bind (·.lookup n) = some t) :
    es.lookup n = some (codeOf t) := by
  cases file with
  | none => cases h
  | some env => exact agreeEnv_lookup_rev h ht

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
