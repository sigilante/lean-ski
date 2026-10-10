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
    d := <e>                        a datum: e quoted over the object type
    r := [i a… |-] <e>@n            a run of an interpreter core, fuel n
    n := ns{/p => <e>, …}           a namespace literal, a resolver
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

Inside `< >` a leaf of the object type is that leaf, even `S`, `K` or
`I`; juxtaposition is its application constructor; any other name is
inlined as its level-0 term and quoted; `?^/a/b` is the `Scry` leaf
applied to the path `Cons A (Cons B Nil)`.  Refused, as `skijack`
refuses them: a qualified name where it is compiled, a bare number, an
applied capturing macro (`:=!`), a path payload, and a program with an
unresolved name, mutual recursion, a name, type or core defined twice, a
macro applied to too few arguments or without a fixpoint, an expression
nested deeper than 256, or a level-1 declaration without the types it
needs.

## The passes

- `lexA` and `lexU` split a text into tokens, over code points, in the
  ASCII and Unicode lexicons.
- `parseWith` parses every declaration (`pExpr` and its siblings), with
  fuel proportional to the tokens, so every function is total and
  structural.
- `generate` adds, for a file with an object type, the forms
  `generate.py` adds: the walker `sp`, the rebuilder `rb`, the default
  `S`/`K`/`I` step equations, and each interpreter core's `step` and fuel
  loop, each unless the file defines the name (`readWith` is parsing then
  generation).
- Level 1 (`compileDecls`, pass 6 of `expand.py`): each datum and
  namespace literal in declaration order, each joining the program so
  later declarations may name it; then each run, as its interpreter
  core's loop applied to its arguments, a fuel numeral and its datum.
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
  | qopen
  | qclose
  | fuel (n : Nat)
  | policy
  | scry
  | turnstile
  | nsopen
  | mapsto
  | comma
  | slash
  deriving DecidableEq, Repr

def isLetter (c : Nat) : Bool := (65 ≤ c && c ≤ 90) || (97 ≤ c && c ≤ 122) || c == 95
def isDigit (c : Nat) : Bool := 48 ≤ c && c ≤ 57

/-- What the lexer is in the middle of. -/
inductive Mode
  | none
  | ident (acc : List Nat)
  | num (n : Nat)
  | comment
  | fuel (n : Nat)

def flushM : Mode → List Tok
  | .ident acc => [.ident acc.reverse]
  | .num n => [.num n]
  | .fuel n => [.fuel n]
  | _ => []

/-- A letter, digit, `_` or `'`, in the middle of reading `m`. -/
def lexWord (c : Nat) : Mode → Option (List Tok × Mode)
  | .ident acc =>
    if isLetter c || isDigit c || c == 39 then some ([], .ident (c :: acc)) else none
  | .num n =>
    if isDigit c then some ([], .num (10 * n + (c - 48)))
    else if isLetter c then some ([.num n], .ident [c])
    else none
  | .fuel n =>
    if isLetter c then some ([.fuel n], .ident [c])
    else if isDigit c then some ([.fuel n], .num (c - 48))
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
  | 124 :: 45 :: r, m, acc => lexA r .none ([.turnstile] ++ (flushM m).reverse ++ acc)
  | 110 :: 115 :: 123 :: r, .none, acc => lexA r .none (.nsopen :: acc)
  | 110 :: 115 :: 123 :: r, .num n, acc => lexA r .none ([.nsopen, .num n] ++ acc)
  | 110 :: 115 :: 123 :: r, .fuel n, acc => lexA r .none ([.nsopen, .fuel n] ++ acc)
  | 63 :: 94 :: r, m, acc => lexA r .none ([.scry] ++ (flushM m).reverse ++ acc)
  | 58 :: 61 :: r, m, acc => lexA r .none ([.assign] ++ (flushM m).reverse ++ acc)
  | 61 :: 62 :: r, m, acc => lexA r .none ([.mapsto] ++ (flushM m).reverse ++ acc)
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
  | 64 :: 91 :: 93 :: r, m, acc => lexA r .none ([.policy] ++ (flushM m).reverse ++ acc)
  | 64 :: c :: r, m, acc =>
    if isDigit c then lexA r (.fuel (c - 48)) ((flushM m).reverse ++ acc) else none
  | 60 :: r, m, acc => lexA r .none ([.qopen] ++ (flushM m).reverse ++ acc)
  | 62 :: r, m, acc => lexA r .none ([.qclose] ++ (flushM m).reverse ++ acc)
  | 44 :: r, m, acc => lexA r .none ([.comma] ++ (flushM m).reverse ++ acc)
  | 47 :: r, m, acc => lexA r .none ([.slash] ++ (flushM m).reverse ++ acc)
  | 10 :: r, m, acc => lexA r .none ([.nl] ++ (flushM m).reverse ++ acc)
  | c :: r, m, acc =>
    if c == 32 || c == 9 || c == 13 then lexA r .none ((flushM m).reverse ++ acc)
    else
      match m, isDigit c with
      | .fuel n, true => lexA r (.fuel (10 * n + (c - 48))) acc
      | _, _ =>
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
  | 8757 :: r, m, acc => lexU r .none ([.scry] ++ (flushM m).reverse ++ acc)
  | 8866 :: r, m, acc => lexU r .none ([.turnstile] ++ (flushM m).reverse ++ acc)
  | 8614 :: r, m, acc => lexU r .none ([.mapsto] ++ (flushM m).reverse ++ acc)
  | 8333 :: 8334 :: r, m, acc => lexU r .none ([.policy] ++ (flushM m).reverse ++ acc)
  | 110 :: 115 :: 123 :: r, .none, acc => lexU r .none (.nsopen :: acc)
  | 110 :: 115 :: 123 :: r, .num n, acc => lexU r .none ([.nsopen, .num n] ++ acc)
  | 110 :: 115 :: 123 :: r, .fuel n, acc => lexU r .none ([.nsopen, .fuel n] ++ acc)
  | 60 :: r, m, acc => lexU r .none ([.qopen] ++ (flushM m).reverse ++ acc)
  | 62 :: r, m, acc => lexU r .none ([.qclose] ++ (flushM m).reverse ++ acc)
  | 44 :: r, m, acc => lexU r .none ([.comma] ++ (flushM m).reverse ++ acc)
  | 47 :: r, m, acc => lexU r .none ([.slash] ++ (flushM m).reverse ++ acc)
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
      | .fuel n => lexU r (.fuel (10 * n + (c - 8320))) acc
      | _ => lexU r (.fuel (c - 8320)) ((flushM m).reverse ++ acc)
    else
      match lexWord c m with
      | some (ts, m') => lexU r m' (ts.reverse ++ acc)
      | none => none

-- ---------------------------------------------------------------------------
-- Syntax
-- ---------------------------------------------------------------------------

/-- A quotation's fuel: none, a number (`@10`), or the runtime's policy
    (`@[]`). -/
inductive QFuel
  | none
  | num (n : Nat)
  | policy

mutual
  inductive Expr
    | name (n : Nm)
    | app (f a : Expr)
    | case (e : Expr) (bs : Branches)
    | lam (x : Nm) (b : Expr)
    | cell (items : Items)
    | pick (n : Nat) (e : Expr)
    /-- `<e>`, `<e>@n`, `<e>@[]`: a quotation, a datum when it has no fuel. -/
    | quote (e : Expr) (fuel : QFuel)
    /-- `i |- <e>@n`: a run of the interpreter `i`. -/
    | run (i : Expr) (e : Expr) (fuel : QFuel)
    /-- `?^/a/b`: a scry, its segments' tags and whether each carries a
        payload. -/
    | scry (path : List (Nm × Bool))
    /-- `ns{/a => <e>, …}`: a namespace literal. -/
    | nslit (facts : Facts)
  /-- Case branches, in source order: constructor, binders, body. -/
  inductive Branches
    | nil
    | cons (c : Nm) (xs : List Nm) (body : Expr) (rest : Branches)
  /-- A cell's items. -/
  inductive Items
    | nil
    | cons (e : Expr) (rest : Items)
  /-- A namespace literal's facts: a path and its value. -/
  inductive Facts
    | nil
    | cons (path : List (Nm × Bool)) (v : Expr) (rest : Facts)
end

/-- A type: its name and its constructors with their arities, in
    declaration order, and with their field types. -/
structure TypeDecl where
  name : Nm
  ctors : List (Nm × Nat)
  ftys : List (Nm × List Nm)

/-- A type from its constructors and their field types. -/
def TypeDecl.of (n : Nm) (cs : List (Nm × List Nm)) : TypeDecl :=
  ⟨n, cs.map fun c => (c.1, c.2.length), cs⟩

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
  | sig (name : Nm) (tys : List Nm)
  | eqn (e : Eqn)
  | core (name : Nm) (params : List Nm) (eqs : List (Nm × List Nm × Expr))
  /-- `name params :=* body`, or `:=!` when `capturing`. -/
  | macro (name : Nm) (params : List Nm) (body : Expr) (capturing : Bool)
  /-- `name := e` whose right side is a quotation, a run or a namespace
      literal: level 1. -/
  | qdef (name : Nm) (e : Expr)

-- ---------------------------------------------------------------------------
-- Parsing
-- ---------------------------------------------------------------------------

/-- Newlines are invisible inside brackets. -/
def sk : Bool → List Tok → List Tok
  | true, .nl :: r => sk true r
  | _, ts => ts

def atomStart : Tok → Bool
  | .ident _ | .lparen | .lbrack | .axis _ | .lam | .num _ | .qopen | .scry | .nsopen => true
  | _ => false

/-- The constructors of a type declaration, to the end of the line. -/
def parseCtors : List Tok → List Nm → List (Nm × List Nm) →
    Option (List (Nm × List Nm) × List Tok)
  | [], cur, out =>
    match cur.reverse with
    | c :: fs => some (out.reverse ++ [(c, fs)], [])
    | [] => none
  | .nl :: r, cur, out =>
    match cur.reverse with
    | c :: fs => some (out.reverse ++ [(c, fs)], .nl :: r)
    | [] => none
  | .bar :: r, cur, out =>
    match cur.reverse with
    | c :: fs => parseCtors r [] ((c, fs) :: out)
    | [] => none
  | .ident x :: r, cur, out => parseCtors r (x :: cur) out
  | _, _, _ => none

/-- Pass one: every type the file declares, wherever.  The scan goes on
    after each `===`: a constructor list never holds another `===`. -/
def collectTypes : List Tok → List TypeDecl → Option (List TypeDecl)
  | [], acc => some acc.reverse
  | .ident n :: .defTy :: r, acc =>
    match parseCtors r [] [] with
    | some (cs, _) => collectTypes r (TypeDecl.of n cs :: acc)
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

/-- A qualified name's further parts, `.b.c`: joined by a code point no
    source name holds, so a qualified name never resolves, as in `skijack`. -/
def qualTail : List Tok → Nm → Nm × List Tok
  | .dot :: .ident y :: r, acc => qualTail r (acc ++ [0] ++ y)
  | ts, acc => (acc, ts)

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
      | .turnstile :: r =>
        match pQuote ar d f r with
        | some ((q, fu), r1) => pCases ar d f (.run e q fu) r1
        | none => none
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
      | .ident x :: r => let q := qualTail r x; some (.name q.1, q.2)
      | .qopen :: r =>
        match pQuote ar d f (.qopen :: r) with
        | some ((e, fu), r1) => some (.quote e fu, r1)
        | none => none
      | .scry :: r =>
        match pPath ar d f r with
        | some ([], _) => none
        | some (p, r1) => some (.scry p, r1)
        | none => none
      | .nsopen :: r =>
        match sk true r with
        | .rbrace :: r1 => some (.nslit .nil, r1)
        | _ =>
          match pFacts ar f r with
          | some (fs, r1) =>
            match sk d r1 with
            | .rbrace :: r2 => some (.nslit fs, r2)
            | _ => none
          | none => none
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
  /-- `<e>` and its fuel, `@n` or `@[]` right after the `>`. -/
  def pQuote (ar : Nm → Option Nat) (d : Bool) : Nat → List Tok → Option ((Expr × QFuel) × List Tok)
    | 0, _ => none
    | f + 1, ts =>
      match sk d ts with
      | .qopen :: r =>
        match pExpr ar true f r with
        | some (e, r') =>
          match sk d r' with
          | .qclose :: .fuel n :: r'' => some ((e, .num n), r'')
          | .qclose :: .policy :: r'' => some ((e, .policy), r'')
          | .qclose :: r'' => some ((e, .none), r'')
          | _ => none
        | none => none
      | _ => none
  /-- A path's segments `/tag`, each with or without a `[e]` payload. -/
  def pPath (ar : Nm → Option Nat) (d : Bool) : Nat → List Tok → Option (List (Nm × Bool) × List Tok)
    | 0, _ => none
    | f + 1, .slash :: r =>
      match sk d r with
      | .ident t :: .lbrack :: r2 =>
        match pExpr ar true f r2 with
        | some (_, r3) =>
          match sk d r3 with
          | .rbrack :: r4 =>
            match pPath ar d f r4 with
            | some (ss, r5) => some ((t, true) :: ss, r5)
            | none => none
          | _ => none
        | none => none
      | .ident t :: r1 =>
        match pPath ar d f r1 with
        | some (ss, r5) => some ((t, false) :: ss, r5)
        | none => none
      | _ => none
    | _ + 1, ts => some ([], ts)
  /-- A namespace literal's facts `path => e`, separated by commas,
      newlines invisible. -/
  def pFacts (ar : Nm → Option Nat) : Nat → List Tok → Option (Facts × List Tok)
    | 0, _ => none
    | f + 1, ts =>
      match pPath ar true f ts with
      | some ([], _) => none
      | some (p, r) =>
        match sk true r with
        | .mapsto :: r1 =>
          match pExpr ar true f r1 with
          | some (v, r2) =>
            match sk true r2 with
            | .comma :: r3 =>
              match pFacts ar f r3 with
              | some (fs, r4) => some (.cons p v fs, r4)
              | none => none
            | _ => some (.cons p v .nil, r2)
          | none => none
        | _ => none
      | none => none
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
def pSig : List Tok → Option (List Nm × List Tok)
  | .ident t :: .arrow :: r => (pSig r).map fun p => (t :: p.1, p.2)
  | .ident t :: r => if endDecl r then some ([t], r) else none
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
    | some (cs, rest) => some (.ty (TypeDecl.of n cs), rest)
    | none => none
  | some ([n], .colon :: r) =>
    match pSig r with
    | some (ts, rest) => some (.sig n ts, rest)
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
      if endDecl rest then
        match e with
        | .quote .. | .run .. | .nslit _ => some (.qdef n e, rest)
        | _ => some (.eqn ⟨n, n, [], e, none, []⟩, rest)
      else none
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
    | .quote e _ => freeE e
    | .run i e _ => freeE e ++ freeE i
    | .scry _ => []
    | .nslit _ => []
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
    | .quote e _ => depthE e + 1
    | .run i e _ => max (depthE i) (depthE e) + 1
    | .scry _ => 0
    | .nslit _ => 0
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
      | _ => none

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
      | _ => none

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
-- Type-generated forms (`skijack/generate.py`)
-- ---------------------------------------------------------------------------

/-- `f x1 … xn`. -/
def apE (f : Expr) (xs : List Expr) : Expr := xs.foldl .app f

/-- The object type: the one type with exactly one constructor of two
    fields of its own type (the application), every other constructor a
    leaf. -/
structure ObjT where
  decl : TypeDecl
  app : Nm
  leaves : List (Nm × List Nm)

/-- The file's object type (`find_object_type`): `some none` when there is
    none, `none` when the file is refused — a type with two application
    constructors, an object type with a non-leaf beside its application, or
    two object types. -/
def findObject (tys : List TypeDecl) : Option (Option ObjT) :=
  let cands := tys.filterMap fun d =>
    let apps := d.ftys.filter fun c => c.2.length == 2 && c.2.all (· == d.name)
    match apps with
    | [] => none
    | a :: _ => some (d, apps.length, a)
  if cands.any (fun c => c.2.1 != 1) then none
  else
    let objs := cands.map fun (d, _, a) => (⟨d, a.1, d.ftys.filter (·.1 != a.1)⟩ : ObjT)
    if objs.any (fun o => o.leaves.any (!·.2.isEmpty)) then none
    else
      match objs with
      | [] => some none
      | [o] => some (some o)
      | _ => none

/-- The loop's types (`LoopTypes`): the step outcome `O` with its
    term-carrying constructor `stepped` and first leaf `done`, the result
    `R` with its term-carrying `value` and last leaf `timeout`, and the
    `R` constructor each other `O` constructor maps to. -/
structure LoopT where
  outcome : TypeDecl
  result : Nm
  stepped : Nm
  done : Nm
  value : Nm
  timeout : Nm
  mapping : List (Nm × Nm)

/-- A type's first constructor carrying exactly one field, of type `t`,
    and its other constructors (`_carrier`). -/
def carrier (d : TypeDecl) (t : Nm) : Option ((Nm × List Nm) × List (Nm × List Nm)) :=
  if d.ftys.length < 2 then none
  else
    match d.ftys.find? (fun c => c.2 == [t]) with
    | none => none
    | some c => some (c, d.ftys.filter (·.1 != c.1))

/-- `_build_loop_types`: `O`'s first leaf is done, a payload constructor
    maps to `R`'s at the same position, the other leaves map in order onto
    `R`'s leaves but its value and its last leaf, the timeout. -/
def buildLoop (od : TypeDecl) (st : Nm × List Nm) (rest : List (Nm × List Nm))
    (rd : TypeDecl) (v : Nm × List Nm) : Option LoopT :=
  let rNull := rd.ftys.filter (·.2.isEmpty)
  match rNull.getLast? with
  | none => none
  | some timeout =>
    let spare := rNull.filter fun c => c.1 != timeout.1 && c.1 != v.1
    match (rest.filter (·.2.isEmpty)).head? with
    | none => none
    | some done =>
      let step := fun (acc : List (Nm × Nm) × Nat) (c : Nm × List Nm) =>
        if c.2.isEmpty then
          match spare[acc.2]? with
          | some sc => some (acc.1 ++ [(c.1, sc.1)], acc.2 + 1)
          | none => none
        else
          match od.ftys.findIdx? (·.1 == c.1) with
          | none => none
          | some idx =>
            match rd.ftys[idx]? with
            | some rc => if rc.2.length == c.2.length then some (acc.1 ++ [(c.1, rc.1)], acc.2) else none
            | none => none
      ((rest.filter (·.1 != done.1)).foldlM step ([(done.1, v.1)], 0)).map fun r =>
        ⟨od, rd.name, st.1, done.1, v.1, timeout.1, r.1⟩

/-- `find_loop_types`: the types other than the object type with a
    carrier; the first of the last two is `O` and the last `R`, or the one
    is both.  They must have as many constructors. -/
def findLoop (tys : List TypeDecl) (o : ObjT) : Option LoopT :=
  let cands := tys.filterMap fun d =>
    if d.name == o.decl.name then none else (carrier d o.decl.name).map fun r => (d, r.1, r.2)
  let pick := fun (od : TypeDecl) (st : Nm × List Nm) (rest : List (Nm × List Nm))
      (rd : TypeDecl) (v : Nm × List Nm) =>
    if od.ftys.length != rd.ftys.length then none else buildLoop od st rest rd v
  match cands.reverse with
  | [] => none
  | [(od, st, rest)] => pick od st rest od st
  | (rd, v, _) :: (od, st, rest) :: _ => pick od st rest rd v

/-- The spine walker `sp` and the rebuilder `rb`, with their helpers
    (`_walker_and_rebuilder`). -/
def walker (o : ObjT) : List (Nm × List Nm × Expr) :=
  let n := o.leaves.length
  let conts := (List.range n).map fun i => nm! "c" ++ decimal i
  let res := (o.leaves.zip (List.range n)).map fun (c, j) =>
    (nm! "res" ++ c.1, nm! "acc" :: conts, apE (.name (nm! "c" ++ decimal j)) [.name (nm! "acc")])
  let slots := o.decl.ftys.map fun c =>
    if c.1 == o.app then apE (.name (nm! "spApp")) [.name (nm! "sp"), .name (nm! "acc")]
    else apE (.name (nm! "res" ++ c.1)) [.name (nm! "acc")]
  res ++
    [(nm! "spApp", [nm! "f", nm! "acc", nm! "t", nm! "u"],
        apE (.name (nm! "f")) [.name (nm! "t"),
          apE (.name (nm! "cons")) [.name (nm! "u"), .name (nm! "acc")]]),
     (nm! "sp", [nm! "m", nm! "acc"], apE (.name (nm! "m")) slots),
     (nm! "rb1", [nm! "f", nm! "h", nm! "x", nm! "xs"],
        apE (.name (nm! "f")) [apE (.name o.app) [.name (nm! "h"), .name (nm! "x")], .name (nm! "xs")]),
     (nm! "rb", [nm! "h", nm! "args"],
        apE (.name (nm! "args")) [.name (nm! "h"),
          apE (.name (nm! "rb1")) [.name (nm! "rb"), .name (nm! "h")]])]

/-- The ISA's default step equations, for the leaves named `I`, `K`, `S`
    (`_default_step_equations`). -/
def defaultSteps (o : ObjT) (lt : LoopT) : List (Nm × List Nm × Expr) :=
  let has := fun c => o.leaves.any (·.1 == c)
  let st := Expr.name lt.stepped
  let dn := Expr.name lt.done
  let app := fun a b => apE (.name o.app) [a, b]
  let x := Expr.name (nm! "x")
  let y := Expr.name (nm! "y")
  let z := Expr.name (nm! "z")
  let r := Expr.name (nm! "r")
  let rest := Expr.name (nm! "rest")
  let args := Expr.name (nm! "args")
  let rb := fun a => apE (.name (nm! "rb")) [a, rest]
  (if has [73] then
    [(nm! "stepI1", [nm! "x", nm! "rest"], apE st [rb x]),
     (nm! "stepI", [nm! "args"], apE args [dn, .name (nm! "stepI1")])] else []) ++
  (if has [75] then
    [(nm! "stepK2", [nm! "x", nm! "y", nm! "rest"], apE st [rb x]),
     (nm! "stepK1", [nm! "x", nm! "r"], apE r [dn, apE (.name (nm! "stepK2")) [x]]),
     (nm! "stepK", [nm! "args"], apE args [dn, .name (nm! "stepK1")])] else []) ++
  (if has [83] then
    [(nm! "stepS3", [nm! "x", nm! "y", nm! "z", nm! "rest"], apE st [rb (app (app x z) (app y z))]),
     (nm! "stepS2", [nm! "x", nm! "y", nm! "r2"],
        apE (.name (nm! "r2")) [dn, apE (.name (nm! "stepS3")) [x, y]]),
     (nm! "stepS1", [nm! "x", nm! "r"], apE r [dn, apE (.name (nm! "stepS2")) [x]]),
     (nm! "stepS", [nm! "args"], apE args [dn, .name (nm! "stepS1")])] else [])

/-- A core that writes `step`, `loop` or a step equation for a
    constructor of the object type (`is_interpreter_core`). -/
def isInterp (o : ObjT) (eqs : List (Nm × List Nm × Expr)) : Bool :=
  let names := eqs.map (·.1)
  names.contains (nm! "step") || names.contains (nm! "loop") ||
    o.decl.ftys.any fun c => names.contains (nm! "step" ++ c.1)

/-- An interpreter core with its `step` and its fuel loop added unless it
    writes them (`_fill_core`); `loop1` without `loop` is refused. -/
def fillCore (o : ObjT) (lt : LoopT) (ps : List Nm) (eqs : List (Nm × List Nm × Expr)) :
    Option (List (Nm × List Nm × Expr)) :=
  let have_ := eqs.map (·.1)
  let pv := ps.map Expr.name
  let step :=
    if have_.contains (nm! "step") then []
    else
      let slots := o.leaves.map fun c =>
        let n := nm! "step" ++ c.1
        if have_.contains n then apE (.name n) pv else .name n
      [(nm! "step", [nm! "m"], apE (.name (nm! "sp")) ([.name (nm! "m"), .name (nm! "nil")] ++ slots))]
  if have_.contains (nm! "loop") then some (eqs ++ step)
  else if have_.contains (nm! "loop1") then none
  else
    let conts := lt.outcome.ftys.map fun c =>
      if c.1 == lt.stepped then apE (.name (nm! "f")) (pv ++ [.name (nm! "n2")])
      else if c.1 == lt.done then apE (.name lt.value) [.name (nm! "m")]
      else .name ((lt.mapping.lookup c.1).getD c.1)
    some (eqs ++ step ++
      [(nm! "loop1", [nm! "f", nm! "m", nm! "n2"],
          apE (apE (.name (nm! "step")) pv) (.name (nm! "m") :: conts)),
       (nm! "loop", [nm! "n", nm! "m"],
          apE (.name (nm! "n")) [.name lt.timeout,
            apE (apE (.name (nm! "loop1")) pv) [.name (nm! "loop"), .name (nm! "m")]])])

/-- **Generation** (`generate`): with an object type, every interpreter
    core gets its `step` and fuel loop, and the walker, the rebuilder and
    the default step equations are appended, each unless the file defines
    its name.  Without one, the file is unchanged. -/
def generate (ds : List Decl) : Option (List Decl) :=
  let tys := ds.filterMap fun d => match d with | .ty t => some t | _ => none
  match findObject tys with
  | none => none
  | some none => some ds
  | some (some o) =>
    match findLoop tys o with
    | none => none
    | some lt =>
      let taken := ds.flatMap fun d =>
        match d with
        | .ty t => t.ctors.map (·.1)
        | .eqn e => [e.name]
        | .macro n _ _ _ => [n]
        | .core c _ _ => [c]
        | .qdef n _ => [n]
        | .sig _ _ => []
      let extra := (walker o ++ defaultSteps o lt).filter fun e => !taken.contains e.1
      let fill : Decl → Option Decl := fun d =>
        match d with
        | Decl.core c ps eqs =>
          if isInterp o eqs then (fillCore o lt ps eqs).map (Decl.core c ps ·) else some d
        | _ => some d
      (ds.mapM fill).map fun l =>
        l ++ extra.map fun (n, ps, b) => Decl.eqn ⟨n, n, ps, b, none, []⟩

/-- **Reading a file**: parsing, then generation. -/
def readWith (u : Bool) (src : List Nat) : Option (List Decl) := (parseWith u src).bind generate

def readFile (src : List Nat) : Option (List Decl) := readWith false src

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

-- ---------------------------------------------------------------------------
-- η-lifting (`skijack.compile(eta=True)`)
-- ---------------------------------------------------------------------------

/-- Free occurrence, before resolution. -/
def CSrc.occurs (x : Nat) : CSrc → Bool
  | .glob _ => false
  | .var y => y == x
  | .app f a => f.occurs x || a.occurs x
  | .lam y b => y != x && b.occurs x

/-- Nodes, a bound on the η pass's recursion. -/
def CSrc.size : CSrc → Nat
  | .app f a => f.size + a.size + 1
  | .lam _ b => b.size + 1
  | _ => 1

/-- A λ chain's parameters, outermost first, and its body. -/
def CSrc.peel : CSrc → List Nat × CSrc
  | .lam x b => (x :: b.peel.1, b.peel.2)
  | e => ([], e)

/-- `e` η-reduced over the parameters `ps`, last parameter first: `e' p`
    with `p` not free in `e'` gives `e'`, and so on; `none` when some
    parameter does not reduce away. -/
def etaStrip : List Nat → CSrc → Option CSrc
  | [], e => some e
  | p :: ps, .app f (.var q) => if q == p && !f.occurs p then etaStrip ps f else none
  | _ :: _, _ => none

/-- A λ chain over `ps`. -/
def CSrc.lams : List Nat → CSrc → CSrc
  | [], b => b
  | x :: xs, b => .lam x (CSrc.lams xs b)

/-- The η pass, with fuel: every recursive call is on a proper subterm, so
    `e.size` suffices (`CSrc.eta`). -/
def CSrc.etaN : Nat → CSrc → CSrc
  | 0, e => e
  | n + 1, .app f a => .app (f.etaN n) (a.etaN n)
  | n + 1, e@(.lam _ _) =>
    match etaStrip e.peel.1.reverse e.peel.2 with
    | some r => r.etaN n
    | none => CSrc.lams e.peel.1 (e.peel.2.etaN n)
  | _ + 1, e => e

/-- **η-lifting**, `skijack`'s `_Codegen.lift` with `eta=True`: a λ chain
    whose body η-reduces over all its parameters, `λ p₁ … pₙ. e p₁ … pₙ`
    with no `pᵢ` free in `e`, is `e`, compiled where the chain stood.
    Lifted, it would be a combinator applied to the binders `e` captures:
    `λ g t. g t` is `I`, so case lowering's `λ t. g t` became `I ⬝ g`.  A
    chain that does not reduce whole is lifted as before (abstraction
    η-reduces its tail anyway). -/
def CSrc.eta (e : CSrc) : CSrc := e.etaN e.size

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
    | _, _ => none
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

/-- An equation, η-lifted. -/
def FEqn.eta (e : FEqn) : FEqn := { e with body := e.body.eta }

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
  match readFile src with
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
    (es.filter fun e => e.core.isNone).map (·.name) ++
    ds.filterMap (fun d => match d with | .qdef n _ => some n | _ => none)
  let cores := ds.filterMap fun d => match d with | .core c _ eqs => some (c, eqs.map (·.1)) | _ => none
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
    if nodup defined && nodup (tys.map (·.name)) && nodup (cores.map (·.1)) &&
        cores.all (fun c => nodup c.2) then
      some ((prelude.filter fun p => !defined.contains p.1) ++ fes ++ loops)
    else none

-- ---------------------------------------------------------------------------
-- Level 1: quotation, runs, scry and namespace literals (`expand.py`, pass 6)
-- ---------------------------------------------------------------------------

/-- `find_answer_type`: the one carrier type besides the object, outcome
    and result types, with its carrier `hit` and last leaf `notyet`;
    `some none` when there is none, `none` when the file is refused. -/
def findAnswer (tys : List TypeDecl) (o : ObjT) (lt : LoopT) : Option (Option (Nm × Nm)) :=
  let cands := tys.filterMap fun d =>
    if d.name == o.decl.name || d.name == lt.outcome.name || d.name == lt.result then none
    else (carrier d o.decl.name).map fun r => (d, r.1)
  match cands with
  | [] => some none
  | [(d, hit)] => ((d.ftys.filter (·.2.isEmpty)).getLast?).map fun nt => some (hit.1, nt.1)
  | _ => none

/-- `find_path_type`: the type named `path`, which must be
    `Nil | Cons seg path`: its nil, its cons and its segment type. -/
def findPath (tys : List TypeDecl) : Option (Option (Nm × Nm × Nm)) :=
  match tys.find? (·.name == nm! "path") with
  | none => some none
  | some d =>
    let nils := d.ftys.filter (·.2.isEmpty)
    let conses := d.ftys.filter fun c => c.2.length == 2 && c.2[1]? == some d.name
    match nils, conses with
    | [n], [c] =>
      if d.ftys.length == 2 then (c.2.head?).map fun sg => some (n.1, c.1, sg) else none
    | _, _ => none

/-- What a quotation is compiled against: the types, the macros, the
    object type's leaves with their constructors' terms, its application
    constructor's term, and the path type. -/
structure QCtx where
  tys : List TypeDecl
  ms : List (Nm × Macro)
  leaves : List (Nm × Term)
  appT : Term
  path : Option (Nm × Nm × Nm)
  /-- η-lifting (`CSrc.eta`) on. -/
  eta : Bool

/-- A segment's constructor: its tag with the first letter capitalized. -/
def capital : Nm → Nm
  | c :: r => (if 97 ≤ c && c ≤ 122 then c - 32 else c) :: r
  | [] => []

/-- `path_expr`: `/a/b` is `Cons A (Cons B Nil)`, each tag a constructor
    of the segment type; a payload is refused. -/
def pathExpr (q : QCtx) (p : List (Nm × Bool)) : Option Expr :=
  match q.path with
  | none => none
  | some (nilC, consC, seg) =>
    p.foldr (fun s acc => acc.bind fun e =>
      let c := capital s.1
      if !s.2 && (q.tys.find? (·.name == seg)).any (·.ctors.any (·.1 == c)) then
        some (apE (.name consC) [.name c, e])
      else none) (some (.name nilC))

/-- `?^p` inside a quotation: the object type's `Scry` leaf applied to the
    path. -/
def scryOf (q : QCtx) (p : List (Nm × Bool)) : Option Expr :=
  match q.leaves.lookup (nm! "Scry") with
  | none => none
  | some _ => (pathExpr q p).map fun pe => .app (.name (nm! "Scry")) pe

/-- A nested datum's placeholder name, which no source name spells. -/
def placeholder (k : Nat) : Nm := 0 :: decimal k

mutual
  /-- `strip`: each nested quotation compiled by `nest` and replaced by a
      placeholder, each scry by its expression; a nested quotation with
      fuel or an interpreter, a run or a namespace literal is refused. -/
  def stripE (nest : Expr → Option Term) (sc : List (Nm × Bool) → Option Expr) :
      Expr → List (Nm × Term) → Option (Expr × List (Nm × Term))
    | .name n, s => some (.name n, s)
    | .app a b, s =>
      match stripE nest sc a s with
      | none => none
      | some (a', s1) => (stripE nest sc b s1).map fun r => (.app a' r.1, r.2)
    | .case e bs, s =>
      match stripE nest sc e s with
      | none => none
      | some (e', s1) => (stripB nest sc bs s1).map fun r => (.case e' r.1, r.2)
    | .lam x b, s => (stripE nest sc b s).map fun r => (.lam x r.1, r.2)
    | .cell items, s => (stripI nest sc items s).map fun r => (.cell r.1, r.2)
    | .pick n e, s => (stripE nest sc e s).map fun r => (.pick n r.1, r.2)
    | .quote e .none, s =>
      (nest e).map fun t => (.name (placeholder s.length), s ++ [(placeholder s.length, t)])
    | .scry p, s => (sc p).map fun e => (e, s)
    | _, _ => none
  def stripB (nest : Expr → Option Term) (sc : List (Nm × Bool) → Option Expr) :
      Branches → List (Nm × Term) → Option (Branches × List (Nm × Term))
    | .nil, s => some (.nil, s)
    | .cons c xs body rest, s =>
      match stripE nest sc body s with
      | none => none
      | some (b', s1) => (stripB nest sc rest s1).map fun r => (.cons c xs b' r.1, r.2)
  def stripI (nest : Expr → Option Term) (sc : List (Nm × Bool) → Option Expr) :
      Items → List (Nm × Term) → Option (Items × List (Nm × Term))
    | .nil, s => some (.nil, s)
    | .cons e rest, s =>
      match stripE nest sc e s with
      | none => none
      | some (e', s1) => (stripI nest sc rest s1).map fun r => (.cons e' r.1, r.2)
end

/-- Globals resolved inside a quotation (`qresolve`): a nested datum, then
    a leaf of the object type as the free variable `k + j`, above every
    binder, then a level-0 name. -/
def CSrc.resolveQ (subs : List (Nm × Term)) (leafIx : Nm → Option Nat) (k : Nat)
    (done : List (Nm × Term)) : CSrc → Option Src
  | .glob n =>
    match subs.lookup n with
    | some t => some (.glob t)
    | none =>
      match leafIx n with
      | some j => some (.var (k + j))
      | none => (resolveIn done n).map .glob
  | .var x => some (.var x)
  | .app f a =>
    match CSrc.resolveQ subs leafIx k done f, CSrc.resolveQ subs leafIx k done a with
    | some f', some a' => some (.app f' a')
    | _, _ => none
  | .lam x b => (CSrc.resolveQ subs leafIx k done b).map (.lam x)

/-- **The encoding** (`Encoder.quote`): `S`, `K`, `I` to the leaves of those
    names, the variable `k + j` to leaf `j`, an application to the
    application constructor. -/
def encodeO (leaves : List (Nm × Term)) (appT : Term) (k : Nat) : OTerm → Option Term
  | .S => leaves.lookup [83]
  | .K => leaves.lookup [75]
  | .I => leaves.lookup [73]
  | .var i => if k ≤ i then (leaves[i - k]?).map (·.2) else none
  | .app f a =>
    match encodeO leaves appT k f, encodeO leaves appT k a with
    | some f', some a' => some (appT ⬝ f' ⬝ a')
    | _, _ => none

/-- **A quotation's datum** (`quote_expr`): nested quotations first, then
    macros, case lowering, and compilation as a definition with the leaves
    free, then the encoding.  The fuel bounds the nesting of quotations. -/
def quoteAt (q : QCtx) (done : List (Nm × Term)) : Nat → Expr → Option Term
  | 0, _ => none
  | f + 1, e =>
    match stripE (quoteAt q done f) (scryOf q) e [] with
    | none => none
    | some (body, subs) =>
      match expandE 400 q.ms 0 0 200000 body with
      | none => none
      | some (b, _) =>
        match dExpr q.tys id [] b 0 with
        | none => none
        | some (cs, k) =>
          let cs := if q.eta then cs.eta else cs
          match cs.resolveQ subs (fun n => q.leaves.findIdx? (·.1 == n)) k done with
          | none => none
          | some src => encodeO q.leaves q.appT k (compDefF [] src)

/-- A namespace literal's resolver (`resolver_term`):
    `λp. EQ5 p k1 (hit a1) (… notyet)`, first match winning. -/
def resolverTerm (eq hit notyet : Term) (facts : List (Term × Term)) : Term :=
  toTerm (absNF [0] (facts.foldr (fun f body =>
    eq.toO ⬝ₒ .var 0 ⬝ₒ f.1.toO ⬝ₒ (hit.toO ⬝ₒ f.2.toO) ⬝ₒ body) notyet.toO))

/-- A namespace literal's facts, as a list. -/
def Facts.toList : Facts → List (List (Nm × Bool) × Expr)
  | .nil => []
  | .cons p v r => (p, v) :: r.toList

/-- A dictionary update: `n` set to `t`, in place when present. -/
def dset (d : List (Nm × Term)) (p : Nm × Term) : List (Nm × Term) :=
  if d.any (·.1 == p.1) then d.map fun q => if q.1 == p.1 then p else q else d ++ [p]

/-- A level-1 run, before packaging: its name, its interpreter, its datum
    and its fuel. -/
structure Run where
  name : Nm
  interp : Option Expr
  datum : Term
  fuel : QFuel

/-- One level-1 declaration in pass 6a: a namespace literal or a datum is
    compiled and joins the environment, and the pending equations are
    retried; a run's datum is compiled and kept. -/
def step1 (q : QCtx) (hitNt : Option (Term × Term))
    (st : List (Nm × FEqn) × List (Nm × Term) × List Run) (d : Nm × Expr) :
    Option (List (Nm × FEqn) × List (Nm × Term) × List Run) :=
  let (pend, done, runs) := st
  let join := fun (t : Term) =>
    let r := passes (pend.length + 1) (done ++ [(d.1, t)]) pend
    (r.1, r.2, runs)
  match d.2 with
  | .nslit facts =>
    match hitNt, done.lookup (nm! "EQ5") with
    | some (hit, nt), some eq =>
      (facts.toList.mapM fun (pv : List (Nm × Bool) × Expr) =>
        let p := pv.1
        match pv.2 with
        | Expr.quote e QFuel.none =>
          match (pathExpr q p).bind fun pe => quoteAt q done (depthE pe + 1) pe,
              quoteAt q done (depthE e + 1) e with
          | some k, some a => some (k, a)
          | _, _ => none
        | _ => none).map fun fs => join (resolverTerm eq hit nt fs)
    | _, _ => none
  | .quote e .none => (quoteAt q done (depthE e + 1) e).map join
  | .quote e fu =>
    (quoteAt q done (depthE e + 1) e).map fun t => (pend, done, runs ++ [⟨d.1, none, t, fu⟩])
  | .run i e fu =>
    (quoteAt q done (depthE e + 1) e).map fun t => (pend, done, runs ++ [⟨d.1, some i, t, fu⟩])
  | _ => none

/-- A type's constructors' terms, by name. -/
def allCtorTerms (tys : List TypeDecl) : List (Nm × Term) := (tys.map ctorTerms).flatten

/-- Passes 6a and 6b over the file's level-1 declarations `qs`, which need
    an object type, and the loop, answer and path types well formed. -/
def level1 (ds : List Decl) (tys : List TypeDecl) (pend : List (Nm × FEqn))
    (done : List (Nm × Term)) (qs : List (Nm × Expr)) (eta : Bool := false) :
    Option (List (Nm × FEqn) × List (Nm × Term) × List Run) :=
  match findObject tys with
  | some (some o) =>
    match findLoop tys o with
    | none => none
    | some lt =>
      match findAnswer tys o lt, findPath tys with
      | some ans, some pt =>
        let cts := ctorTerms o.decl
        let leaves := o.leaves.map fun c => (c.1, (cts.lookup c.1).getD K)
        let q : QCtx := ⟨tys, macrosOf ds, leaves, (cts.lookup o.app).getD K, pt, eta⟩
        let hitNt := ans.bind fun (h, n) =>
          match (allCtorTerms tys).lookup h, (allCtorTerms tys).lookup n with
          | some ht, some nt => some (ht, nt)
          | _, _ => none
        (qs.foldlM (step1 q hitNt) (pend, done, [])).map fun st =>
          let r := passes (st.1.length + 1) st.2.1 st.1
          (r.1, r.2, st.2.2)
      | _, _ => none
  | _ => none

/-- The file's output (`expand_all`): the compiled environment, then each
    core equation under its bare name when no other core defines it and
    no level-1 declaration takes it, then each interpreter core's name for
    its loop. -/
def assemble (ds : List Decl) (done : List (Nm × Term)) : List (Nm × Term) :=
  let es := eqns ds
  let quoted := ds.filterMap fun d => match d with | .qdef n _ => some n | _ => none
  let bare := es.filterMap fun e =>
    if e.core.isSome && (es.filter fun e' => e'.core.isSome && e'.bare == e.bare).length == 1 &&
        !quoted.contains e.bare
    then (done.lookup e.name).map fun t => (e.bare, t) else none
  let loops := ds.filterMap fun d =>
    match d with
    | .core c _ eqs =>
      if eqs.any (·.1 == nm! "loop") then (done.lookup (c ++ [46] ++ nm! "loop")).map (c, ·)
      else none
    | _ => none
  (done ++ bare ++ loops).foldl dset []

/-- Pass 6c: each run with a numeric fuel is its interpreter core's loop
    applied to the core's arguments, the fuel numeral and the datum; a
    run without an interpreter uses the core `whnfF`.  A run under the
    runtime's policy has no term. -/
def packageRuns (ds : List Decl) (tys : List TypeDecl) (done : List (Nm × Term))
    (eta : Bool := false) : List (Nm × Term) → List Run → Option (List (Nm × Term))
  | out, [] => some out
  | out, r :: rs =>
    let cores := ds.filterMap fun d =>
      match d with
      | .core c ps eqs => some (c, ps.length, eqs.any (·.1 == nm! "loop"))
      | _ => none
    let spine? : Option (Nm × List Expr) :=
      match r.interp with
      | none => if cores.any (·.1 == nm! "whnfF") then some (nm! "whnfF", []) else none
      | some i =>
        match spine i with
        | (.name c, args) =>
          match cores.find? (·.1 == c) with
          | some (_, k, _) => if args.length == k then some (c, args) else none
          | none => none
        | _ => none
    let param := fun (a : Expr) =>
      match expandE 400 (macrosOf ds) 0 0 200000 a with
      | none => none
      | some (b, _) =>
        match dExpr tys id [] b 0 with
        | none => none
        | some (cs, _) =>
          let cs := if eta then cs.eta else cs
          if cs.globs.all fun g => (resolveIn done g).isSome then
            some (toTerm (compDefF [] (cs.resolve fun g => (resolveIn done g).getD K)))
          else none
    match spine? with
    | none => none
    | some (c, args) =>
      if !(cores.any fun p => p.1 == c && p.2.2) then none
      else
        match out.lookup c, args.mapM param with
        | some it, some ps =>
          match r.fuel with
          | .num n =>
            match out.lookup (nm! "zero"), out.lookup (nm! "suc") with
            | some z, some sc =>
              let numeral := (List.range n).foldl (fun t _ => sc ⬝ t) z
              packageRuns ds tys done eta (dset out (r.name, ps.foldl (· ⬝ ·) it ⬝ numeral ⬝ r.datum)) rs
            | _, _ => none
          | _ => packageRuns ds tys done eta out rs
        | _, _ => none

/-- The lowered equations, η-lifted when `eta` is on. -/
def etaFEqns : Bool → Option (List (Nm × FEqn)) → Option (List (Nm × FEqn))
  | false, o => o
  | true, o => o.map fun fes => fes.map fun p => (p.1, p.2.eta)

/-- A file's compiled output and the environment its equations were
    compiled in, or `none` when it is refused.  With `eta`, every λ chain
    is η-lifted (`CSrc.eta`): equations, quotations and runs' arguments,
    each place `skijack` compiles code. -/
def compileDecls (ds : List Decl) (eta : Bool := false) :
    Option (List (Nm × Term) × List (Nm × Term)) :=
  match etaFEqns eta (fileFEqns ds) with
  | none => none
  | some fes =>
    let tys := types ds
    let r := passes (fes.length + 1) (allCtorTerms tys) fes
    let qs := ds.filterMap fun d => match d with | .qdef n e => some (n, e) | _ => none
    let l1 := if qs.isEmpty then some (r.1, r.2, []) else level1 ds tys r.1 r.2 qs eta
    match l1 with
    | none => none
    | some (pend, done, runs) =>
      if pend.isEmpty then (packageRuns ds tys done eta (assemble ds done) runs).map (·, done)
      else none

/-- **Compile a file**, in the ASCII (`u = false`) or Unicode lexicon:
    every constructor, equation and level-1 declaration to the closed term
    `skijack` emits, a core's equation also under its bare name when no
    other core defines it.  A file `skijack` refuses is refused. -/
def compileWith (u : Bool) (src : List Nat) (eta : Bool := false) : Option (List (Nm × Term)) :=
  (readWith u src).bind fun ds => (compileDecls ds eta).map (·.1)

/-- The environment a file's equations were compiled in: its compiled
    program-level names, `core.eq`s and level-1 data, without the bare
    aliases or the runs. -/
def compiledEnv (u : Bool) (src : List Nat) : List (Nm × Term) :=
  match (readWith u src).bind compileDecls with
  | some r => r.2
  | none => []

def compileFile (src : List Nat) : Option (List (Nm × Term)) := compileWith false src

/-- `compileFile` with η-lifting (`skijack.compile(eta=True)`), the
    compilation of a SKIlark predicate's source. -/
def compileFileEta (src : List Nat) : Option (List (Nm × Term)) := compileWith false src true

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
