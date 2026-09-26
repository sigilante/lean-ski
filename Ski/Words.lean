import Ski.Scott
open Term

/-!
# Words and `phi`

`Word` is Joy's kernel as SKIlark compiles it, and `phi w` is the closed
term `skijack` emits for `w`, taken from `Ski/Scott.lean`; the canonicity
tests in `Ski/Corpus.lean` pin each term against a second compilation.

## Values

`Item`, `Quotation` and `Stack` are the compiled kernel's `item`, `quot`
and `stack` as Lean data, and `encItem`, `encQuot` and `encStack` apply the
Scott constructors of `Ski/Scott.lean` to them.

No closed `{S, K, I}` term turns a live term into data (Proposition
`prop:quote` of the ski-in-ski manuscript, after Jay and Given-Wilson), so
a quotation's code enters a program only at compile time: SKIlark makes
each static quotation a constructor of a closed sum `quot`.  The sum is
therefore per program, and so are the terms that build or eliminate it:
`wQcons`, `wCat`, `wUnit` and `applyU` differ between compilations
(`canon_wQcons_differs` and its siblings), while the other nine words do
not.  The terms of `Ski/Scott.lean` come from a program with no bracketed
quotations, so `Quotation` here is `QCons | QUnit | QThen` alone, and a
quotation carries data and `i` but no code (see `Ski/Total.lean`).

## Parameters

`wLit` and `wQuote` take their literal as a term, so `phi (.lit n)` is
`wLit` applied to `encNat n`.  `wDip`, `wDo` and `wIfz` take the quotation
eliminator `ap` first; `phi` leaves them unapplied, and their contracts
quantify over `ap`.
-/

mutual
  inductive Item
    | num : Nat → Item
    | quot : Quotation → Item
  /-- A quotation, defunctionalized: `[P] [Q] cat` is `cons [P] (then Q)`. -/
  inductive Quotation
    | cons : Item → Quotation → Quotation
    | unit : Item → Quotation
    | then : Quotation → Quotation
end

/-- The top of the stack is the head of the list. -/
abbrev Stack := List Item

def encNat : Nat → Term
  | 0 => Scott.Zero
  | n + 1 => Scott.Suc ⬝ encNat n

mutual
  def encItem : Item → Term
    | .num n => Scott.Num ⬝ encNat n
    | .quot q => Scott.Quot ⬝ encQuot q
  def encQuot : Quotation → Term
    | .cons x r => Scott.QCons ⬝ encItem x ⬝ encQuot r
    | .unit x => Scott.QUnit ⬝ encItem x
    | .then r => Scott.QThen ⬝ encQuot r
end

def encStack : Stack → Term
  | [] => Scott.Empty
  | a :: s => Scott.Push ⬝ encItem a ⬝ encStack s

/-- Joy's kernel.  `i` is SKIlark's `Do`; `cons` is `Qcons`. -/
inductive Word
  | dup | swap | pop | cons | cat | unit | dip | i | ifz
  | lit (n : Nat) | quote (q : Quotation) | add

/-- The compiled word terms. -/
def phi : Word → Term
  | .dup => Scott.wDup
  | .swap => Scott.wSwap
  | .pop => Scott.wPop
  | .cons => Scott.wQcons
  | .cat => Scott.wCat
  | .unit => Scott.wUnit
  | .dip => Scott.wDip
  | .i => Scott.wDo
  | .ifz => Scott.wIfz
  | .lit n => Scott.wLit ⬝ encNat n
  | .quote q => Scott.wQuote ⬝ encQuot q
  | .add => Scott.wAdd

/-!
## The C model

`cw ap w S` is the outcome of word `w` on stack `S`, transcribed from the
equations of `skilark.joy.COMPILED_KERNEL`.  It is `lean-nock`'s `cw`,
with one change: the higher-order words `dip`, `i` and `ifz` run a
quotation, and a quotation can loop (`[dup cons] dup cons i`), so no total
function computes them.  The model takes the quotation's meaning as the
parameter `ap`, as the compiled terms take the eliminator `ap`, and is
total in every word.

Divergence is therefore not an outcome.  `Outcome` has `val` and `err`,
the compiled kernel's `RVal` and `RErr`; a run that never returns has no
outcome, and the relation that runs quotations (§2.6 of `PLAN.md`, where
`ap` is realized) is where its absence shows up as the absence of a
derivation, exactly as `CEval` in `lean-nock` leaves an infinite `while`
underivable.  `RTime` is the fuelled `apply`'s timeout; no word produces
it on its own, and it decodes to no outcome.
-/

inductive Outcome
  | val (s : Stack)
  | err

def cw (ap : Quotation → Stack → Outcome) : Word → Stack → Outcome
  | .dup, a :: t => .val (a :: a :: t)
  | .swap, a :: b :: u => .val (b :: a :: u)
  | .pop, _ :: t => .val t
  | .cons, .quot r :: b :: u => .val (.quot (.cons b r) :: u)
  | .cat, .quot r :: .quot l :: u => .val (.quot (.cons (.quot l) (.then r)) :: u)
  | .unit, a :: t => .val (.quot (.unit a) :: t)
  | .dip, .quot r :: b :: u =>
    match ap r u with
    | .val v => .val (b :: v)
    | .err => .err
  | .i, .quot r :: t => ap r t
  | .ifz, .quot _ :: .quot z :: .num 0 :: v => ap z v
  | .ifz, .quot sc :: .quot _ :: .num (m + 1) :: v => ap sc (.num m :: v)
  | .lit n, s => .val (.num n :: s)
  | .quote q, s => .val (.quot q :: s)
  | .add, .num m :: .num n :: u => .val (.num (m + n) :: u)
  | _, _ => .err
