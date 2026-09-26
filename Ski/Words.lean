import Ski.Scott
open Term

/-!
# Words, quotation tables, and `phi`

`Word` is Joy's kernel as SKIlark compiles it, and `phi w` is the closed
term `skijack` emits for `w`.

## Values

`Item`, `Quotation` and `Stack` are the compiled kernel's `item`, `quot`
and `stack` as Lean data, and `encItem`, `encQuot` and `encStack` apply the
Scott constructors to them.

## The quotation table

No closed `{S, K, I}` term turns a live term into data (Proposition
`prop:quote` of the ski-in-ski manuscript, after Jay and Given-Wilson), so
a quotation's code enters a program only at compile time: SKIlark makes
each static quotation a constructor of a closed sum `quot`, whose body is
that quotation's compiled code.  `Quotation.stat k` is the table's `k`-th
static quotation; `cons`, `unit` and `then` are built at run time.

The sum is per program, and so are the terms that build or eliminate it:
`wQcons`, `wCat`, `wUnit` and `applyU` differ between compilations
(`canon_wQcons_differs` and its siblings), while the other nine words do
not.  A `Kit` is one table: its size `n`, its `quot` constructors, those
four terms, and each static quotation's body as words (`body`) and as
the compiled term (`bodyT`).  Everything proved over a `Kit` holds for
every table.  What a table must satisfy is collected in the law classes
`KitElim`, `KitWords` and `KitApply`; `Ski/Laws.lean` proves all three
for the kit compiled from any valid table (`Table.kit`, `Ski/Kernel.lean`).

A static index is meaningful only below `n`; `Quotation.ok n` says a
quotation mentions no other.

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
  /-- A quotation, defunctionalized: `stat k` is the table's `k`-th static
      quotation, and `[P] [Q] cat` is `cons [P] (then Q)`. -/
  inductive Quotation
    | stat : Nat → Quotation
    | cons : Item → Quotation → Quotation
    | unit : Item → Quotation
    | then : Quotation → Quotation
end

/-- The top of the stack is the head of the list. -/
abbrev Stack := List Item

mutual
  /-- Every static index is below `n`. -/
  def Item.ok (n : Nat) : Item → Bool
    | .num _ => true
    | .quot q => q.ok n
  def Quotation.ok (n : Nat) : Quotation → Bool
    | .stat k => decide (k < n)
    | .cons x r => x.ok n && r.ok n
    | .unit x => x.ok n
    | .then r => r.ok n
end

def encNat : Nat → Term
  | 0 => Scott.Zero
  | n + 1 => Scott.Suc ⬝ encNat n

/-- Joy's kernel.  `i` is SKIlark's `Do`; `cons` is `Qcons`. -/
inductive Word
  | dup | swap | pop | cons | cat | unit | dip | i | ifz
  | lit (n : Nat) | quote (q : Quotation) | add

def Word.ok (n : Nat) : Word → Bool
  | .quote q => q.ok n
  | _ => true

/-- A quotation table, as the compiler closes it. -/
class Kit where
  /-- The number of static quotations. -/
  n : Nat
  /-- `Qs k` constructs the `k`-th static quotation, for `k < n`. -/
  Qs : Nat → Term
  QCons : Term
  QUnit : Term
  QThen : Term
  wQcons : Term
  wCat : Term
  wUnit : Term
  applyU : Term
  /-- The `k`-th static quotation's code. -/
  body : Nat → List Word
  /-- Its compiled term, `b_k`, which takes the eliminator first. -/
  bodyT : Nat → Term

variable [Kit]

mutual
  def encItem : Item → Term
    | .num n => Scott.Num ⬝ encNat n
    | .quot q => Scott.Quot ⬝ encQuot q
  def encQuot : Quotation → Term
    | .stat k => Kit.Qs k
    | .cons x r => Kit.QCons ⬝ encItem x ⬝ encQuot r
    | .unit x => Kit.QUnit ⬝ encItem x
    | .then r => Kit.QThen ⬝ encQuot r
end

def encStack : Stack → Term
  | [] => Scott.Empty
  | a :: s => Scott.Push ⬝ encItem a ⬝ encStack s

/-- The compiled word terms. -/
def phi : Word → Term
  | .dup => Scott.wDup
  | .swap => Scott.wSwap
  | .pop => Scott.wPop
  | .cons => Kit.wQcons
  | .cat => Kit.wCat
  | .unit => Kit.wUnit
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
quotation, and a quotation can loop (`[dup i] dup i`), so no total
function computes them.  The model takes the quotation's meaning as the
parameter `ap`, as the compiled terms take the eliminator `ap`, and is
total in every word.

Divergence is therefore not an outcome.  `Outcome` has `val` and `err`,
the compiled kernel's `RVal` and `RErr`; a run that never returns has no
outcome, and the relation that runs quotations (`Run`, `Ski/Apply.lean`)
is where its absence shows up as the absence of a derivation, exactly as
`CEval` in `lean-nock` leaves an infinite `while` underivable.  `RTime` is
the fuelled `apply`'s timeout; no word produces it on its own, and it
decodes to no outcome.
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
