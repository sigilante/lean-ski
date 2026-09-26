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
Scott constructors of `Ski/Scott.lean` to them.  `Quotation` has no static
constructors: the terms of `Ski/Scott.lean` come from a program with no
bracketed quotations, so its `quot` sum is `QCons | QUnit | QThen` alone.
A program with `k` static quotations compiles `wQcons`, `wCat` and `wUnit`
to different terms (`canon_wQcons_differs` and its two siblings), and
extending `Quotation` to it means one more generated `phi` per `k`.

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
