import Ski.Air

open Term

/-!
# Checking a table against the AIR

`checkB` decides the AIR's constraints (`Air.Accepts`) on a concrete table:
a memory table, a term and a list of rows.  It is what a table produced
outside Lean — by the Plonky3 prover in `bench/plonky3` — is checked
against.

**The theorems.**  `checkB` decides the AIR's constraints: a table it
accepts is accepted by the AIR, with the rows read off the list
(`checkB_sound`), and conversely (`checkB_complete`).  So by
`air_sound_eval` the term evaluates to the value an accepted table ends on.
`checkA` is the same checker over an array (`checkA_eq`, `checkA_iff`).

**The format** read by `bench/AirCheck.lean`: one item per line, and
nothing after the rows.
- the term, in prefix form (`` ` `` for application);
- the number of memory cells, then each cell: `S`, `K`, `I`, `N` (the
  empty stack), `A f x` (an application) or `C x r` (a stack cell);
- the number of rows, then each row: `hd stk ctr`.
-/

namespace Air

open Mach

/-- Each row steps to the next or has halted and repeats. -/
def chainB (M : List Cell) : List Row → Bool
  | r :: r' :: rest =>
    (decide (stepRow M r = some r') || (haltRow M r && decide (r' = r))) && chainB M (r' :: rest)
  | _ => true

/-- **The AIR's constraints, decided** on a table. -/
def checkB (M : List Cell) (t : Term) : List Row → Bool
  | [] => false
  | r0 :: rest =>
    decide (M.take r0.ctr = (load t).heap) && decide (r0.hd = (load t).hd) &&
      decide (r0.stk = (load t).stk) && decide (r0.ctr = (load t).heap.length) &&
      chainB M (r0 :: rest) && haltRow M ((r0 :: rest).getLast (List.cons_ne_nil _ _))

/-- The rows of a list, as the AIR's row function. -/
def rowFn (rows : List Row) (i : Nat) : Row := rows.getD i ⟨0, 0, 0⟩

theorem chainB_trans {M : List Cell} : ∀ {rows : List Row}, chainB M rows = true →
    ∀ i, i + 1 < rows.length →
      stepRow M (rowFn rows i) = some (rowFn rows (i + 1)) ∨
        (haltRow M (rowFn rows i) = true ∧ rowFn rows (i + 1) = rowFn rows i)
  | [], _, i, hi => absurd hi (by simp)
  | [_], _, i, hi => absurd hi (by simp)
  | r :: r' :: rest, h, i, hi => by
    unfold chainB at h
    rw [Bool.and_eq_true, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_iff,
      decide_eq_true_iff] at h
    cases i with
    | zero =>
      show stepRow M r = some r' ∨ (haltRow M r = true ∧ r' = r)
      exact h.1
    | succ i =>
      have := chainB_trans h.2 i (by simp at hi ⊢; omega)
      exact this

theorem getLast_eq_getD : ∀ (rows : List Row) (h : rows ≠ []),
    rows.getLast h = rowFn rows (rows.length - 1)
  | [r], _ => rfl
  | r :: r' :: rest, _ => by
    rw [List.getLast_cons (List.cons_ne_nil _ _), getLast_eq_getD (r' :: rest) (List.cons_ne_nil _ _)]
    show (r' :: rest).getD ((r' :: rest).length - 1) _ = (r :: r' :: rest).getD ((r :: r' :: rest).length - 1) _
    simp

/-- **`checkB` is sound**: a table it accepts, the AIR accepts. -/
theorem checkB_sound {M : List Cell} {t : Term} {rows : List Row} (h : checkB M t rows = true) :
    Accepts M t rows.length (rowFn rows) := by
  cases rows with
  | nil => cases h
  | cons r0 rest =>
    unfold checkB at h
    simp only [Bool.and_eq_true, decide_eq_true_iff] at h
    obtain ⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩ := h
    refine ⟨by simp, h0, h1, h2, h3, chainB_trans h4, ?_⟩
    rw [← getLast_eq_getD]
    exact h5

theorem rowFn_cons (r : Row) (rows : List Row) (i : Nat) :
    rowFn (r :: rows) (i + 1) = rowFn rows i := rfl

theorem chainB_of_trans {M : List Cell} : ∀ {rows : List Row},
    (∀ i, i + 1 < rows.length →
      stepRow M (rowFn rows i) = some (rowFn rows (i + 1)) ∨
        (haltRow M (rowFn rows i) = true ∧ rowFn rows (i + 1) = rowFn rows i)) →
    chainB M rows = true
  | [], _ => rfl
  | [_], _ => rfl
  | r :: r' :: rest, h => by
    unfold chainB
    rw [Bool.and_eq_true, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_iff,
      decide_eq_true_iff]
    refine ⟨h 0 (by simp), chainB_of_trans fun i hi => ?_⟩
    have := h (i + 1) (by simp at hi ⊢; omega)
    rw [rowFn_cons, rowFn_cons] at this
    exact this

/-- **`checkB` is complete**: a table the AIR accepts, `checkB` accepts.
    With `checkB_sound`, `checkB` decides the AIR's constraints. -/
theorem checkB_complete {M : List Cell} {t : Term} {rows : List Row}
    (h : Accepts M t rows.length (rowFn rows)) : checkB M t rows = true := by
  cases rows with
  | nil => exact absurd h.pos (Nat.lt_irrefl 0)
  | cons r0 rest =>
    unfold checkB
    simp only [Bool.and_eq_true, decide_eq_true_iff]
    refine ⟨⟨⟨⟨⟨h.heap0, h.hd0⟩, h.stk0⟩, h.ctr0⟩, chainB_of_trans h.trans⟩, ?_⟩
    rw [getLast_eq_getD]
    exact h.final

/-- A table `checkB` accepts proves the evaluation it ends on. -/
theorem checkB_eval {M : List Cell} {t : Term} {rows : List Row} (h : checkB M t rows = true) :
    ∃ v, decode (st M (rowFn rows (rows.length - 1))) = some v ∧ Eval t v :=
  air_sound_eval (checkB_sound h)

-- ---------------------------------------------------------------------------
-- The same checker over any reader, so an array can back it
-- ---------------------------------------------------------------------------

/-- `rd`, over a reader. -/
def rdG (g : Nat → Option Cell) (c a : Nat) : Option Cell := if a < c then g a else none

/-- `wrs`, over a reader. -/
def wrsG (g : Nat → Option Cell) : Nat → List Cell → Bool
  | _, [] => true
  | c, w :: ws => (g c == some w) && wrsG g (c + 1) ws

/-- `stepRow`, over a reader. -/
def stepRowG (g : Nat → Option Cell) (r : Row) : Option Row :=
  match stepG (rdG g r.ctr) r.ctr r.hd r.stk with
  | some (h, s, ws) => if wrsG g r.ctr ws then some ⟨h, s, r.ctr + ws.length⟩ else none
  | none => none

/-- `short`, over a reader. -/
def shortG (g : Nat → Option Cell) (c : Nat) : Nat → Nat → Bool
  | 0, _ => false
  | n + 1, s =>
    match rdG g c s with
    | some .nil => true
    | some (.cons _ s') => shortG g c n s'
    | _ => false

/-- `haltRow`, over a reader. -/
def haltRowG (g : Nat → Option Cell) (r : Row) : Bool :=
  match rdG g r.ctr r.hd with
  | some .I => shortG g r.ctr 1 r.stk
  | some .K => shortG g r.ctr 2 r.stk
  | some .S => shortG g r.ctr 3 r.stk
  | some (.atom _) => true
  | _ => false

/-- `chainB`, over a reader. -/
def chainG (g : Nat → Option Cell) : List Row → Bool
  | r :: r' :: rest =>
    (decide (stepRowG g r = some r') || (haltRowG g r && decide (r' = r))) && chainG g (r' :: rest)
  | _ => true

/-- **The checker over an array**: the memory table in an `Array`, so a read
    is constant time. -/
def checkA (A : Array Cell) (t : Term) : List Row → Bool
  | [] => false
  | r0 :: rest =>
    decide (A.toList.take r0.ctr = (load t).heap) && decide (r0.hd = (load t).hd) &&
      decide (r0.stk = (load t).stk) && decide (r0.ctr = (load t).heap.length) &&
      chainG (fun a => A[a]?) (r0 :: rest) &&
      haltRowG (fun a => A[a]?) ((r0 :: rest).getLast (List.cons_ne_nil _ _))

theorem rd_G (M : List Cell) (c : Nat) : rd M c = rdG (fun a => M[a]?) c := rfl

theorem wrs_G (M : List Cell) : ∀ (c : Nat) (ws : List Cell), wrs M c ws = wrsG (fun a => M[a]?) c ws
  | _, [] => rfl
  | c, w :: ws => by
    show ((M[c]? == some w) && wrs M (c + 1) ws) = ((M[c]? == some w) && wrsG _ (c + 1) ws)
    rw [wrs_G M (c + 1) ws]

theorem stepRow_G (M : List Cell) (r : Row) : stepRow M r = stepRowG (fun a => M[a]?) r := by
  unfold stepRow stepRowG
  rw [rd_G]
  cases stepG (rdG (fun a => M[a]?) r.ctr) r.ctr r.hd r.stk with
  | none => rfl
  | some p =>
    obtain ⟨h, s, ws⟩ := p
    dsimp only
    rw [wrs_G]

theorem short_G (M : List Cell) (c : Nat) : ∀ n s, short M c n s = shortG (fun a => M[a]?) c n s
  | 0, _ => rfl
  | n + 1, s => by
    unfold short shortG
    rw [rd_G]
    cases rdG (fun a => M[a]?) c s with
    | none => rfl
    | some x =>
      cases x with
      | cons _ s' => exact short_G M c n s'
      | _ => rfl

theorem haltRow_G (M : List Cell) (r : Row) : haltRow M r = haltRowG (fun a => M[a]?) r := by
  unfold haltRow haltRowG
  rw [rd_G]
  cases rdG (fun a => M[a]?) r.ctr r.hd with
  | none => rfl
  | some x => cases x <;> first | rfl | exact short_G M r.ctr _ r.stk

theorem chainB_G (M : List Cell) : ∀ rows : List Row, chainB M rows = chainG (fun a => M[a]?) rows
  | [] => rfl
  | [_] => rfl
  | r :: r' :: rest => by
    unfold chainB chainG
    rw [stepRow_G, haltRow_G, chainB_G M (r' :: rest)]

theorem getElem?_fun (A : Array Cell) : (fun a : Nat => A[a]?) = (fun a : Nat => A.toList[a]?) := by
  funext a; rw [Array.getElem?_toList]

/-- **The array checker is the list checker.** -/
theorem checkA_eq (A : Array Cell) (t : Term) (rows : List Row) :
    checkA A t rows = checkB A.toList t rows := by
  have hg : (fun a : Nat => A[a]?) = (fun a : Nat => A.toList[a]?) := by
    funext a; rw [Array.getElem?_toList]
  cases rows with
  | nil => rfl
  | cons r0 rest =>
    simp only [checkA, checkB, chainB_G, haltRow_G, hg]

/-- The array checker decides the AIR's constraints. -/
theorem checkA_iff {A : Array Cell} {t : Term} {rows : List Row} :
    checkA A t rows = true ↔ Accepts A.toList t rows.length (rowFn rows) := by
  rw [checkA_eq]
  exact ⟨checkB_sound, checkB_complete⟩

/-- A table the array checker accepts, the AIR accepts. -/
theorem checkA_sound {A : Array Cell} {t : Term} {rows : List Row} (h : checkA A t rows = true) :
    Accepts A.toList t rows.length (rowFn rows) := by
  rw [checkA_eq] at h
  exact checkB_sound h

end Air
