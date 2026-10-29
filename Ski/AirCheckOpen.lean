import Ski.SudokuCheck

open Term

/-!
# Checking a table of an open term against the AIR

`checkA` decides the AIR's constraints on a table that starts from a loaded
closed term.  `checkFromB` decides them from any machine state, the
constraint set of `AcceptsFrom`: a table it accepts is accepted from that
state (`checkFromB_sound`), and conversely (`checkFromB_complete`).
`checkFromA`, the Sudoku checker's array version (`Ski/SudokuCheck.lean`,
sound there), is this checker (`checkFromA_eq`), so it decides
`AcceptsFrom` (`checkFromA_iff`).

`checkOA A t` starts from `oload t`, an open term loaded with each variable
`i` as the atom cell `i`.  The machine treats an atom as inert: an atom at
the head halts (`haltRow`).

**The theorems.**
- `checkOA_iff`: `checkOA` decides `AcceptsFrom` from `oload t`.
- `checkOA_open`: a table `checkOA` accepts ends on a halted state that
  reads back as an open head reduct of `t` (`air_sound_open`).
- `checkOA_close`: so for every closing substitution `σ`, the closed term
  `t.close σ` head-reduces to that reduct closed by `σ`.  The run is the
  same whatever the atoms stand for.

**The format** read by `bench/AirCheck.lean` is `checkA`'s, with an atom
`i` written `Xi` in the term (decimal, no space: `` ``SX0X12 ``) and `X i`
as a memory cell.
-/

namespace Air

open Mach

/-- **The AIR's constraints from a state, decided** on a table. -/
def checkFromB (M : List Cell) (m0 : Mach) : List Row → Bool
  | [] => false
  | r0 :: rest =>
    decide (M.take r0.ctr = m0.heap) && decide (r0.hd = m0.hd) &&
      decide (r0.stk = m0.stk) && decide (r0.ctr = m0.heap.length) &&
      chainB M (r0 :: rest) && haltRow M ((r0 :: rest).getLast (List.cons_ne_nil _ _))

/-- **`checkFromB` is sound**: a table it accepts, the AIR accepts from `m0`. -/
theorem checkFromB_sound {M : List Cell} {m0 : Mach} {rows : List Row}
    (h : checkFromB M m0 rows = true) : AcceptsFrom M m0 rows.length (rowFn rows) := by
  cases rows with
  | nil => cases h
  | cons r0 rest =>
    unfold checkFromB at h
    simp only [Bool.and_eq_true, decide_eq_true_iff] at h
    obtain ⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩ := h
    refine ⟨by simp, h0, h1, h2, h3, chainB_trans h4, ?_⟩
    rw [← getLast_eq_getD]
    exact h5

/-- **`checkFromB` is complete**: a table the AIR accepts from `m0`, it accepts. -/
theorem checkFromB_complete {M : List Cell} {m0 : Mach} {rows : List Row}
    (h : AcceptsFrom M m0 rows.length (rowFn rows)) : checkFromB M m0 rows = true := by
  cases rows with
  | nil => exact absurd h.pos (Nat.lt_irrefl 0)
  | cons r0 rest =>
    unfold checkFromB
    simp only [Bool.and_eq_true, decide_eq_true_iff]
    refine ⟨⟨⟨⟨⟨h.heap0, h.hd0⟩, h.stk0⟩, h.ctr0⟩, chainB_of_trans h.trans⟩, ?_⟩
    rw [getLast_eq_getD]
    exact h.final

/-- **The array checker is the list checker.** -/
theorem checkFromA_eq (A : Array Cell) (m0 : Mach) (rows : List Row) :
    checkFromA A m0 rows = checkFromB A.toList m0 rows := by
  have hg : (fun a : Nat => A[a]?) = (fun a : Nat => A.toList[a]?) := by
    funext a; rw [Array.getElem?_toList]
  cases rows with
  | nil => rfl
  | cons r0 rest =>
    simp only [checkFromA, checkFromB, chainB_G, haltRow_G, hg]

/-- The array checker decides the AIR's constraints from `m0`. -/
theorem checkFromA_iff {A : Array Cell} {m0 : Mach} {rows : List Row} :
    checkFromA A m0 rows = true ↔ AcceptsFrom A.toList m0 rows.length (rowFn rows) := by
  rw [checkFromA_eq]
  exact ⟨checkFromB_sound, checkFromB_complete⟩

/-- **The checker for an open term**: from `oload t`. -/
def checkOA (A : Array Cell) (t : OTerm) (rows : List Row) : Bool :=
  checkFromA A (oload t) rows

theorem checkOA_iff {A : Array Cell} {t : OTerm} {rows : List Row} :
    checkOA A t rows = true ↔ AcceptsFrom A.toList (oload t) rows.length (rowFn rows) :=
  checkFromA_iff

/-- **A table `checkOA` accepts proves open head reduction**: its last row
    reads back as a reduct of `t`, and the machine has halted there. -/
theorem checkOA_open {A : Array Cell} {t : OTerm} {rows : List Row}
    (h : checkOA A t rows = true) :
    ∃ v, odecode (st A.toList (rowFn rows (rows.length - 1))) = some v ∧ OSteps t v ∧
      mstep (st A.toList (rowFn rows (rows.length - 1))) = none :=
  air_sound_open (checkOA_iff.1 h)

/-- **The atoms are generic**: for every closing substitution `σ`, the
    closed term `t.close σ` head-reduces to the table's reduct closed by `σ`. -/
theorem checkOA_close {A : Array Cell} {t : OTerm} {rows : List Row}
    (h : checkOA A t rows = true) :
    ∃ v, odecode (st A.toList (rowFn rows (rows.length - 1))) = some v ∧
      ∀ σ : Nat → Term, Steps (t.close σ) (v.close σ) := by
  obtain ⟨v, hv, hs, _⟩ := checkOA_open h
  exact ⟨v, hv, fun σ => hs.close σ⟩

end Air
