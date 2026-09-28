import Ski.Sudoku
import Ski.AirCheck
import Ski.AirOpen

open Term

/-!
# Checking a Sudoku table produced outside Lean

The Plonky3 prover in `bench/plonky3` proves a table started from the
statement machine of a Sudoku puzzle.  `sudokuCheck` checks, on the same
table, what `Sudoku.sudoku_sound` needs (soundly; completeness is not
proved), reading the inputs off the table's
own memory: input `n` is set when the cell at `n + 3` is `K`.

**The theorems.**
- `checkFromA_sound`: a table `checkFromA` accepts, over an array, meets
  the AIR's constraints from a machine state (`Air.AcceptsFrom`).
- `stmtMachineA_eq`: the statement machine built over an array, which is
  fast, is the statement machine.
- `sudokuCheck_sound`: a table `sudokuCheck` accepts carries a solution of
  the puzzle in its input cells.
-/

namespace Air

open Mach

/-- **The AIR's constraints from a machine state, decided** on a table. -/
def checkFromA (A : Array Cell) (m0 : Mach) : List Row → Bool
  | [] => false
  | r0 :: rest =>
    decide (A.toList.take r0.ctr = m0.heap) && decide (r0.hd = m0.hd) &&
      decide (r0.stk = m0.stk) && decide (r0.ctr = m0.heap.length) &&
      chainG (fun a => A[a]?) (r0 :: rest) &&
      haltRowG (fun a => A[a]?) ((r0 :: rest).getLast (List.cons_ne_nil _ _))

/-- **`checkFromA` is sound.** -/
theorem checkFromA_sound {A : Array Cell} {m0 : Mach} {rows : List Row}
    (h : checkFromA A m0 rows = true) : AcceptsFrom A.toList m0 rows.length (rowFn rows) := by
  cases rows with
  | nil => cases h
  | cons r0 rest =>
    unfold checkFromA at h
    dsimp only at h
    rw [getElem?_fun, ← chainB_G, ← haltRow_G] at h
    simp only [Bool.and_eq_true, decide_eq_true_iff] at h
    obtain ⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩ := h
    refine ⟨by simp, h0, h1, h2, h3, chainB_trans h4, ?_⟩
    rw [← getLast_eq_getD]
    exact h5

end Air

namespace Stmt

open Mach

/-- `pbuild` over an array. -/
def pbuildA (bound : Nat) : Array Cell → OTerm → Array Cell × Nat
  | h, .S => (h.push .S, h.size)
  | h, .K => (h.push .K, h.size)
  | h, .I => (h.push .I, h.size)
  | h, .var x => if x < bound then (h, slotPtr x) else (h.push (.atom x), h.size)
  | h, .app f a =>
    let (h1, pf) := pbuildA bound h f
    let (h2, pa) := pbuildA bound h1 a
    (h2.push (.app pf pa), h2.size)

theorem pbuildA_eq (bound : Nat) : ∀ (t : OTerm) (h : Array Cell),
    ((pbuildA bound h t).1.toList, (pbuildA bound h t).2) = pbuild bound h.toList t
  | .S, h => by simp [pbuildA, pbuild, alloc]
  | .K, h => by simp [pbuildA, pbuild, alloc]
  | .I, h => by simp [pbuildA, pbuild, alloc]
  | .var x, h => by
    unfold pbuildA pbuild
    by_cases hx : x < bound
    · simp [hx]
    · simp [hx, alloc]
  | .app f a, h => by
    have ef := pbuildA_eq bound f h
    have ea := pbuildA_eq bound a (pbuildA bound h f).1
    unfold pbuildA pbuild
    rw [← ef]
    dsimp only
    rw [← ea]
    simp [alloc]

/-- The statement machine, built over an array. -/
def stmtMachineA (ρ : Nat → Bool) (N : Nat) (e : BExpr) (acc rej : Nat) : Mach :=
  let (h, p) := pbuildA (N + 2) (slotHeap ρ N).toArray (probeTerm e acc rej)
  ⟨h.toList ++ [.nil], p, h.size⟩

theorem stmtMachineA_eq (ρ : Nat → Bool) (N : Nat) (e : BExpr) (acc rej : Nat) :
    stmtMachineA ρ N e acc rej = stmtMachine ρ N e acc rej := by
  have := pbuildA_eq (N + 2) (probeTerm e acc rej) (slotHeap ρ N).toArray
  rw [List.toList_toArray] at this
  unfold stmtMachineA stmtMachine
  rw [← this]
  simp

end Stmt

namespace Sudoku

open Stmt Mach

/-- The inputs a table's memory sets: input `n` when the cell at `n + 3` is
    `K`. -/
def rhoOf (A : Array Cell) (n : Nat) : Bool := A[n + 3]? == some .K

/-- The last row's head cell, read against the memory table. -/
def lastHead (A : Array Cell) (rows : List Air.Row) : Option Cell :=
  let r := Air.rowFn rows (rows.length - 1)
  Air.rdG (fun a => A[a]?) r.ctr r.hd

/-- **The Sudoku table check**: the markers are atoms outside the slots and
    distinct, the clues are well formed, the table satisfies the AIR from
    the statement machine for the inputs its memory sets, and its last row
    reads the accepting marker at the head. -/
def sudokuCheck (clues : List Clue) (acc rej : Nat) (A : Array Cell) (rows : List Air.Row) : Bool :=
  decide (731 ≤ acc) && decide (731 ≤ rej) && decide (acc ≠ rej) && cluesOKB clues &&
    Air.checkFromA A (stmtMachineA (rhoOf A) 729 (sudokuExpr clues) acc rej) rows &&
    lastHead A rows == some (.atom acc)

/-- **A table `sudokuCheck` accepts carries a solution** of the puzzle in its
    input cells. -/
theorem sudokuCheck_sound {clues : List Clue} {acc rej : Nat} {A : Array Cell} {rows : List Air.Row}
    (h : sudokuCheck clues acc rej A rows = true) : Solves clues (gridOf (rhoOf A)) := by
  unfold sudokuCheck at h
  simp only [Bool.and_eq_true, decide_eq_true_iff, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  rw [stmtMachineA_eq] at h5
  have hacc := Air.checkFromA_sound h5
  have hi : Air.rd A.toList (Air.rowFn rows (rows.length - 1)).ctr
      (Air.rowFn rows (rows.length - 1)).hd = some (.atom acc) := by
    rw [Air.rd_G, ← Air.getElem?_fun]
    exact h6
  exact sudoku_sound (cluesOK_of h4) h1 h2 h3 hacc hi

end Sudoku
