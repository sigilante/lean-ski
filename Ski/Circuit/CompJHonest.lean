import Ski.Circuit.CompJFinal
import Ski.Circuit.CompComplete
import Ski.Circuit.ProbeComplete

/-!
# The honest tables of the composed circuit with jets

The tables a prover builds from a run of `CompM.AcceptsCJ` (as
`bench/plonky3/src/compj.rs`'s `traces` does).  The run is a jetted run
(`JRun`) whose restart rows another part of the circuit accounts for
(`CRun.J`, skipping `isRestart`): the jet circuit's honest rows serve
every other row, its POP and INSTW rows every instantiation.

- **CPU** (`cpuColCJ`): the jet table's columns, the kind selectors clear
  on a restart row; the restart selector; the segment counter; the next
  root; the blinding flags clear.
- **POP**, **INSTW**: the jet run's.  **ROOTS**, **HDR**, **TMPL**: each
  tuple's use count on its first row, the rows padded to `2^8`.
- **Memory**: the cells, each with the count of messages sent to it by
  the CPU, program, witness, POP and INSTW tables (`memTable5`).
-/

namespace Circuit

open B Air JetTable Compose CompM Mach

/-- A run of the composed machine with jets: memory, the jet table, the
    segment roots and ends, and the rows. -/
structure CRun where
  A : List Cell
  jroots : List (Nat × Nat)
  jets : List Air.Jet
  segRoots : List Nat
  e : Nat → Nat
  n : Nat
  row : Nat → Air.Row

namespace CRun

variable (R : CRun)

/-- **The jetted run**: every row up to the last segment's end, the restart
    rows skipped. -/
def J : JRun := ⟨R.A, R.jroots, R.jets, R.e (R.n - 1) + 1, R.row, isRestart R.e R.n⟩

/-- **The honest CPU row**: the jet table's, the restart's. -/
def cpuColCJ (i col : Nat) : F :=
  if col < CPU_WIDTH + JET_WIDTH then
    (if SEL ≤ col ∧ col < SEL + NKINDS ∧ isRestart R.e R.n i = true then 0 else R.J.cpuCol i col)
  else if col = RSJ then (if isRestart R.e R.n i then 1 else 0)
  else if col = CNTJ then ofN (cntS (rsI R.e R.n) i)
  else if col = ROOTJ then ofN (R.segRoots.getD (cntS (rsI R.e R.n) i + 1) 0)
  else 0

def cpuTableCJ (K : Nat) : Table := ⟨K, fun i col => R.cpuColCJ i col, fun _ _ => 0⟩

end CRun

-- ---------------------------------------------------------------------------
-- The run's facts
-- ---------------------------------------------------------------------------

section

variable {A : List Cell} {m0 : Mach} {jroots : List (Nat × Nat)} {jets : List Air.Jet} {segRoots : List Nat}
  {nilA n : Nat} {e : Nat → Nat} {row : Nat → Air.Row}
  (hA : AcceptsCJ A m0 jroots jets segRoots nilA n e row) (hroots : RootsOK m0.heap jroots jets)
include hA

omit hA in
theorem _root_.CompM.AcceptsCJ.notEnd {i : Nat} (hr : isRestart e n i = false) : ∀ j, j + 1 < n → i ≠ e j :=
  fun j hj h' => by rw [isRestart_iff.2 ⟨j, hj, h'.symm⟩] at hr; cases hr

theorem _root_.CompM.AcceptsCJ.restart_lt {i : Nat} (hr : isRestart e n i = true) : i < e (n - 1) := by
  obtain ⟨j, hj, rfl⟩ := isRestart_iff.1 hr
  exact emono_lt hA.emono (by omega) (by have := hA.npos; omega)

include hroots in
/-- **Every row's counter is within the memory.** -/
theorem _root_.CompM.AcceptsCJ.ctr_le : ∀ i, i ≤ e (n - 1) → (row i).ctr ≤ A.length := by
  intro i hi
  have hn := hA.npos
  obtain ⟨j, hj, h1, h2⟩ := seg_cover (e := e) (n := n) (n - 1) (by omega) i hi
  obtain ⟨hc, hm, _, _, _⟩ := hA.runs hroots j (by omega)
  have hc0 : (row 0).ctr ≤ (row (segStart e j)).ctr := by rw [hA.ctr0]; exact hm
  exact (hA.within hroots (by omega) hc hc0 i h1 h2).1

include hroots in
/-- **The jetted run is one**: every row but a restart and the last steps,
    instantiates or repeats a halt; the last halts. -/
theorem _root_.CompM.AcceptsCJ.jok : JOK ⟨A, jroots, jets, e (n - 1) + 1, row, isRestart e n⟩ := by
  have hn := hA.npos
  refine ⟨Nat.succ_pos _, fun i hi hsk => ?_, ?_, fun i hi => hA.ctr_le hroots i (by simp at hi; omega)⟩
  · exact hA.trans i (by show i < e (n - 1); simp at hi; omega) (AcceptsCJ.notEnd hsk)
  · show haltRow A (row (e (n - 1) + 1 - 1)) = true
    rw [Nat.add_sub_cancel]
    exact halt_K (hA.ends (n - 1) (by omega)).1 (hA.ends (n - 1) (by omega)).2

end

end Circuit
