import Ski.ZK.HideWire
import Ski.ZK.Honest
import Ski.Circuit.SudComplete

/-!
# One Sudoku run, for the composed PCS

An accepting run of the Sudoku statement gives its tables: `cpuTableW`,
`memTableC`, `witTableS`.  `sud_honest_zk` proves they are `Balanced`
and `Unblinded`, which the transcript theorem asks.  `sud_run_sats`
proves they meet `Sat`, which the composed PCS asks, for the same
tables.  `sud_run_wire` then gives, at every edge tuple, the blinded
tables' `Sat` and the view's terminals at 0, 1, 2.
-/

namespace Circuit

open B Air Stmt Mach Sudoku SudokuText

/-- **The run's tables meet `Sat`**: the CPU, memory and witness tables an
    accepting run of the Sudoku statement builds. -/
theorem sud_run_sats {puzzle : List Nat} (hc : CluesOK (cluesOf puzzle)) {ρ : Nat → Bool}
    {A : List Cell} {k : Nat} {row : Nat → Air.Row}
    (hA : AcceptsFrom A (stmtMachine ρ 729 (sudokuExpr (cluesOf puzzle)) ACC REJ) k row)
    (hacc : rd A (row (k - 1)).ctr (row (k - 1)).hd = some (.atom ACC))
    (hlen : A.length = 2 ^ 16) (hk : k ≤ 2 ^ 16) :
    let blank := stmtMachine (fun _ => false) 729 (sudokuExpr (cluesOf puzzle)) ACC REJ
    let C := cpuTableW A row k (2 ^ 16)
    let Pg := progTableS blank.heap
    let Wt := witTableS A
    let Mm := memTableC A (cpuAirS blank.hd blank.stk blank.heap.length ACC) (progAirS blank.heap) witAirS C Pg Wt
    Sat (cpuAirS blank.hd blank.stk blank.heap.length ACC) C ∧ Sat memAirC Mm ∧ Sat witAirS Wt := by
  intro blank C Pg Wt Mm
  have hb := bounded_sudoku hc
  obtain ⟨hhd, hstk, hlenm, _⟩ :=
    stmtMachine_public ρ (fun _ => false) 729 (sudokuExpr (cluesOf puzzle)) ACC REJ
  obtain ⟨m0, hm0⟩ : ∃ m, stmtMachine ρ 729 (sudokuExpr (cluesOf puzzle)) ACC REJ = m := ⟨_, rfl⟩
  rw [hm0] at hA hhd hstk hlenm
  have hk0 := hA.pos
  have hcpu : Sat (cpuAirS blank.hd blank.stk blank.heap.length ACC) C := by
    have := cpuS_sat hA hk (by decide) (by omega) (by decide) hacc
    have e0 : rowQ row k 0 = row 0 := by unfold rowQ; rw [if_pos hk0]
    rw [e0, hA.hd0, hA.stk0, hA.ctr0, hhd, hstk, hlenm] at this
    exact this
  exact ⟨hcpu, memC_sat A _ _ _ _ _ _ (by omega), (witS_sat A).1⟩

set_option maxRecDepth 100000 in
/-- **One run, for the composed PCS and the transcript**: the run's tables
    are `Balanced` and `Unblinded`, and at every edge tuple their blinded
    copies meet `Sat` and the view publishes their terminals at 0, 1, 2. -/
theorem sud_run_wire {puzzle : List Nat} (hc : CluesOK (cluesOf puzzle)) {ρ : Nat → Bool}
    {A : List Cell} {k : Nat} {row : Nat → Air.Row}
    (hA : AcceptsFrom A (stmtMachine ρ 729 (sudokuExpr (cluesOf puzzle)) ACC REJ) k row)
    (hacc : rd A (row (k - 1)).ctr (row (k - 1)).hd = some (.atom ACC))
    (hlen : A.length = 2 ^ 16) (hk : k ≤ 2 ^ 16) (pre : String → EF) (β : EF) (t : Nat → Tup) :
    let blank := stmtMachine (fun _ => false) 729 (sudokuExpr (cluesOf puzzle)) ACC REJ
    let C := cpuTableW A row k (2 ^ 16)
    let Pg := progTableS blank.heap
    let Wt := witTableS A
    let Mm := memTableC A (cpuAirS blank.hd blank.stk blank.heap.length ACC) (progAirS blank.heap) witAirS C Pg Wt
    Balanced (sudTables blank.hd blank.stk blank.heap.length blank.heap C Mm Pg Wt) ∧ Unblinded 1 C Mm Wt ∧
    Sat memAirC (Mm.setBlind 5 (t 0)) ∧
    Sat (cpuAirS blank.hd blank.stk blank.heap.length ACC) ((C.setBlind BLA (t 1)).setBlind BLB (t 0)) ∧
    Sat witAirS (Wt.setBlind 1 (t 1)) ∧
    (sudViewN pre β blank.hd blank.stk blank.heap.length C Mm Wt t).getD 0 EF.zero =
      terminal pre β memAirC (Mm.setBlind 5 (t 0)) ∧
    (sudViewN pre β blank.hd blank.stk blank.heap.length C Mm Wt t).getD 1 EF.zero =
      terminal pre β (cpuAirS blank.hd blank.stk blank.heap.length ACC) ((C.setBlind BLA (t 1)).setBlind BLB (t 0)) ∧
    (sudViewN pre β blank.hd blank.stk blank.heap.length C Mm Wt t).getD 2 EF.zero =
      terminal pre β witAirS (Wt.setBlind 1 (t 1)) := by
  intro blank C Pg Wt Mm
  obtain ⟨hbal, hun⟩ := sud_honest_zk hc hA hlen hk
  obtain ⟨sc, sm, sw⟩ := sud_run_sats hc hA hacc hlen hk
  obtain ⟨b1, b2, _, _, _, _, b7, b8, _, _⟩ := blind_ok blank.hd blank.stk blank.heap.length 0 0 0 0
  exact ⟨hbal, hun, sat_setBlind sm b7 _, sat_setBlind (sat_setBlind sc b1 _) b2 _, sat_setBlind sw b8 _,
    rfl, rfl, rfl⟩

end Circuit
