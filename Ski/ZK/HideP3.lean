import Ski.ZK.LogUpBase
import Ski.Circuit.CompStep
import Ski.Circuit.SudSound
import Ski.Circuit.WitSound

/-!
# The hiding circuits' AIRs meet the composed PCS's checks

`tabsHonest_corpus` and `pcsCloseN_fri_corpus` ask one fact of an AIR,
`AirP3`: its constraints guarded, in its window, of Plonky3 degree at
most 2 with at most one transition factor, and its interactions'
elements and multiplicities in its columns, of degree at most 1 and 2.
The kernel checks it for every AIR of the Sudoku, hidden-term and
composed circuits, at every parameter: the parameters enter only as
constants, which none of these checks read (`sud_P3`, `wit_P3`,
`comp_P3`).
-/

namespace Circuit

set_option maxRecDepth 100000 in
/-- **The Sudoku circuit's AIRs.** -/
theorem sud_P3 (hd0 stk0 ctr0 : Nat) (heap : List Cell) (C Mm Pg Wt : Table) :
    ∀ p ∈ sudTables hd0 stk0 ctr0 heap C Mm Pg Wt, AirP3 p.1 = true := by
  intro p hp
  simp only [sudTables, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl <;> rfl

set_option maxRecDepth 100000 in
/-- **The hidden-term circuit's AIRs.** -/
theorem wit_P3 (hd0 stk0 ctr0 : Nat) (heap : List Cell) (W : Nat) (C Mm Pg Wt : Table) :
    ∀ p ∈ witTables hd0 stk0 ctr0 heap W C Mm Pg Wt, AirP3 p.1 = true := by
  intro p hp
  simp only [witTables, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl <;> rfl

set_option maxRecDepth 100000 in
/-- **The composed circuit's AIRs.** -/
theorem comp_P3 (hd0 stk0 ctr0 n nilA : Nat) (heap : List Cell) (N W : Nat) (roots : List Nat)
    (C Mm Pg Wt Sg : Table) :
    ∀ p ∈ compTables hd0 stk0 ctr0 n nilA heap N W roots C Mm Pg Wt Sg, AirP3 p.1 = true := by
  intro p hp
  simp only [compTables, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl <;> rfl

end Circuit
