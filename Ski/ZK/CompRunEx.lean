import Ski.ZK.CompRun
import Ski.ComposeExamples

/-!
# The budget, checked for the released `∨`

The released `∨` statement (`negOr`, a region of 64 cells, heights `2^11`
rows and memory cells) with its first side's witness (`witL`): the region
`regionOf'` builds holds it, and the composed machine's run halts in the
last segment at step 263 on 712 cells, as `ski-air composed-prove` reports
for this witness (264 rows, 712 memory cells), so the budget holds
(`or_budget`, by kernel evaluation) and the witness has an accepted run in
`CRel` (`or_run`): `CBudget` is met by a released statement.
-/

namespace Circuit

open Compose CompM ComposeEx WitEx Mach

/-- The region `regionOf'` builds of the `∨`'s witness. -/
def orRegion : List Cell := (ComposedText.regionOf' (BT.nleaves (clear negOr)) 64 witL).getD []

theorem or_region : ComposedText.regionOf' (BT.nleaves (clear negOr)) 64 witL = some orRegion := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
/-- **The budget holds for the released `∨`**: its run halts in the last
    segment at step 263, on 712 cells, within `2^11`. -/
theorem or_budget : CBudget ⟨clear negOr, stmtOf negOr, 64, 11, 11⟩ (leafAt bitsL) orRegion :=
  ⟨263, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- **The released `∨`'s witness has an accepted run** in `CRel`. -/
theorem or_run : ∃ run : CRun', CRel ⟨clear negOr, stmtOf negOr, 64, 11, 11⟩ run ∧
    run.ρ = leafAt bitsL ∧ run.region = orRegion :=
  accepted_run negOr 64 11 11 (by decide) (by decide) (by decide) bitsL witL negOr_accepts orRegion
    or_region or_budget

end Circuit
