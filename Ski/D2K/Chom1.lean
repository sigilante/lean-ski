import Ski.D2Base
import Ski.D2K.Chom0
/-! Generated.  Kernel check `homRow`, rows 96..191. -/
namespace D2
theorem homB_96 : homB 96 12 = true := by decide +kernel
theorem homB_108 : homB 108 12 = true := by decide +kernel
theorem homB_120 : homB 120 12 = true := by decide +kernel
theorem homB_132 : homB 132 12 = true := by decide +kernel
theorem homB_144 : homB 144 12 = true := by decide +kernel
theorem homB_156 : homB 156 12 = true := by decide +kernel
theorem homB_168 : homB 168 12 = true := by decide +kernel
theorem homB_180 : homB 180 12 = true := by decide +kernel
theorem homG_1 (a : Nat) (h1 : 96 ≤ a) (h2 : a < 192) : homRow a = true := by
  if h96 : a < 108 then exact chunk_get homB_96 (by omega) (by omega) else
  if h108 : a < 120 then exact chunk_get homB_108 (by omega) (by omega) else
  if h120 : a < 132 then exact chunk_get homB_120 (by omega) (by omega) else
  if h132 : a < 144 then exact chunk_get homB_132 (by omega) (by omega) else
  if h144 : a < 156 then exact chunk_get homB_144 (by omega) (by omega) else
  if h156 : a < 168 then exact chunk_get homB_156 (by omega) (by omega) else
  if h168 : a < 180 then exact chunk_get homB_168 (by omega) (by omega) else
  if h180 : a < 192 then exact chunk_get homB_180 (by omega) (by omega) else
  omega
end D2
