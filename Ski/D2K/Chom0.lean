import Ski.D2Base
import Ski.D2K.Cout21
/-! Generated.  Kernel check `homRow`, rows 0..95. -/
namespace D2
theorem homB_0 : homB 0 12 = true := by decide +kernel
theorem homB_12 : homB 12 12 = true := by decide +kernel
theorem homB_24 : homB 24 12 = true := by decide +kernel
theorem homB_36 : homB 36 12 = true := by decide +kernel
theorem homB_48 : homB 48 12 = true := by decide +kernel
theorem homB_60 : homB 60 12 = true := by decide +kernel
theorem homB_72 : homB 72 12 = true := by decide +kernel
theorem homB_84 : homB 84 12 = true := by decide +kernel
theorem homG_0 (a : Nat) (h1 : 0 ≤ a) (h2 : a < 96) : homRow a = true := by
  if h0 : a < 12 then exact chunk_get homB_0 (by omega) (by omega) else
  if h12 : a < 24 then exact chunk_get homB_12 (by omega) (by omega) else
  if h24 : a < 36 then exact chunk_get homB_24 (by omega) (by omega) else
  if h36 : a < 48 then exact chunk_get homB_36 (by omega) (by omega) else
  if h48 : a < 60 then exact chunk_get homB_48 (by omega) (by omega) else
  if h60 : a < 72 then exact chunk_get homB_60 (by omega) (by omega) else
  if h72 : a < 84 then exact chunk_get homB_72 (by omega) (by omega) else
  if h84 : a < 96 then exact chunk_get homB_84 (by omega) (by omega) else
  omega
end D2
