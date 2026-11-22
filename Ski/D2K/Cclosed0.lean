import Ski.D2Base
/-! Generated.  Kernel check `closedRow`, rows 0..187. -/
namespace D2
theorem closedB_0 : closedB 0 47 = true := by decide +kernel
theorem closedB_47 : closedB 47 47 = true := by decide +kernel
theorem closedB_94 : closedB 94 47 = true := by decide +kernel
theorem closedB_141 : closedB 141 47 = true := by decide +kernel
theorem closedG_0 (a : Nat) (h1 : 0 ≤ a) (h2 : a < 188) : closedRow a = true := by
  if h0 : a < 47 then exact chunk_get closedB_0 (by omega) (by omega) else
  if h47 : a < 94 then exact chunk_get closedB_47 (by omega) (by omega) else
  if h94 : a < 141 then exact chunk_get closedB_94 (by omega) (by omega) else
  if h141 : a < 188 then exact chunk_get closedB_141 (by omega) (by omega) else
  omega
end D2
