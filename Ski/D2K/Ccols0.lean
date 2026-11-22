import Ski.D2Base
import Ski.D2K.Chom3
/-! Generated.  Kernel check `colsRow`, rows 0..187. -/
namespace D2
theorem colsB_0 : colsB 0 47 = true := by decide +kernel
theorem colsB_47 : colsB 47 47 = true := by decide +kernel
theorem colsB_94 : colsB 94 47 = true := by decide +kernel
theorem colsB_141 : colsB 141 47 = true := by decide +kernel
theorem colsG_0 (a : Nat) (h1 : 0 ≤ a) (h2 : a < 188) : colsRow a = true := by
  if h0 : a < 47 then exact chunk_get colsB_0 (by omega) (by omega) else
  if h47 : a < 94 then exact chunk_get colsB_47 (by omega) (by omega) else
  if h94 : a < 141 then exact chunk_get colsB_94 (by omega) (by omega) else
  if h141 : a < 188 then exact chunk_get colsB_141 (by omega) (by omega) else
  omega
end D2
