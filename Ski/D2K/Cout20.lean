import Ski.D2Base
import Ski.D2K.Cclosed1
/-! Generated.  Kernel check `out2Row`, rows 0..187. -/
namespace D2
theorem out2B_0 : out2B 0 47 = true := by decide +kernel
theorem out2B_47 : out2B 47 47 = true := by decide +kernel
theorem out2B_94 : out2B 94 47 = true := by decide +kernel
theorem out2B_141 : out2B 141 47 = true := by decide +kernel
theorem out2G_0 (a : Nat) (h1 : 0 ≤ a) (h2 : a < 188) : out2Row a = true := by
  if h0 : a < 47 then exact chunk_get out2B_0 (by omega) (by omega) else
  if h47 : a < 94 then exact chunk_get out2B_47 (by omega) (by omega) else
  if h94 : a < 141 then exact chunk_get out2B_94 (by omega) (by omega) else
  if h141 : a < 188 then exact chunk_get out2B_141 (by omega) (by omega) else
  omega
end D2
