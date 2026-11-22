import Ski.D2Base
import Ski.D2K.Chom1
/-! Generated.  Kernel check `homRow`, rows 192..287. -/
namespace D2
theorem homB_192 : homB 192 12 = true := by decide +kernel
theorem homB_204 : homB 204 12 = true := by decide +kernel
theorem homB_216 : homB 216 12 = true := by decide +kernel
theorem homB_228 : homB 228 12 = true := by decide +kernel
theorem homB_240 : homB 240 12 = true := by decide +kernel
theorem homB_252 : homB 252 12 = true := by decide +kernel
theorem homB_264 : homB 264 12 = true := by decide +kernel
theorem homB_276 : homB 276 12 = true := by decide +kernel
theorem homG_2 (a : Nat) (h1 : 192 ≤ a) (h2 : a < 288) : homRow a = true := by
  if h192 : a < 204 then exact chunk_get homB_192 (by omega) (by omega) else
  if h204 : a < 216 then exact chunk_get homB_204 (by omega) (by omega) else
  if h216 : a < 228 then exact chunk_get homB_216 (by omega) (by omega) else
  if h228 : a < 240 then exact chunk_get homB_228 (by omega) (by omega) else
  if h240 : a < 252 then exact chunk_get homB_240 (by omega) (by omega) else
  if h252 : a < 264 then exact chunk_get homB_252 (by omega) (by omega) else
  if h264 : a < 276 then exact chunk_get homB_264 (by omega) (by omega) else
  if h276 : a < 288 then exact chunk_get homB_276 (by omega) (by omega) else
  omega
end D2
