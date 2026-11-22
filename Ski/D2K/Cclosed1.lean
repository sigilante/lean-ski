import Ski.D2Base
import Ski.D2K.Cclosed0
/-! Generated.  Kernel check `closedRow`, rows 188..372. -/
namespace D2
theorem closedB_188 : closedB 188 47 = true := by decide +kernel
theorem closedB_235 : closedB 235 47 = true := by decide +kernel
theorem closedB_282 : closedB 282 47 = true := by decide +kernel
theorem closedB_329 : closedB 329 44 = true := by decide +kernel
theorem closedG_1 (a : Nat) (h1 : 188 ≤ a) (h2 : a < 373) : closedRow a = true := by
  if h188 : a < 235 then exact chunk_get closedB_188 (by omega) (by omega) else
  if h235 : a < 282 then exact chunk_get closedB_235 (by omega) (by omega) else
  if h282 : a < 329 then exact chunk_get closedB_282 (by omega) (by omega) else
  if h329 : a < 373 then exact chunk_get closedB_329 (by omega) (by omega) else
  omega
theorem closedRow_all (a : Nat) (h : a < 373) : closedRow a = true := by
  if h0 : a < 188 then exact closedG_0 a (by omega) h0 else
  if h1 : a < 373 then exact closedG_1 a (by omega) h1 else
  omega
end D2
