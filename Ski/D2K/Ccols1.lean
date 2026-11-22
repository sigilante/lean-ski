import Ski.D2Base
import Ski.D2K.Ccols0
/-! Generated.  Kernel check `colsRow`, rows 188..372. -/
namespace D2
theorem colsB_188 : colsB 188 47 = true := by decide +kernel
theorem colsB_235 : colsB 235 47 = true := by decide +kernel
theorem colsB_282 : colsB 282 47 = true := by decide +kernel
theorem colsB_329 : colsB 329 44 = true := by decide +kernel
theorem colsG_1 (a : Nat) (h1 : 188 ≤ a) (h2 : a < 373) : colsRow a = true := by
  if h188 : a < 235 then exact chunk_get colsB_188 (by omega) (by omega) else
  if h235 : a < 282 then exact chunk_get colsB_235 (by omega) (by omega) else
  if h282 : a < 329 then exact chunk_get colsB_282 (by omega) (by omega) else
  if h329 : a < 373 then exact chunk_get colsB_329 (by omega) (by omega) else
  omega
theorem colsRow_all (a : Nat) (h : a < 373) : colsRow a = true := by
  if h0 : a < 188 then exact colsG_0 a (by omega) h0 else
  if h1 : a < 373 then exact colsG_1 a (by omega) h1 else
  omega
end D2
