import Ski.D2Base
import Ski.D2K.Chom2
/-! Generated.  Kernel check `homRow`, rows 288..372. -/
namespace D2
theorem homB_288 : homB 288 12 = true := by decide +kernel
theorem homB_300 : homB 300 12 = true := by decide +kernel
theorem homB_312 : homB 312 12 = true := by decide +kernel
theorem homB_324 : homB 324 12 = true := by decide +kernel
theorem homB_336 : homB 336 12 = true := by decide +kernel
theorem homB_348 : homB 348 12 = true := by decide +kernel
theorem homB_360 : homB 360 12 = true := by decide +kernel
theorem homB_372 : homB 372 1 = true := by decide +kernel
theorem homG_3 (a : Nat) (h1 : 288 ≤ a) (h2 : a < 373) : homRow a = true := by
  if h288 : a < 300 then exact chunk_get homB_288 (by omega) (by omega) else
  if h300 : a < 312 then exact chunk_get homB_300 (by omega) (by omega) else
  if h312 : a < 324 then exact chunk_get homB_312 (by omega) (by omega) else
  if h324 : a < 336 then exact chunk_get homB_324 (by omega) (by omega) else
  if h336 : a < 348 then exact chunk_get homB_336 (by omega) (by omega) else
  if h348 : a < 360 then exact chunk_get homB_348 (by omega) (by omega) else
  if h360 : a < 372 then exact chunk_get homB_360 (by omega) (by omega) else
  if h372 : a < 373 then exact chunk_get homB_372 (by omega) (by omega) else
  omega
theorem homRow_all (a : Nat) (h : a < 373) : homRow a = true := by
  if h0 : a < 96 then exact homG_0 a (by omega) h0 else
  if h1 : a < 192 then exact homG_1 a (by omega) h1 else
  if h2 : a < 288 then exact homG_2 a (by omega) h2 else
  if h3 : a < 373 then exact homG_3 a (by omega) h3 else
  omega
end D2
