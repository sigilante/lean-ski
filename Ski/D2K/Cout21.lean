import Ski.D2Base
import Ski.D2K.Cout20
/-! Generated.  Kernel check `out2Row`, rows 188..372. -/
namespace D2
theorem out2B_188 : out2B 188 47 = true := by decide +kernel
theorem out2B_235 : out2B 235 47 = true := by decide +kernel
theorem out2B_282 : out2B 282 47 = true := by decide +kernel
theorem out2B_329 : out2B 329 44 = true := by decide +kernel
theorem out2G_1 (a : Nat) (h1 : 188 ≤ a) (h2 : a < 373) : out2Row a = true := by
  if h188 : a < 235 then exact chunk_get out2B_188 (by omega) (by omega) else
  if h235 : a < 282 then exact chunk_get out2B_235 (by omega) (by omega) else
  if h282 : a < 329 then exact chunk_get out2B_282 (by omega) (by omega) else
  if h329 : a < 373 then exact chunk_get out2B_329 (by omega) (by omega) else
  omega
theorem out2Row_all (a : Nat) (h : a < 373) : out2Row a = true := by
  if h0 : a < 188 then exact out2G_0 a (by omega) h0 else
  if h1 : a < 373 then exact out2G_1 a (by omega) h1 else
  omega
end D2
