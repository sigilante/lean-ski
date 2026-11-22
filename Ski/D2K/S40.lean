import Ski.D2Base
import Ski.D2K.S39
/-! Generated.  S-law of D: chunks 320..327 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_320 : slawChunk 320 = true := by decide +kernel
theorem slawChunk_321 : slawChunk 321 = true := by decide +kernel
theorem slawChunk_322 : slawChunk 322 = true := by decide +kernel
theorem slawChunk_323 : slawChunk 323 = true := by decide +kernel
theorem slawChunk_324 : slawChunk 324 = true := by decide +kernel
theorem slawChunk_325 : slawChunk 325 = true := by decide +kernel
theorem slawChunk_326 : slawChunk 326 = true := by decide +kernel
theorem slawChunk_327 : slawChunk 327 = true := by decide +kernel
theorem slawC_40 (k : Nat) (h1 : 320 ≤ k) (h2 : k < 328) : slawChunk k = true := by
  if e320 : k = 320 then subst e320; exact slawChunk_320 else
  if e321 : k = 321 then subst e321; exact slawChunk_321 else
  if e322 : k = 322 then subst e322; exact slawChunk_322 else
  if e323 : k = 323 then subst e323; exact slawChunk_323 else
  if e324 : k = 324 then subst e324; exact slawChunk_324 else
  if e325 : k = 325 then subst e325; exact slawChunk_325 else
  if e326 : k = 326 then subst e326; exact slawChunk_326 else
  if e327 : k = 327 then subst e327; exact slawChunk_327 else
  omega
end D2
