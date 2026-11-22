import Ski.D2Base
import Ski.D2K.S37
/-! Generated.  S-law of D: chunks 304..311 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_304 : slawChunk 304 = true := by decide +kernel
theorem slawChunk_305 : slawChunk 305 = true := by decide +kernel
theorem slawChunk_306 : slawChunk 306 = true := by decide +kernel
theorem slawChunk_307 : slawChunk 307 = true := by decide +kernel
theorem slawChunk_308 : slawChunk 308 = true := by decide +kernel
theorem slawChunk_309 : slawChunk 309 = true := by decide +kernel
theorem slawChunk_310 : slawChunk 310 = true := by decide +kernel
theorem slawChunk_311 : slawChunk 311 = true := by decide +kernel
theorem slawC_38 (k : Nat) (h1 : 304 ≤ k) (h2 : k < 312) : slawChunk k = true := by
  if e304 : k = 304 then subst e304; exact slawChunk_304 else
  if e305 : k = 305 then subst e305; exact slawChunk_305 else
  if e306 : k = 306 then subst e306; exact slawChunk_306 else
  if e307 : k = 307 then subst e307; exact slawChunk_307 else
  if e308 : k = 308 then subst e308; exact slawChunk_308 else
  if e309 : k = 309 then subst e309; exact slawChunk_309 else
  if e310 : k = 310 then subst e310; exact slawChunk_310 else
  if e311 : k = 311 then subst e311; exact slawChunk_311 else
  omega
end D2
