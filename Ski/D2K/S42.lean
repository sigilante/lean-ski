import Ski.D2Base
import Ski.D2K.S41
/-! Generated.  S-law of D: chunks 336..343 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_336 : slawChunk 336 = true := by decide +kernel
theorem slawChunk_337 : slawChunk 337 = true := by decide +kernel
theorem slawChunk_338 : slawChunk 338 = true := by decide +kernel
theorem slawChunk_339 : slawChunk 339 = true := by decide +kernel
theorem slawChunk_340 : slawChunk 340 = true := by decide +kernel
theorem slawChunk_341 : slawChunk 341 = true := by decide +kernel
theorem slawChunk_342 : slawChunk 342 = true := by decide +kernel
theorem slawChunk_343 : slawChunk 343 = true := by decide +kernel
theorem slawC_42 (k : Nat) (h1 : 336 ≤ k) (h2 : k < 344) : slawChunk k = true := by
  if e336 : k = 336 then subst e336; exact slawChunk_336 else
  if e337 : k = 337 then subst e337; exact slawChunk_337 else
  if e338 : k = 338 then subst e338; exact slawChunk_338 else
  if e339 : k = 339 then subst e339; exact slawChunk_339 else
  if e340 : k = 340 then subst e340; exact slawChunk_340 else
  if e341 : k = 341 then subst e341; exact slawChunk_341 else
  if e342 : k = 342 then subst e342; exact slawChunk_342 else
  if e343 : k = 343 then subst e343; exact slawChunk_343 else
  omega
end D2
