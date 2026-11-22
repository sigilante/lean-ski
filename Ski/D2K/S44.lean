import Ski.D2Base
import Ski.D2K.S43
/-! Generated.  S-law of D: chunks 352..359 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_352 : slawChunk 352 = true := by decide +kernel
theorem slawChunk_353 : slawChunk 353 = true := by decide +kernel
theorem slawChunk_354 : slawChunk 354 = true := by decide +kernel
theorem slawChunk_355 : slawChunk 355 = true := by decide +kernel
theorem slawChunk_356 : slawChunk 356 = true := by decide +kernel
theorem slawChunk_357 : slawChunk 357 = true := by decide +kernel
theorem slawChunk_358 : slawChunk 358 = true := by decide +kernel
theorem slawChunk_359 : slawChunk 359 = true := by decide +kernel
theorem slawC_44 (k : Nat) (h1 : 352 ≤ k) (h2 : k < 360) : slawChunk k = true := by
  if e352 : k = 352 then subst e352; exact slawChunk_352 else
  if e353 : k = 353 then subst e353; exact slawChunk_353 else
  if e354 : k = 354 then subst e354; exact slawChunk_354 else
  if e355 : k = 355 then subst e355; exact slawChunk_355 else
  if e356 : k = 356 then subst e356; exact slawChunk_356 else
  if e357 : k = 357 then subst e357; exact slawChunk_357 else
  if e358 : k = 358 then subst e358; exact slawChunk_358 else
  if e359 : k = 359 then subst e359; exact slawChunk_359 else
  omega
end D2
