import Ski.D2Base
import Ski.D2K.S60
/-! Generated.  S-law of D: chunks 488..495 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_488 : slawChunk 488 = true := by decide +kernel
theorem slawChunk_489 : slawChunk 489 = true := by decide +kernel
theorem slawChunk_490 : slawChunk 490 = true := by decide +kernel
theorem slawChunk_491 : slawChunk 491 = true := by decide +kernel
theorem slawChunk_492 : slawChunk 492 = true := by decide +kernel
theorem slawChunk_493 : slawChunk 493 = true := by decide +kernel
theorem slawChunk_494 : slawChunk 494 = true := by decide +kernel
theorem slawChunk_495 : slawChunk 495 = true := by decide +kernel
theorem slawC_61 (k : Nat) (h1 : 488 ≤ k) (h2 : k < 496) : slawChunk k = true := by
  if e488 : k = 488 then subst e488; exact slawChunk_488 else
  if e489 : k = 489 then subst e489; exact slawChunk_489 else
  if e490 : k = 490 then subst e490; exact slawChunk_490 else
  if e491 : k = 491 then subst e491; exact slawChunk_491 else
  if e492 : k = 492 then subst e492; exact slawChunk_492 else
  if e493 : k = 493 then subst e493; exact slawChunk_493 else
  if e494 : k = 494 then subst e494; exact slawChunk_494 else
  if e495 : k = 495 then subst e495; exact slawChunk_495 else
  omega
end D2
