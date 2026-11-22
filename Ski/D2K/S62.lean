import Ski.D2Base
import Ski.D2K.S61
/-! Generated.  S-law of D: chunks 496..503 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_496 : slawChunk 496 = true := by decide +kernel
theorem slawChunk_497 : slawChunk 497 = true := by decide +kernel
theorem slawChunk_498 : slawChunk 498 = true := by decide +kernel
theorem slawChunk_499 : slawChunk 499 = true := by decide +kernel
theorem slawChunk_500 : slawChunk 500 = true := by decide +kernel
theorem slawChunk_501 : slawChunk 501 = true := by decide +kernel
theorem slawChunk_502 : slawChunk 502 = true := by decide +kernel
theorem slawChunk_503 : slawChunk 503 = true := by decide +kernel
theorem slawC_62 (k : Nat) (h1 : 496 ≤ k) (h2 : k < 504) : slawChunk k = true := by
  if e496 : k = 496 then subst e496; exact slawChunk_496 else
  if e497 : k = 497 then subst e497; exact slawChunk_497 else
  if e498 : k = 498 then subst e498; exact slawChunk_498 else
  if e499 : k = 499 then subst e499; exact slawChunk_499 else
  if e500 : k = 500 then subst e500; exact slawChunk_500 else
  if e501 : k = 501 then subst e501; exact slawChunk_501 else
  if e502 : k = 502 then subst e502; exact slawChunk_502 else
  if e503 : k = 503 then subst e503; exact slawChunk_503 else
  omega
end D2
