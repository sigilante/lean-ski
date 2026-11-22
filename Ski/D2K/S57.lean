import Ski.D2Base
import Ski.D2K.S56
/-! Generated.  S-law of D: chunks 456..463 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_456 : slawChunk 456 = true := by decide +kernel
theorem slawChunk_457 : slawChunk 457 = true := by decide +kernel
theorem slawChunk_458 : slawChunk 458 = true := by decide +kernel
theorem slawChunk_459 : slawChunk 459 = true := by decide +kernel
theorem slawChunk_460 : slawChunk 460 = true := by decide +kernel
theorem slawChunk_461 : slawChunk 461 = true := by decide +kernel
theorem slawChunk_462 : slawChunk 462 = true := by decide +kernel
theorem slawChunk_463 : slawChunk 463 = true := by decide +kernel
theorem slawC_57 (k : Nat) (h1 : 456 ≤ k) (h2 : k < 464) : slawChunk k = true := by
  if e456 : k = 456 then subst e456; exact slawChunk_456 else
  if e457 : k = 457 then subst e457; exact slawChunk_457 else
  if e458 : k = 458 then subst e458; exact slawChunk_458 else
  if e459 : k = 459 then subst e459; exact slawChunk_459 else
  if e460 : k = 460 then subst e460; exact slawChunk_460 else
  if e461 : k = 461 then subst e461; exact slawChunk_461 else
  if e462 : k = 462 then subst e462; exact slawChunk_462 else
  if e463 : k = 463 then subst e463; exact slawChunk_463 else
  omega
end D2
