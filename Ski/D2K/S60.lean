import Ski.D2Base
import Ski.D2K.S59
/-! Generated.  S-law of D: chunks 480..487 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_480 : slawChunk 480 = true := by decide +kernel
theorem slawChunk_481 : slawChunk 481 = true := by decide +kernel
theorem slawChunk_482 : slawChunk 482 = true := by decide +kernel
theorem slawChunk_483 : slawChunk 483 = true := by decide +kernel
theorem slawChunk_484 : slawChunk 484 = true := by decide +kernel
theorem slawChunk_485 : slawChunk 485 = true := by decide +kernel
theorem slawChunk_486 : slawChunk 486 = true := by decide +kernel
theorem slawChunk_487 : slawChunk 487 = true := by decide +kernel
theorem slawC_60 (k : Nat) (h1 : 480 ≤ k) (h2 : k < 488) : slawChunk k = true := by
  if e480 : k = 480 then subst e480; exact slawChunk_480 else
  if e481 : k = 481 then subst e481; exact slawChunk_481 else
  if e482 : k = 482 then subst e482; exact slawChunk_482 else
  if e483 : k = 483 then subst e483; exact slawChunk_483 else
  if e484 : k = 484 then subst e484; exact slawChunk_484 else
  if e485 : k = 485 then subst e485; exact slawChunk_485 else
  if e486 : k = 486 then subst e486; exact slawChunk_486 else
  if e487 : k = 487 then subst e487; exact slawChunk_487 else
  omega
end D2
