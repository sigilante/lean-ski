import Ski.D2Base
import Ski.D2K.S58
/-! Generated.  S-law of D: chunks 472..479 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_472 : slawChunk 472 = true := by decide +kernel
theorem slawChunk_473 : slawChunk 473 = true := by decide +kernel
theorem slawChunk_474 : slawChunk 474 = true := by decide +kernel
theorem slawChunk_475 : slawChunk 475 = true := by decide +kernel
theorem slawChunk_476 : slawChunk 476 = true := by decide +kernel
theorem slawChunk_477 : slawChunk 477 = true := by decide +kernel
theorem slawChunk_478 : slawChunk 478 = true := by decide +kernel
theorem slawChunk_479 : slawChunk 479 = true := by decide +kernel
theorem slawC_59 (k : Nat) (h1 : 472 ≤ k) (h2 : k < 480) : slawChunk k = true := by
  if e472 : k = 472 then subst e472; exact slawChunk_472 else
  if e473 : k = 473 then subst e473; exact slawChunk_473 else
  if e474 : k = 474 then subst e474; exact slawChunk_474 else
  if e475 : k = 475 then subst e475; exact slawChunk_475 else
  if e476 : k = 476 then subst e476; exact slawChunk_476 else
  if e477 : k = 477 then subst e477; exact slawChunk_477 else
  if e478 : k = 478 then subst e478; exact slawChunk_478 else
  if e479 : k = 479 then subst e479; exact slawChunk_479 else
  omega
end D2
