import Ski.D2Base
import Ski.D2K.S72
/-! Generated.  S-law of D: chunks 584..591 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_584 : slawChunk 584 = true := by decide +kernel
theorem slawChunk_585 : slawChunk 585 = true := by decide +kernel
theorem slawChunk_586 : slawChunk 586 = true := by decide +kernel
theorem slawChunk_587 : slawChunk 587 = true := by decide +kernel
theorem slawChunk_588 : slawChunk 588 = true := by decide +kernel
theorem slawChunk_589 : slawChunk 589 = true := by decide +kernel
theorem slawChunk_590 : slawChunk 590 = true := by decide +kernel
theorem slawChunk_591 : slawChunk 591 = true := by decide +kernel
theorem slawC_73 (k : Nat) (h1 : 584 ≤ k) (h2 : k < 592) : slawChunk k = true := by
  if e584 : k = 584 then subst e584; exact slawChunk_584 else
  if e585 : k = 585 then subst e585; exact slawChunk_585 else
  if e586 : k = 586 then subst e586; exact slawChunk_586 else
  if e587 : k = 587 then subst e587; exact slawChunk_587 else
  if e588 : k = 588 then subst e588; exact slawChunk_588 else
  if e589 : k = 589 then subst e589; exact slawChunk_589 else
  if e590 : k = 590 then subst e590; exact slawChunk_590 else
  if e591 : k = 591 then subst e591; exact slawChunk_591 else
  omega
end D2
