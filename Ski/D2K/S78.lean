import Ski.D2Base
import Ski.D2K.S77
/-! Generated.  S-law of D: chunks 624..631 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_624 : slawChunk 624 = true := by decide +kernel
theorem slawChunk_625 : slawChunk 625 = true := by decide +kernel
theorem slawChunk_626 : slawChunk 626 = true := by decide +kernel
theorem slawChunk_627 : slawChunk 627 = true := by decide +kernel
theorem slawChunk_628 : slawChunk 628 = true := by decide +kernel
theorem slawChunk_629 : slawChunk 629 = true := by decide +kernel
theorem slawChunk_630 : slawChunk 630 = true := by decide +kernel
theorem slawChunk_631 : slawChunk 631 = true := by decide +kernel
theorem slawC_78 (k : Nat) (h1 : 624 ≤ k) (h2 : k < 632) : slawChunk k = true := by
  if e624 : k = 624 then subst e624; exact slawChunk_624 else
  if e625 : k = 625 then subst e625; exact slawChunk_625 else
  if e626 : k = 626 then subst e626; exact slawChunk_626 else
  if e627 : k = 627 then subst e627; exact slawChunk_627 else
  if e628 : k = 628 then subst e628; exact slawChunk_628 else
  if e629 : k = 629 then subst e629; exact slawChunk_629 else
  if e630 : k = 630 then subst e630; exact slawChunk_630 else
  if e631 : k = 631 then subst e631; exact slawChunk_631 else
  omega
end D2
