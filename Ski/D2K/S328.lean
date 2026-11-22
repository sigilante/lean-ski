import Ski.D2Base
import Ski.D2K.S327
/-! Generated.  S-law of D: chunks 2624..2631 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_2624 : slawChunk 2624 = true := by decide +kernel
theorem slawChunk_2625 : slawChunk 2625 = true := by decide +kernel
theorem slawChunk_2626 : slawChunk 2626 = true := by decide +kernel
theorem slawChunk_2627 : slawChunk 2627 = true := by decide +kernel
theorem slawChunk_2628 : slawChunk 2628 = true := by decide +kernel
theorem slawChunk_2629 : slawChunk 2629 = true := by decide +kernel
theorem slawChunk_2630 : slawChunk 2630 = true := by decide +kernel
theorem slawChunk_2631 : slawChunk 2631 = true := by decide +kernel
theorem slawC_328 (k : Nat) (h1 : 2624 ≤ k) (h2 : k < 2632) : slawChunk k = true := by
  if e2624 : k = 2624 then subst e2624; exact slawChunk_2624 else
  if e2625 : k = 2625 then subst e2625; exact slawChunk_2625 else
  if e2626 : k = 2626 then subst e2626; exact slawChunk_2626 else
  if e2627 : k = 2627 then subst e2627; exact slawChunk_2627 else
  if e2628 : k = 2628 then subst e2628; exact slawChunk_2628 else
  if e2629 : k = 2629 then subst e2629; exact slawChunk_2629 else
  if e2630 : k = 2630 then subst e2630; exact slawChunk_2630 else
  if e2631 : k = 2631 then subst e2631; exact slawChunk_2631 else
  omega
end D2
