import Ski.D2Base
import Ski.D2K.S341
/-! Generated.  S-law of D: chunks 2736..2743 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_2736 : slawChunk 2736 = true := by decide +kernel
theorem slawChunk_2737 : slawChunk 2737 = true := by decide +kernel
theorem slawChunk_2738 : slawChunk 2738 = true := by decide +kernel
theorem slawChunk_2739 : slawChunk 2739 = true := by decide +kernel
theorem slawChunk_2740 : slawChunk 2740 = true := by decide +kernel
theorem slawChunk_2741 : slawChunk 2741 = true := by decide +kernel
theorem slawChunk_2742 : slawChunk 2742 = true := by decide +kernel
theorem slawChunk_2743 : slawChunk 2743 = true := by decide +kernel
theorem slawC_342 (k : Nat) (h1 : 2736 ≤ k) (h2 : k < 2744) : slawChunk k = true := by
  if e2736 : k = 2736 then subst e2736; exact slawChunk_2736 else
  if e2737 : k = 2737 then subst e2737; exact slawChunk_2737 else
  if e2738 : k = 2738 then subst e2738; exact slawChunk_2738 else
  if e2739 : k = 2739 then subst e2739; exact slawChunk_2739 else
  if e2740 : k = 2740 then subst e2740; exact slawChunk_2740 else
  if e2741 : k = 2741 then subst e2741; exact slawChunk_2741 else
  if e2742 : k = 2742 then subst e2742; exact slawChunk_2742 else
  if e2743 : k = 2743 then subst e2743; exact slawChunk_2743 else
  omega
end D2
