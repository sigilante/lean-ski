import Ski.D2Base
import Ski.D2K.S104
/-! Generated.  S-law of D: chunks 840..847 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_840 : slawChunk 840 = true := by decide +kernel
theorem slawChunk_841 : slawChunk 841 = true := by decide +kernel
theorem slawChunk_842 : slawChunk 842 = true := by decide +kernel
theorem slawChunk_843 : slawChunk 843 = true := by decide +kernel
theorem slawChunk_844 : slawChunk 844 = true := by decide +kernel
theorem slawChunk_845 : slawChunk 845 = true := by decide +kernel
theorem slawChunk_846 : slawChunk 846 = true := by decide +kernel
theorem slawChunk_847 : slawChunk 847 = true := by decide +kernel
theorem slawC_105 (k : Nat) (h1 : 840 ≤ k) (h2 : k < 848) : slawChunk k = true := by
  if e840 : k = 840 then subst e840; exact slawChunk_840 else
  if e841 : k = 841 then subst e841; exact slawChunk_841 else
  if e842 : k = 842 then subst e842; exact slawChunk_842 else
  if e843 : k = 843 then subst e843; exact slawChunk_843 else
  if e844 : k = 844 then subst e844; exact slawChunk_844 else
  if e845 : k = 845 then subst e845; exact slawChunk_845 else
  if e846 : k = 846 then subst e846; exact slawChunk_846 else
  if e847 : k = 847 then subst e847; exact slawChunk_847 else
  omega
end D2
