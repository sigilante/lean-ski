import Ski.D2Base
import Ski.D2K.S229
/-! Generated.  S-law of D: chunks 1840..1847 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_1840 : slawChunk 1840 = true := by decide +kernel
theorem slawChunk_1841 : slawChunk 1841 = true := by decide +kernel
theorem slawChunk_1842 : slawChunk 1842 = true := by decide +kernel
theorem slawChunk_1843 : slawChunk 1843 = true := by decide +kernel
theorem slawChunk_1844 : slawChunk 1844 = true := by decide +kernel
theorem slawChunk_1845 : slawChunk 1845 = true := by decide +kernel
theorem slawChunk_1846 : slawChunk 1846 = true := by decide +kernel
theorem slawChunk_1847 : slawChunk 1847 = true := by decide +kernel
theorem slawC_230 (k : Nat) (h1 : 1840 ≤ k) (h2 : k < 1848) : slawChunk k = true := by
  if e1840 : k = 1840 then subst e1840; exact slawChunk_1840 else
  if e1841 : k = 1841 then subst e1841; exact slawChunk_1841 else
  if e1842 : k = 1842 then subst e1842; exact slawChunk_1842 else
  if e1843 : k = 1843 then subst e1843; exact slawChunk_1843 else
  if e1844 : k = 1844 then subst e1844; exact slawChunk_1844 else
  if e1845 : k = 1845 then subst e1845; exact slawChunk_1845 else
  if e1846 : k = 1846 then subst e1846; exact slawChunk_1846 else
  if e1847 : k = 1847 then subst e1847; exact slawChunk_1847 else
  omega
end D2
