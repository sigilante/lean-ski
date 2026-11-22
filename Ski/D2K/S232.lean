import Ski.D2Base
import Ski.D2K.S231
/-! Generated.  S-law of D: chunks 1856..1863 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_1856 : slawChunk 1856 = true := by decide +kernel
theorem slawChunk_1857 : slawChunk 1857 = true := by decide +kernel
theorem slawChunk_1858 : slawChunk 1858 = true := by decide +kernel
theorem slawChunk_1859 : slawChunk 1859 = true := by decide +kernel
theorem slawChunk_1860 : slawChunk 1860 = true := by decide +kernel
theorem slawChunk_1861 : slawChunk 1861 = true := by decide +kernel
theorem slawChunk_1862 : slawChunk 1862 = true := by decide +kernel
theorem slawChunk_1863 : slawChunk 1863 = true := by decide +kernel
theorem slawC_232 (k : Nat) (h1 : 1856 ≤ k) (h2 : k < 1864) : slawChunk k = true := by
  if e1856 : k = 1856 then subst e1856; exact slawChunk_1856 else
  if e1857 : k = 1857 then subst e1857; exact slawChunk_1857 else
  if e1858 : k = 1858 then subst e1858; exact slawChunk_1858 else
  if e1859 : k = 1859 then subst e1859; exact slawChunk_1859 else
  if e1860 : k = 1860 then subst e1860; exact slawChunk_1860 else
  if e1861 : k = 1861 then subst e1861; exact slawChunk_1861 else
  if e1862 : k = 1862 then subst e1862; exact slawChunk_1862 else
  if e1863 : k = 1863 then subst e1863; exact slawChunk_1863 else
  omega
end D2
