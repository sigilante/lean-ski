import Ski.D2Base
import Ski.D2K.S232
/-! Generated.  S-law of D: chunks 1864..1871 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_1864 : slawChunk 1864 = true := by decide +kernel
theorem slawChunk_1865 : slawChunk 1865 = true := by decide +kernel
theorem slawChunk_1866 : slawChunk 1866 = true := by decide +kernel
theorem slawChunk_1867 : slawChunk 1867 = true := by decide +kernel
theorem slawChunk_1868 : slawChunk 1868 = true := by decide +kernel
theorem slawChunk_1869 : slawChunk 1869 = true := by decide +kernel
theorem slawChunk_1870 : slawChunk 1870 = true := by decide +kernel
theorem slawChunk_1871 : slawChunk 1871 = true := by decide +kernel
theorem slawC_233 (k : Nat) (h1 : 1864 ≤ k) (h2 : k < 1872) : slawChunk k = true := by
  if e1864 : k = 1864 then subst e1864; exact slawChunk_1864 else
  if e1865 : k = 1865 then subst e1865; exact slawChunk_1865 else
  if e1866 : k = 1866 then subst e1866; exact slawChunk_1866 else
  if e1867 : k = 1867 then subst e1867; exact slawChunk_1867 else
  if e1868 : k = 1868 then subst e1868; exact slawChunk_1868 else
  if e1869 : k = 1869 then subst e1869; exact slawChunk_1869 else
  if e1870 : k = 1870 then subst e1870; exact slawChunk_1870 else
  if e1871 : k = 1871 then subst e1871; exact slawChunk_1871 else
  omega
end D2
