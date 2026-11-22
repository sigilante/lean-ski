import Ski.D2Base
import Ski.D2K.S235
/-! Generated.  S-law of D: chunks 1888..1895 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_1888 : slawChunk 1888 = true := by decide +kernel
theorem slawChunk_1889 : slawChunk 1889 = true := by decide +kernel
theorem slawChunk_1890 : slawChunk 1890 = true := by decide +kernel
theorem slawChunk_1891 : slawChunk 1891 = true := by decide +kernel
theorem slawChunk_1892 : slawChunk 1892 = true := by decide +kernel
theorem slawChunk_1893 : slawChunk 1893 = true := by decide +kernel
theorem slawChunk_1894 : slawChunk 1894 = true := by decide +kernel
theorem slawChunk_1895 : slawChunk 1895 = true := by decide +kernel
theorem slawC_236 (k : Nat) (h1 : 1888 ≤ k) (h2 : k < 1896) : slawChunk k = true := by
  if e1888 : k = 1888 then subst e1888; exact slawChunk_1888 else
  if e1889 : k = 1889 then subst e1889; exact slawChunk_1889 else
  if e1890 : k = 1890 then subst e1890; exact slawChunk_1890 else
  if e1891 : k = 1891 then subst e1891; exact slawChunk_1891 else
  if e1892 : k = 1892 then subst e1892; exact slawChunk_1892 else
  if e1893 : k = 1893 then subst e1893; exact slawChunk_1893 else
  if e1894 : k = 1894 then subst e1894; exact slawChunk_1894 else
  if e1895 : k = 1895 then subst e1895; exact slawChunk_1895 else
  omega
end D2
