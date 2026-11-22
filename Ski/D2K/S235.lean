import Ski.D2Base
import Ski.D2K.S234
/-! Generated.  S-law of D: chunks 1880..1887 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_1880 : slawChunk 1880 = true := by decide +kernel
theorem slawChunk_1881 : slawChunk 1881 = true := by decide +kernel
theorem slawChunk_1882 : slawChunk 1882 = true := by decide +kernel
theorem slawChunk_1883 : slawChunk 1883 = true := by decide +kernel
theorem slawChunk_1884 : slawChunk 1884 = true := by decide +kernel
theorem slawChunk_1885 : slawChunk 1885 = true := by decide +kernel
theorem slawChunk_1886 : slawChunk 1886 = true := by decide +kernel
theorem slawChunk_1887 : slawChunk 1887 = true := by decide +kernel
theorem slawC_235 (k : Nat) (h1 : 1880 ≤ k) (h2 : k < 1888) : slawChunk k = true := by
  if e1880 : k = 1880 then subst e1880; exact slawChunk_1880 else
  if e1881 : k = 1881 then subst e1881; exact slawChunk_1881 else
  if e1882 : k = 1882 then subst e1882; exact slawChunk_1882 else
  if e1883 : k = 1883 then subst e1883; exact slawChunk_1883 else
  if e1884 : k = 1884 then subst e1884; exact slawChunk_1884 else
  if e1885 : k = 1885 then subst e1885; exact slawChunk_1885 else
  if e1886 : k = 1886 then subst e1886; exact slawChunk_1886 else
  if e1887 : k = 1887 then subst e1887; exact slawChunk_1887 else
  omega
end D2
