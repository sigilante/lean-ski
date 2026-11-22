import Ski.D2Base
import Ski.D2K.S230
/-! Generated.  S-law of D: chunks 1848..1855 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_1848 : slawChunk 1848 = true := by decide +kernel
theorem slawChunk_1849 : slawChunk 1849 = true := by decide +kernel
theorem slawChunk_1850 : slawChunk 1850 = true := by decide +kernel
theorem slawChunk_1851 : slawChunk 1851 = true := by decide +kernel
theorem slawChunk_1852 : slawChunk 1852 = true := by decide +kernel
theorem slawChunk_1853 : slawChunk 1853 = true := by decide +kernel
theorem slawChunk_1854 : slawChunk 1854 = true := by decide +kernel
theorem slawChunk_1855 : slawChunk 1855 = true := by decide +kernel
theorem slawC_231 (k : Nat) (h1 : 1848 ≤ k) (h2 : k < 1856) : slawChunk k = true := by
  if e1848 : k = 1848 then subst e1848; exact slawChunk_1848 else
  if e1849 : k = 1849 then subst e1849; exact slawChunk_1849 else
  if e1850 : k = 1850 then subst e1850; exact slawChunk_1850 else
  if e1851 : k = 1851 then subst e1851; exact slawChunk_1851 else
  if e1852 : k = 1852 then subst e1852; exact slawChunk_1852 else
  if e1853 : k = 1853 then subst e1853; exact slawChunk_1853 else
  if e1854 : k = 1854 then subst e1854; exact slawChunk_1854 else
  if e1855 : k = 1855 then subst e1855; exact slawChunk_1855 else
  omega
end D2
