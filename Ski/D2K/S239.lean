import Ski.D2Base
import Ski.D2K.S238
/-! Generated.  S-law of D: chunks 1912..1919 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_1912 : slawChunk 1912 = true := by decide +kernel
theorem slawChunk_1913 : slawChunk 1913 = true := by decide +kernel
theorem slawChunk_1914 : slawChunk 1914 = true := by decide +kernel
theorem slawChunk_1915 : slawChunk 1915 = true := by decide +kernel
theorem slawChunk_1916 : slawChunk 1916 = true := by decide +kernel
theorem slawChunk_1917 : slawChunk 1917 = true := by decide +kernel
theorem slawChunk_1918 : slawChunk 1918 = true := by decide +kernel
theorem slawChunk_1919 : slawChunk 1919 = true := by decide +kernel
theorem slawC_239 (k : Nat) (h1 : 1912 ≤ k) (h2 : k < 1920) : slawChunk k = true := by
  if e1912 : k = 1912 then subst e1912; exact slawChunk_1912 else
  if e1913 : k = 1913 then subst e1913; exact slawChunk_1913 else
  if e1914 : k = 1914 then subst e1914; exact slawChunk_1914 else
  if e1915 : k = 1915 then subst e1915; exact slawChunk_1915 else
  if e1916 : k = 1916 then subst e1916; exact slawChunk_1916 else
  if e1917 : k = 1917 then subst e1917; exact slawChunk_1917 else
  if e1918 : k = 1918 then subst e1918; exact slawChunk_1918 else
  if e1919 : k = 1919 then subst e1919; exact slawChunk_1919 else
  omega
end D2
