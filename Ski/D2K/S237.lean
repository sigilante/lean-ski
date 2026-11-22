import Ski.D2Base
import Ski.D2K.S236
/-! Generated.  S-law of D: chunks 1896..1903 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_1896 : slawChunk 1896 = true := by decide +kernel
theorem slawChunk_1897 : slawChunk 1897 = true := by decide +kernel
theorem slawChunk_1898 : slawChunk 1898 = true := by decide +kernel
theorem slawChunk_1899 : slawChunk 1899 = true := by decide +kernel
theorem slawChunk_1900 : slawChunk 1900 = true := by decide +kernel
theorem slawChunk_1901 : slawChunk 1901 = true := by decide +kernel
theorem slawChunk_1902 : slawChunk 1902 = true := by decide +kernel
theorem slawChunk_1903 : slawChunk 1903 = true := by decide +kernel
theorem slawC_237 (k : Nat) (h1 : 1896 ≤ k) (h2 : k < 1904) : slawChunk k = true := by
  if e1896 : k = 1896 then subst e1896; exact slawChunk_1896 else
  if e1897 : k = 1897 then subst e1897; exact slawChunk_1897 else
  if e1898 : k = 1898 then subst e1898; exact slawChunk_1898 else
  if e1899 : k = 1899 then subst e1899; exact slawChunk_1899 else
  if e1900 : k = 1900 then subst e1900; exact slawChunk_1900 else
  if e1901 : k = 1901 then subst e1901; exact slawChunk_1901 else
  if e1902 : k = 1902 then subst e1902; exact slawChunk_1902 else
  if e1903 : k = 1903 then subst e1903; exact slawChunk_1903 else
  omega
end D2
