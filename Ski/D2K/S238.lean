import Ski.D2Base
import Ski.D2K.S237
/-! Generated.  S-law of D: chunks 1904..1911 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_1904 : slawChunk 1904 = true := by decide +kernel
theorem slawChunk_1905 : slawChunk 1905 = true := by decide +kernel
theorem slawChunk_1906 : slawChunk 1906 = true := by decide +kernel
theorem slawChunk_1907 : slawChunk 1907 = true := by decide +kernel
theorem slawChunk_1908 : slawChunk 1908 = true := by decide +kernel
theorem slawChunk_1909 : slawChunk 1909 = true := by decide +kernel
theorem slawChunk_1910 : slawChunk 1910 = true := by decide +kernel
theorem slawChunk_1911 : slawChunk 1911 = true := by decide +kernel
theorem slawC_238 (k : Nat) (h1 : 1904 ≤ k) (h2 : k < 1912) : slawChunk k = true := by
  if e1904 : k = 1904 then subst e1904; exact slawChunk_1904 else
  if e1905 : k = 1905 then subst e1905; exact slawChunk_1905 else
  if e1906 : k = 1906 then subst e1906; exact slawChunk_1906 else
  if e1907 : k = 1907 then subst e1907; exact slawChunk_1907 else
  if e1908 : k = 1908 then subst e1908; exact slawChunk_1908 else
  if e1909 : k = 1909 then subst e1909; exact slawChunk_1909 else
  if e1910 : k = 1910 then subst e1910; exact slawChunk_1910 else
  if e1911 : k = 1911 then subst e1911; exact slawChunk_1911 else
  omega
end D2
