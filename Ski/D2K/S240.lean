import Ski.D2Base
import Ski.D2K.S239
/-! Generated.  S-law of D: chunks 1920..1927 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_1920 : slawChunk 1920 = true := by decide +kernel
theorem slawChunk_1921 : slawChunk 1921 = true := by decide +kernel
theorem slawChunk_1922 : slawChunk 1922 = true := by decide +kernel
theorem slawChunk_1923 : slawChunk 1923 = true := by decide +kernel
theorem slawChunk_1924 : slawChunk 1924 = true := by decide +kernel
theorem slawChunk_1925 : slawChunk 1925 = true := by decide +kernel
theorem slawChunk_1926 : slawChunk 1926 = true := by decide +kernel
theorem slawChunk_1927 : slawChunk 1927 = true := by decide +kernel
theorem slawC_240 (k : Nat) (h1 : 1920 ≤ k) (h2 : k < 1928) : slawChunk k = true := by
  if e1920 : k = 1920 then subst e1920; exact slawChunk_1920 else
  if e1921 : k = 1921 then subst e1921; exact slawChunk_1921 else
  if e1922 : k = 1922 then subst e1922; exact slawChunk_1922 else
  if e1923 : k = 1923 then subst e1923; exact slawChunk_1923 else
  if e1924 : k = 1924 then subst e1924; exact slawChunk_1924 else
  if e1925 : k = 1925 then subst e1925; exact slawChunk_1925 else
  if e1926 : k = 1926 then subst e1926; exact slawChunk_1926 else
  if e1927 : k = 1927 then subst e1927; exact slawChunk_1927 else
  omega
end D2
