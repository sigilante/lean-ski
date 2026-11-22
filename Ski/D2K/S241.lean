import Ski.D2Base
import Ski.D2K.S240
/-! Generated.  S-law of D: chunks 1928..1935 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_1928 : slawChunk 1928 = true := by decide +kernel
theorem slawChunk_1929 : slawChunk 1929 = true := by decide +kernel
theorem slawChunk_1930 : slawChunk 1930 = true := by decide +kernel
theorem slawChunk_1931 : slawChunk 1931 = true := by decide +kernel
theorem slawChunk_1932 : slawChunk 1932 = true := by decide +kernel
theorem slawChunk_1933 : slawChunk 1933 = true := by decide +kernel
theorem slawChunk_1934 : slawChunk 1934 = true := by decide +kernel
theorem slawChunk_1935 : slawChunk 1935 = true := by decide +kernel
theorem slawC_241 (k : Nat) (h1 : 1928 ≤ k) (h2 : k < 1936) : slawChunk k = true := by
  if e1928 : k = 1928 then subst e1928; exact slawChunk_1928 else
  if e1929 : k = 1929 then subst e1929; exact slawChunk_1929 else
  if e1930 : k = 1930 then subst e1930; exact slawChunk_1930 else
  if e1931 : k = 1931 then subst e1931; exact slawChunk_1931 else
  if e1932 : k = 1932 then subst e1932; exact slawChunk_1932 else
  if e1933 : k = 1933 then subst e1933; exact slawChunk_1933 else
  if e1934 : k = 1934 then subst e1934; exact slawChunk_1934 else
  if e1935 : k = 1935 then subst e1935; exact slawChunk_1935 else
  omega
end D2
