import Ski.D2Base
import Ski.D2K.S365
/-! Generated.  S-law of D: chunks 2928..2935 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_2928 : slawChunk 2928 = true := by decide +kernel
theorem slawChunk_2929 : slawChunk 2929 = true := by decide +kernel
theorem slawChunk_2930 : slawChunk 2930 = true := by decide +kernel
theorem slawChunk_2931 : slawChunk 2931 = true := by decide +kernel
theorem slawChunk_2932 : slawChunk 2932 = true := by decide +kernel
theorem slawChunk_2933 : slawChunk 2933 = true := by decide +kernel
theorem slawChunk_2934 : slawChunk 2934 = true := by decide +kernel
theorem slawChunk_2935 : slawChunk 2935 = true := by decide +kernel
theorem slawC_366 (k : Nat) (h1 : 2928 ≤ k) (h2 : k < 2936) : slawChunk k = true := by
  if e2928 : k = 2928 then subst e2928; exact slawChunk_2928 else
  if e2929 : k = 2929 then subst e2929; exact slawChunk_2929 else
  if e2930 : k = 2930 then subst e2930; exact slawChunk_2930 else
  if e2931 : k = 2931 then subst e2931; exact slawChunk_2931 else
  if e2932 : k = 2932 then subst e2932; exact slawChunk_2932 else
  if e2933 : k = 2933 then subst e2933; exact slawChunk_2933 else
  if e2934 : k = 2934 then subst e2934; exact slawChunk_2934 else
  if e2935 : k = 2935 then subst e2935; exact slawChunk_2935 else
  omega
end D2
