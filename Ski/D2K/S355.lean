import Ski.D2Base
import Ski.D2K.S354
/-! Generated.  S-law of D: chunks 2840..2847 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_2840 : slawChunk 2840 = true := by decide +kernel
theorem slawChunk_2841 : slawChunk 2841 = true := by decide +kernel
theorem slawChunk_2842 : slawChunk 2842 = true := by decide +kernel
theorem slawChunk_2843 : slawChunk 2843 = true := by decide +kernel
theorem slawChunk_2844 : slawChunk 2844 = true := by decide +kernel
theorem slawChunk_2845 : slawChunk 2845 = true := by decide +kernel
theorem slawChunk_2846 : slawChunk 2846 = true := by decide +kernel
theorem slawChunk_2847 : slawChunk 2847 = true := by decide +kernel
theorem slawC_355 (k : Nat) (h1 : 2840 ≤ k) (h2 : k < 2848) : slawChunk k = true := by
  if e2840 : k = 2840 then subst e2840; exact slawChunk_2840 else
  if e2841 : k = 2841 then subst e2841; exact slawChunk_2841 else
  if e2842 : k = 2842 then subst e2842; exact slawChunk_2842 else
  if e2843 : k = 2843 then subst e2843; exact slawChunk_2843 else
  if e2844 : k = 2844 then subst e2844; exact slawChunk_2844 else
  if e2845 : k = 2845 then subst e2845; exact slawChunk_2845 else
  if e2846 : k = 2846 then subst e2846; exact slawChunk_2846 else
  if e2847 : k = 2847 then subst e2847; exact slawChunk_2847 else
  omega
end D2
