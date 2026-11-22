import Ski.D2Base
import Ski.D2K.S361
/-! Generated.  S-law of D: chunks 2896..2903 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_2896 : slawChunk 2896 = true := by decide +kernel
theorem slawChunk_2897 : slawChunk 2897 = true := by decide +kernel
theorem slawChunk_2898 : slawChunk 2898 = true := by decide +kernel
theorem slawChunk_2899 : slawChunk 2899 = true := by decide +kernel
theorem slawChunk_2900 : slawChunk 2900 = true := by decide +kernel
theorem slawChunk_2901 : slawChunk 2901 = true := by decide +kernel
theorem slawChunk_2902 : slawChunk 2902 = true := by decide +kernel
theorem slawChunk_2903 : slawChunk 2903 = true := by decide +kernel
theorem slawC_362 (k : Nat) (h1 : 2896 ≤ k) (h2 : k < 2904) : slawChunk k = true := by
  if e2896 : k = 2896 then subst e2896; exact slawChunk_2896 else
  if e2897 : k = 2897 then subst e2897; exact slawChunk_2897 else
  if e2898 : k = 2898 then subst e2898; exact slawChunk_2898 else
  if e2899 : k = 2899 then subst e2899; exact slawChunk_2899 else
  if e2900 : k = 2900 then subst e2900; exact slawChunk_2900 else
  if e2901 : k = 2901 then subst e2901; exact slawChunk_2901 else
  if e2902 : k = 2902 then subst e2902; exact slawChunk_2902 else
  if e2903 : k = 2903 then subst e2903; exact slawChunk_2903 else
  omega
end D2
