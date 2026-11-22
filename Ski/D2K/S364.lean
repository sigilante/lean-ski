import Ski.D2Base
import Ski.D2K.S363
/-! Generated.  S-law of D: chunks 2912..2919 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_2912 : slawChunk 2912 = true := by decide +kernel
theorem slawChunk_2913 : slawChunk 2913 = true := by decide +kernel
theorem slawChunk_2914 : slawChunk 2914 = true := by decide +kernel
theorem slawChunk_2915 : slawChunk 2915 = true := by decide +kernel
theorem slawChunk_2916 : slawChunk 2916 = true := by decide +kernel
theorem slawChunk_2917 : slawChunk 2917 = true := by decide +kernel
theorem slawChunk_2918 : slawChunk 2918 = true := by decide +kernel
theorem slawChunk_2919 : slawChunk 2919 = true := by decide +kernel
theorem slawC_364 (k : Nat) (h1 : 2912 ≤ k) (h2 : k < 2920) : slawChunk k = true := by
  if e2912 : k = 2912 then subst e2912; exact slawChunk_2912 else
  if e2913 : k = 2913 then subst e2913; exact slawChunk_2913 else
  if e2914 : k = 2914 then subst e2914; exact slawChunk_2914 else
  if e2915 : k = 2915 then subst e2915; exact slawChunk_2915 else
  if e2916 : k = 2916 then subst e2916; exact slawChunk_2916 else
  if e2917 : k = 2917 then subst e2917; exact slawChunk_2917 else
  if e2918 : k = 2918 then subst e2918; exact slawChunk_2918 else
  if e2919 : k = 2919 then subst e2919; exact slawChunk_2919 else
  omega
end D2
