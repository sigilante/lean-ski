import Ski.D2Base
import Ski.D2K.S371
/-! Generated.  S-law of D: chunks 2976..2983 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_2976 : slawChunk 2976 = true := by decide +kernel
theorem slawChunk_2977 : slawChunk 2977 = true := by decide +kernel
theorem slawChunk_2978 : slawChunk 2978 = true := by decide +kernel
theorem slawChunk_2979 : slawChunk 2979 = true := by decide +kernel
theorem slawChunk_2980 : slawChunk 2980 = true := by decide +kernel
theorem slawChunk_2981 : slawChunk 2981 = true := by decide +kernel
theorem slawChunk_2982 : slawChunk 2982 = true := by decide +kernel
theorem slawChunk_2983 : slawChunk 2983 = true := by decide +kernel
theorem slawC_372 (k : Nat) (h1 : 2976 ≤ k) (h2 : k < 2984) : slawChunk k = true := by
  if e2976 : k = 2976 then subst e2976; exact slawChunk_2976 else
  if e2977 : k = 2977 then subst e2977; exact slawChunk_2977 else
  if e2978 : k = 2978 then subst e2978; exact slawChunk_2978 else
  if e2979 : k = 2979 then subst e2979; exact slawChunk_2979 else
  if e2980 : k = 2980 then subst e2980; exact slawChunk_2980 else
  if e2981 : k = 2981 then subst e2981; exact slawChunk_2981 else
  if e2982 : k = 2982 then subst e2982; exact slawChunk_2982 else
  if e2983 : k = 2983 then subst e2983; exact slawChunk_2983 else
  omega
end D2
