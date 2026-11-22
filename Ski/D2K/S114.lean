import Ski.D2Base
import Ski.D2K.S113
/-! Generated.  S-law of D: chunks 912..919 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_912 : slawChunk 912 = true := by decide +kernel
theorem slawChunk_913 : slawChunk 913 = true := by decide +kernel
theorem slawChunk_914 : slawChunk 914 = true := by decide +kernel
theorem slawChunk_915 : slawChunk 915 = true := by decide +kernel
theorem slawChunk_916 : slawChunk 916 = true := by decide +kernel
theorem slawChunk_917 : slawChunk 917 = true := by decide +kernel
theorem slawChunk_918 : slawChunk 918 = true := by decide +kernel
theorem slawChunk_919 : slawChunk 919 = true := by decide +kernel
theorem slawC_114 (k : Nat) (h1 : 912 ≤ k) (h2 : k < 920) : slawChunk k = true := by
  if e912 : k = 912 then subst e912; exact slawChunk_912 else
  if e913 : k = 913 then subst e913; exact slawChunk_913 else
  if e914 : k = 914 then subst e914; exact slawChunk_914 else
  if e915 : k = 915 then subst e915; exact slawChunk_915 else
  if e916 : k = 916 then subst e916; exact slawChunk_916 else
  if e917 : k = 917 then subst e917; exact slawChunk_917 else
  if e918 : k = 918 then subst e918; exact slawChunk_918 else
  if e919 : k = 919 then subst e919; exact slawChunk_919 else
  omega
end D2
