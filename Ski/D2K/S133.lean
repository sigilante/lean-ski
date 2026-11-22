import Ski.D2Base
import Ski.D2K.S132
/-! Generated.  S-law of D: chunks 1064..1071 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_1064 : slawChunk 1064 = true := by decide +kernel
theorem slawChunk_1065 : slawChunk 1065 = true := by decide +kernel
theorem slawChunk_1066 : slawChunk 1066 = true := by decide +kernel
theorem slawChunk_1067 : slawChunk 1067 = true := by decide +kernel
theorem slawChunk_1068 : slawChunk 1068 = true := by decide +kernel
theorem slawChunk_1069 : slawChunk 1069 = true := by decide +kernel
theorem slawChunk_1070 : slawChunk 1070 = true := by decide +kernel
theorem slawChunk_1071 : slawChunk 1071 = true := by decide +kernel
theorem slawC_133 (k : Nat) (h1 : 1064 ≤ k) (h2 : k < 1072) : slawChunk k = true := by
  if e1064 : k = 1064 then subst e1064; exact slawChunk_1064 else
  if e1065 : k = 1065 then subst e1065; exact slawChunk_1065 else
  if e1066 : k = 1066 then subst e1066; exact slawChunk_1066 else
  if e1067 : k = 1067 then subst e1067; exact slawChunk_1067 else
  if e1068 : k = 1068 then subst e1068; exact slawChunk_1068 else
  if e1069 : k = 1069 then subst e1069; exact slawChunk_1069 else
  if e1070 : k = 1070 then subst e1070; exact slawChunk_1070 else
  if e1071 : k = 1071 then subst e1071; exact slawChunk_1071 else
  omega
end D2
