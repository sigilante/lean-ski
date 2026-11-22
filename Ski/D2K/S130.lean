import Ski.D2Base
import Ski.D2K.S129
/-! Generated.  S-law of D: chunks 1040..1047 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_1040 : slawChunk 1040 = true := by decide +kernel
theorem slawChunk_1041 : slawChunk 1041 = true := by decide +kernel
theorem slawChunk_1042 : slawChunk 1042 = true := by decide +kernel
theorem slawChunk_1043 : slawChunk 1043 = true := by decide +kernel
theorem slawChunk_1044 : slawChunk 1044 = true := by decide +kernel
theorem slawChunk_1045 : slawChunk 1045 = true := by decide +kernel
theorem slawChunk_1046 : slawChunk 1046 = true := by decide +kernel
theorem slawChunk_1047 : slawChunk 1047 = true := by decide +kernel
theorem slawC_130 (k : Nat) (h1 : 1040 ≤ k) (h2 : k < 1048) : slawChunk k = true := by
  if e1040 : k = 1040 then subst e1040; exact slawChunk_1040 else
  if e1041 : k = 1041 then subst e1041; exact slawChunk_1041 else
  if e1042 : k = 1042 then subst e1042; exact slawChunk_1042 else
  if e1043 : k = 1043 then subst e1043; exact slawChunk_1043 else
  if e1044 : k = 1044 then subst e1044; exact slawChunk_1044 else
  if e1045 : k = 1045 then subst e1045; exact slawChunk_1045 else
  if e1046 : k = 1046 then subst e1046; exact slawChunk_1046 else
  if e1047 : k = 1047 then subst e1047; exact slawChunk_1047 else
  omega
end D2
