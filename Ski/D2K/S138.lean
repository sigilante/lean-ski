import Ski.D2Base
import Ski.D2K.S137
/-! Generated.  S-law of D: chunks 1104..1111 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_1104 : slawChunk 1104 = true := by decide +kernel
theorem slawChunk_1105 : slawChunk 1105 = true := by decide +kernel
theorem slawChunk_1106 : slawChunk 1106 = true := by decide +kernel
theorem slawChunk_1107 : slawChunk 1107 = true := by decide +kernel
theorem slawChunk_1108 : slawChunk 1108 = true := by decide +kernel
theorem slawChunk_1109 : slawChunk 1109 = true := by decide +kernel
theorem slawChunk_1110 : slawChunk 1110 = true := by decide +kernel
theorem slawChunk_1111 : slawChunk 1111 = true := by decide +kernel
theorem slawC_138 (k : Nat) (h1 : 1104 ≤ k) (h2 : k < 1112) : slawChunk k = true := by
  if e1104 : k = 1104 then subst e1104; exact slawChunk_1104 else
  if e1105 : k = 1105 then subst e1105; exact slawChunk_1105 else
  if e1106 : k = 1106 then subst e1106; exact slawChunk_1106 else
  if e1107 : k = 1107 then subst e1107; exact slawChunk_1107 else
  if e1108 : k = 1108 then subst e1108; exact slawChunk_1108 else
  if e1109 : k = 1109 then subst e1109; exact slawChunk_1109 else
  if e1110 : k = 1110 then subst e1110; exact slawChunk_1110 else
  if e1111 : k = 1111 then subst e1111; exact slawChunk_1111 else
  omega
end D2
