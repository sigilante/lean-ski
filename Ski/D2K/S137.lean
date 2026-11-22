import Ski.D2Base
import Ski.D2K.S136
/-! Generated.  S-law of D: chunks 1096..1103 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_1096 : slawChunk 1096 = true := by decide +kernel
theorem slawChunk_1097 : slawChunk 1097 = true := by decide +kernel
theorem slawChunk_1098 : slawChunk 1098 = true := by decide +kernel
theorem slawChunk_1099 : slawChunk 1099 = true := by decide +kernel
theorem slawChunk_1100 : slawChunk 1100 = true := by decide +kernel
theorem slawChunk_1101 : slawChunk 1101 = true := by decide +kernel
theorem slawChunk_1102 : slawChunk 1102 = true := by decide +kernel
theorem slawChunk_1103 : slawChunk 1103 = true := by decide +kernel
theorem slawC_137 (k : Nat) (h1 : 1096 ≤ k) (h2 : k < 1104) : slawChunk k = true := by
  if e1096 : k = 1096 then subst e1096; exact slawChunk_1096 else
  if e1097 : k = 1097 then subst e1097; exact slawChunk_1097 else
  if e1098 : k = 1098 then subst e1098; exact slawChunk_1098 else
  if e1099 : k = 1099 then subst e1099; exact slawChunk_1099 else
  if e1100 : k = 1100 then subst e1100; exact slawChunk_1100 else
  if e1101 : k = 1101 then subst e1101; exact slawChunk_1101 else
  if e1102 : k = 1102 then subst e1102; exact slawChunk_1102 else
  if e1103 : k = 1103 then subst e1103; exact slawChunk_1103 else
  omega
end D2
