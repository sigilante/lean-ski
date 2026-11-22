import Ski.D2Base
import Ski.D2K.S140
/-! Generated.  S-law of D: chunks 1128..1135 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_1128 : slawChunk 1128 = true := by decide +kernel
theorem slawChunk_1129 : slawChunk 1129 = true := by decide +kernel
theorem slawChunk_1130 : slawChunk 1130 = true := by decide +kernel
theorem slawChunk_1131 : slawChunk 1131 = true := by decide +kernel
theorem slawChunk_1132 : slawChunk 1132 = true := by decide +kernel
theorem slawChunk_1133 : slawChunk 1133 = true := by decide +kernel
theorem slawChunk_1134 : slawChunk 1134 = true := by decide +kernel
theorem slawChunk_1135 : slawChunk 1135 = true := by decide +kernel
theorem slawC_141 (k : Nat) (h1 : 1128 ≤ k) (h2 : k < 1136) : slawChunk k = true := by
  if e1128 : k = 1128 then subst e1128; exact slawChunk_1128 else
  if e1129 : k = 1129 then subst e1129; exact slawChunk_1129 else
  if e1130 : k = 1130 then subst e1130; exact slawChunk_1130 else
  if e1131 : k = 1131 then subst e1131; exact slawChunk_1131 else
  if e1132 : k = 1132 then subst e1132; exact slawChunk_1132 else
  if e1133 : k = 1133 then subst e1133; exact slawChunk_1133 else
  if e1134 : k = 1134 then subst e1134; exact slawChunk_1134 else
  if e1135 : k = 1135 then subst e1135; exact slawChunk_1135 else
  omega
end D2
