import Ski.D2Base
import Ski.D2K.S143
/-! Generated.  S-law of D: chunks 1152..1159 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_1152 : slawChunk 1152 = true := by decide +kernel
theorem slawChunk_1153 : slawChunk 1153 = true := by decide +kernel
theorem slawChunk_1154 : slawChunk 1154 = true := by decide +kernel
theorem slawChunk_1155 : slawChunk 1155 = true := by decide +kernel
theorem slawChunk_1156 : slawChunk 1156 = true := by decide +kernel
theorem slawChunk_1157 : slawChunk 1157 = true := by decide +kernel
theorem slawChunk_1158 : slawChunk 1158 = true := by decide +kernel
theorem slawChunk_1159 : slawChunk 1159 = true := by decide +kernel
theorem slawC_144 (k : Nat) (h1 : 1152 ≤ k) (h2 : k < 1160) : slawChunk k = true := by
  if e1152 : k = 1152 then subst e1152; exact slawChunk_1152 else
  if e1153 : k = 1153 then subst e1153; exact slawChunk_1153 else
  if e1154 : k = 1154 then subst e1154; exact slawChunk_1154 else
  if e1155 : k = 1155 then subst e1155; exact slawChunk_1155 else
  if e1156 : k = 1156 then subst e1156; exact slawChunk_1156 else
  if e1157 : k = 1157 then subst e1157; exact slawChunk_1157 else
  if e1158 : k = 1158 then subst e1158; exact slawChunk_1158 else
  if e1159 : k = 1159 then subst e1159; exact slawChunk_1159 else
  omega
end D2
