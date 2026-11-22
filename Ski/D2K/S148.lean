import Ski.D2Base
import Ski.D2K.S147
/-! Generated.  S-law of D: chunks 1184..1191 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_1184 : slawChunk 1184 = true := by decide +kernel
theorem slawChunk_1185 : slawChunk 1185 = true := by decide +kernel
theorem slawChunk_1186 : slawChunk 1186 = true := by decide +kernel
theorem slawChunk_1187 : slawChunk 1187 = true := by decide +kernel
theorem slawChunk_1188 : slawChunk 1188 = true := by decide +kernel
theorem slawChunk_1189 : slawChunk 1189 = true := by decide +kernel
theorem slawChunk_1190 : slawChunk 1190 = true := by decide +kernel
theorem slawChunk_1191 : slawChunk 1191 = true := by decide +kernel
theorem slawC_148 (k : Nat) (h1 : 1184 ≤ k) (h2 : k < 1192) : slawChunk k = true := by
  if e1184 : k = 1184 then subst e1184; exact slawChunk_1184 else
  if e1185 : k = 1185 then subst e1185; exact slawChunk_1185 else
  if e1186 : k = 1186 then subst e1186; exact slawChunk_1186 else
  if e1187 : k = 1187 then subst e1187; exact slawChunk_1187 else
  if e1188 : k = 1188 then subst e1188; exact slawChunk_1188 else
  if e1189 : k = 1189 then subst e1189; exact slawChunk_1189 else
  if e1190 : k = 1190 then subst e1190; exact slawChunk_1190 else
  if e1191 : k = 1191 then subst e1191; exact slawChunk_1191 else
  omega
end D2
