import Ski.D2Base
import Ski.D2K.S141
/-! Generated.  S-law of D: chunks 1136..1143 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_1136 : slawChunk 1136 = true := by decide +kernel
theorem slawChunk_1137 : slawChunk 1137 = true := by decide +kernel
theorem slawChunk_1138 : slawChunk 1138 = true := by decide +kernel
theorem slawChunk_1139 : slawChunk 1139 = true := by decide +kernel
theorem slawChunk_1140 : slawChunk 1140 = true := by decide +kernel
theorem slawChunk_1141 : slawChunk 1141 = true := by decide +kernel
theorem slawChunk_1142 : slawChunk 1142 = true := by decide +kernel
theorem slawChunk_1143 : slawChunk 1143 = true := by decide +kernel
theorem slawC_142 (k : Nat) (h1 : 1136 ≤ k) (h2 : k < 1144) : slawChunk k = true := by
  if e1136 : k = 1136 then subst e1136; exact slawChunk_1136 else
  if e1137 : k = 1137 then subst e1137; exact slawChunk_1137 else
  if e1138 : k = 1138 then subst e1138; exact slawChunk_1138 else
  if e1139 : k = 1139 then subst e1139; exact slawChunk_1139 else
  if e1140 : k = 1140 then subst e1140; exact slawChunk_1140 else
  if e1141 : k = 1141 then subst e1141; exact slawChunk_1141 else
  if e1142 : k = 1142 then subst e1142; exact slawChunk_1142 else
  if e1143 : k = 1143 then subst e1143; exact slawChunk_1143 else
  omega
end D2
