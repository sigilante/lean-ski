import Ski.D2Base
import Ski.D2K.S146
/-! Generated.  S-law of D: chunks 1176..1183 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_1176 : slawChunk 1176 = true := by decide +kernel
theorem slawChunk_1177 : slawChunk 1177 = true := by decide +kernel
theorem slawChunk_1178 : slawChunk 1178 = true := by decide +kernel
theorem slawChunk_1179 : slawChunk 1179 = true := by decide +kernel
theorem slawChunk_1180 : slawChunk 1180 = true := by decide +kernel
theorem slawChunk_1181 : slawChunk 1181 = true := by decide +kernel
theorem slawChunk_1182 : slawChunk 1182 = true := by decide +kernel
theorem slawChunk_1183 : slawChunk 1183 = true := by decide +kernel
theorem slawC_147 (k : Nat) (h1 : 1176 ≤ k) (h2 : k < 1184) : slawChunk k = true := by
  if e1176 : k = 1176 then subst e1176; exact slawChunk_1176 else
  if e1177 : k = 1177 then subst e1177; exact slawChunk_1177 else
  if e1178 : k = 1178 then subst e1178; exact slawChunk_1178 else
  if e1179 : k = 1179 then subst e1179; exact slawChunk_1179 else
  if e1180 : k = 1180 then subst e1180; exact slawChunk_1180 else
  if e1181 : k = 1181 then subst e1181; exact slawChunk_1181 else
  if e1182 : k = 1182 then subst e1182; exact slawChunk_1182 else
  if e1183 : k = 1183 then subst e1183; exact slawChunk_1183 else
  omega
end D2
