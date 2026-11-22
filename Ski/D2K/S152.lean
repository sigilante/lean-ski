import Ski.D2Base
import Ski.D2K.S151
/-! Generated.  S-law of D: chunks 1216..1223 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_1216 : slawChunk 1216 = true := by decide +kernel
theorem slawChunk_1217 : slawChunk 1217 = true := by decide +kernel
theorem slawChunk_1218 : slawChunk 1218 = true := by decide +kernel
theorem slawChunk_1219 : slawChunk 1219 = true := by decide +kernel
theorem slawChunk_1220 : slawChunk 1220 = true := by decide +kernel
theorem slawChunk_1221 : slawChunk 1221 = true := by decide +kernel
theorem slawChunk_1222 : slawChunk 1222 = true := by decide +kernel
theorem slawChunk_1223 : slawChunk 1223 = true := by decide +kernel
theorem slawC_152 (k : Nat) (h1 : 1216 ≤ k) (h2 : k < 1224) : slawChunk k = true := by
  if e1216 : k = 1216 then subst e1216; exact slawChunk_1216 else
  if e1217 : k = 1217 then subst e1217; exact slawChunk_1217 else
  if e1218 : k = 1218 then subst e1218; exact slawChunk_1218 else
  if e1219 : k = 1219 then subst e1219; exact slawChunk_1219 else
  if e1220 : k = 1220 then subst e1220; exact slawChunk_1220 else
  if e1221 : k = 1221 then subst e1221; exact slawChunk_1221 else
  if e1222 : k = 1222 then subst e1222; exact slawChunk_1222 else
  if e1223 : k = 1223 then subst e1223; exact slawChunk_1223 else
  omega
end D2
