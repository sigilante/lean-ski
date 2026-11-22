import Ski.D2Base
import Ski.D2K.S157
/-! Generated.  S-law of D: chunks 1264..1271 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_1264 : slawChunk 1264 = true := by decide +kernel
theorem slawChunk_1265 : slawChunk 1265 = true := by decide +kernel
theorem slawChunk_1266 : slawChunk 1266 = true := by decide +kernel
theorem slawChunk_1267 : slawChunk 1267 = true := by decide +kernel
theorem slawChunk_1268 : slawChunk 1268 = true := by decide +kernel
theorem slawChunk_1269 : slawChunk 1269 = true := by decide +kernel
theorem slawChunk_1270 : slawChunk 1270 = true := by decide +kernel
theorem slawChunk_1271 : slawChunk 1271 = true := by decide +kernel
theorem slawC_158 (k : Nat) (h1 : 1264 ≤ k) (h2 : k < 1272) : slawChunk k = true := by
  if e1264 : k = 1264 then subst e1264; exact slawChunk_1264 else
  if e1265 : k = 1265 then subst e1265; exact slawChunk_1265 else
  if e1266 : k = 1266 then subst e1266; exact slawChunk_1266 else
  if e1267 : k = 1267 then subst e1267; exact slawChunk_1267 else
  if e1268 : k = 1268 then subst e1268; exact slawChunk_1268 else
  if e1269 : k = 1269 then subst e1269; exact slawChunk_1269 else
  if e1270 : k = 1270 then subst e1270; exact slawChunk_1270 else
  if e1271 : k = 1271 then subst e1271; exact slawChunk_1271 else
  omega
end D2
