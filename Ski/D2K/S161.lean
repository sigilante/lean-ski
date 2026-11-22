import Ski.D2Base
import Ski.D2K.S160
/-! Generated.  S-law of D: chunks 1288..1295 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_1288 : slawChunk 1288 = true := by decide +kernel
theorem slawChunk_1289 : slawChunk 1289 = true := by decide +kernel
theorem slawChunk_1290 : slawChunk 1290 = true := by decide +kernel
theorem slawChunk_1291 : slawChunk 1291 = true := by decide +kernel
theorem slawChunk_1292 : slawChunk 1292 = true := by decide +kernel
theorem slawChunk_1293 : slawChunk 1293 = true := by decide +kernel
theorem slawChunk_1294 : slawChunk 1294 = true := by decide +kernel
theorem slawChunk_1295 : slawChunk 1295 = true := by decide +kernel
theorem slawC_161 (k : Nat) (h1 : 1288 ≤ k) (h2 : k < 1296) : slawChunk k = true := by
  if e1288 : k = 1288 then subst e1288; exact slawChunk_1288 else
  if e1289 : k = 1289 then subst e1289; exact slawChunk_1289 else
  if e1290 : k = 1290 then subst e1290; exact slawChunk_1290 else
  if e1291 : k = 1291 then subst e1291; exact slawChunk_1291 else
  if e1292 : k = 1292 then subst e1292; exact slawChunk_1292 else
  if e1293 : k = 1293 then subst e1293; exact slawChunk_1293 else
  if e1294 : k = 1294 then subst e1294; exact slawChunk_1294 else
  if e1295 : k = 1295 then subst e1295; exact slawChunk_1295 else
  omega
end D2
