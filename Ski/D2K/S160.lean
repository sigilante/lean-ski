import Ski.D2Base
import Ski.D2K.S159
/-! Generated.  S-law of D: chunks 1280..1287 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_1280 : slawChunk 1280 = true := by decide +kernel
theorem slawChunk_1281 : slawChunk 1281 = true := by decide +kernel
theorem slawChunk_1282 : slawChunk 1282 = true := by decide +kernel
theorem slawChunk_1283 : slawChunk 1283 = true := by decide +kernel
theorem slawChunk_1284 : slawChunk 1284 = true := by decide +kernel
theorem slawChunk_1285 : slawChunk 1285 = true := by decide +kernel
theorem slawChunk_1286 : slawChunk 1286 = true := by decide +kernel
theorem slawChunk_1287 : slawChunk 1287 = true := by decide +kernel
theorem slawC_160 (k : Nat) (h1 : 1280 ≤ k) (h2 : k < 1288) : slawChunk k = true := by
  if e1280 : k = 1280 then subst e1280; exact slawChunk_1280 else
  if e1281 : k = 1281 then subst e1281; exact slawChunk_1281 else
  if e1282 : k = 1282 then subst e1282; exact slawChunk_1282 else
  if e1283 : k = 1283 then subst e1283; exact slawChunk_1283 else
  if e1284 : k = 1284 then subst e1284; exact slawChunk_1284 else
  if e1285 : k = 1285 then subst e1285; exact slawChunk_1285 else
  if e1286 : k = 1286 then subst e1286; exact slawChunk_1286 else
  if e1287 : k = 1287 then subst e1287; exact slawChunk_1287 else
  omega
end D2
