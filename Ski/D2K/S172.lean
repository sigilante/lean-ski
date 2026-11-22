import Ski.D2Base
import Ski.D2K.S171
/-! Generated.  S-law of D: chunks 1376..1383 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_1376 : slawChunk 1376 = true := by decide +kernel
theorem slawChunk_1377 : slawChunk 1377 = true := by decide +kernel
theorem slawChunk_1378 : slawChunk 1378 = true := by decide +kernel
theorem slawChunk_1379 : slawChunk 1379 = true := by decide +kernel
theorem slawChunk_1380 : slawChunk 1380 = true := by decide +kernel
theorem slawChunk_1381 : slawChunk 1381 = true := by decide +kernel
theorem slawChunk_1382 : slawChunk 1382 = true := by decide +kernel
theorem slawChunk_1383 : slawChunk 1383 = true := by decide +kernel
theorem slawC_172 (k : Nat) (h1 : 1376 ≤ k) (h2 : k < 1384) : slawChunk k = true := by
  if e1376 : k = 1376 then subst e1376; exact slawChunk_1376 else
  if e1377 : k = 1377 then subst e1377; exact slawChunk_1377 else
  if e1378 : k = 1378 then subst e1378; exact slawChunk_1378 else
  if e1379 : k = 1379 then subst e1379; exact slawChunk_1379 else
  if e1380 : k = 1380 then subst e1380; exact slawChunk_1380 else
  if e1381 : k = 1381 then subst e1381; exact slawChunk_1381 else
  if e1382 : k = 1382 then subst e1382; exact slawChunk_1382 else
  if e1383 : k = 1383 then subst e1383; exact slawChunk_1383 else
  omega
end D2
