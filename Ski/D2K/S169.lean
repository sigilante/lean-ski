import Ski.D2Base
import Ski.D2K.S168
/-! Generated.  S-law of D: chunks 1352..1359 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_1352 : slawChunk 1352 = true := by decide +kernel
theorem slawChunk_1353 : slawChunk 1353 = true := by decide +kernel
theorem slawChunk_1354 : slawChunk 1354 = true := by decide +kernel
theorem slawChunk_1355 : slawChunk 1355 = true := by decide +kernel
theorem slawChunk_1356 : slawChunk 1356 = true := by decide +kernel
theorem slawChunk_1357 : slawChunk 1357 = true := by decide +kernel
theorem slawChunk_1358 : slawChunk 1358 = true := by decide +kernel
theorem slawChunk_1359 : slawChunk 1359 = true := by decide +kernel
theorem slawC_169 (k : Nat) (h1 : 1352 ≤ k) (h2 : k < 1360) : slawChunk k = true := by
  if e1352 : k = 1352 then subst e1352; exact slawChunk_1352 else
  if e1353 : k = 1353 then subst e1353; exact slawChunk_1353 else
  if e1354 : k = 1354 then subst e1354; exact slawChunk_1354 else
  if e1355 : k = 1355 then subst e1355; exact slawChunk_1355 else
  if e1356 : k = 1356 then subst e1356; exact slawChunk_1356 else
  if e1357 : k = 1357 then subst e1357; exact slawChunk_1357 else
  if e1358 : k = 1358 then subst e1358; exact slawChunk_1358 else
  if e1359 : k = 1359 then subst e1359; exact slawChunk_1359 else
  omega
end D2
