import Ski.D2Base
import Ski.D2K.S167
/-! Generated.  S-law of D: chunks 1344..1351 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_1344 : slawChunk 1344 = true := by decide +kernel
theorem slawChunk_1345 : slawChunk 1345 = true := by decide +kernel
theorem slawChunk_1346 : slawChunk 1346 = true := by decide +kernel
theorem slawChunk_1347 : slawChunk 1347 = true := by decide +kernel
theorem slawChunk_1348 : slawChunk 1348 = true := by decide +kernel
theorem slawChunk_1349 : slawChunk 1349 = true := by decide +kernel
theorem slawChunk_1350 : slawChunk 1350 = true := by decide +kernel
theorem slawChunk_1351 : slawChunk 1351 = true := by decide +kernel
theorem slawC_168 (k : Nat) (h1 : 1344 ≤ k) (h2 : k < 1352) : slawChunk k = true := by
  if e1344 : k = 1344 then subst e1344; exact slawChunk_1344 else
  if e1345 : k = 1345 then subst e1345; exact slawChunk_1345 else
  if e1346 : k = 1346 then subst e1346; exact slawChunk_1346 else
  if e1347 : k = 1347 then subst e1347; exact slawChunk_1347 else
  if e1348 : k = 1348 then subst e1348; exact slawChunk_1348 else
  if e1349 : k = 1349 then subst e1349; exact slawChunk_1349 else
  if e1350 : k = 1350 then subst e1350; exact slawChunk_1350 else
  if e1351 : k = 1351 then subst e1351; exact slawChunk_1351 else
  omega
end D2
