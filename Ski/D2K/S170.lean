import Ski.D2Base
import Ski.D2K.S169
/-! Generated.  S-law of D: chunks 1360..1367 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_1360 : slawChunk 1360 = true := by decide +kernel
theorem slawChunk_1361 : slawChunk 1361 = true := by decide +kernel
theorem slawChunk_1362 : slawChunk 1362 = true := by decide +kernel
theorem slawChunk_1363 : slawChunk 1363 = true := by decide +kernel
theorem slawChunk_1364 : slawChunk 1364 = true := by decide +kernel
theorem slawChunk_1365 : slawChunk 1365 = true := by decide +kernel
theorem slawChunk_1366 : slawChunk 1366 = true := by decide +kernel
theorem slawChunk_1367 : slawChunk 1367 = true := by decide +kernel
theorem slawC_170 (k : Nat) (h1 : 1360 ≤ k) (h2 : k < 1368) : slawChunk k = true := by
  if e1360 : k = 1360 then subst e1360; exact slawChunk_1360 else
  if e1361 : k = 1361 then subst e1361; exact slawChunk_1361 else
  if e1362 : k = 1362 then subst e1362; exact slawChunk_1362 else
  if e1363 : k = 1363 then subst e1363; exact slawChunk_1363 else
  if e1364 : k = 1364 then subst e1364; exact slawChunk_1364 else
  if e1365 : k = 1365 then subst e1365; exact slawChunk_1365 else
  if e1366 : k = 1366 then subst e1366; exact slawChunk_1366 else
  if e1367 : k = 1367 then subst e1367; exact slawChunk_1367 else
  omega
end D2
