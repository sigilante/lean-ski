import Ski.D2Base
import Ski.D2K.S170
/-! Generated.  S-law of D: chunks 1368..1375 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_1368 : slawChunk 1368 = true := by decide +kernel
theorem slawChunk_1369 : slawChunk 1369 = true := by decide +kernel
theorem slawChunk_1370 : slawChunk 1370 = true := by decide +kernel
theorem slawChunk_1371 : slawChunk 1371 = true := by decide +kernel
theorem slawChunk_1372 : slawChunk 1372 = true := by decide +kernel
theorem slawChunk_1373 : slawChunk 1373 = true := by decide +kernel
theorem slawChunk_1374 : slawChunk 1374 = true := by decide +kernel
theorem slawChunk_1375 : slawChunk 1375 = true := by decide +kernel
theorem slawC_171 (k : Nat) (h1 : 1368 ≤ k) (h2 : k < 1376) : slawChunk k = true := by
  if e1368 : k = 1368 then subst e1368; exact slawChunk_1368 else
  if e1369 : k = 1369 then subst e1369; exact slawChunk_1369 else
  if e1370 : k = 1370 then subst e1370; exact slawChunk_1370 else
  if e1371 : k = 1371 then subst e1371; exact slawChunk_1371 else
  if e1372 : k = 1372 then subst e1372; exact slawChunk_1372 else
  if e1373 : k = 1373 then subst e1373; exact slawChunk_1373 else
  if e1374 : k = 1374 then subst e1374; exact slawChunk_1374 else
  if e1375 : k = 1375 then subst e1375; exact slawChunk_1375 else
  omega
end D2
