import Ski.D2Base
import Ski.D2K.S177
/-! Generated.  S-law of D: chunks 1424..1431 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_1424 : slawChunk 1424 = true := by decide +kernel
theorem slawChunk_1425 : slawChunk 1425 = true := by decide +kernel
theorem slawChunk_1426 : slawChunk 1426 = true := by decide +kernel
theorem slawChunk_1427 : slawChunk 1427 = true := by decide +kernel
theorem slawChunk_1428 : slawChunk 1428 = true := by decide +kernel
theorem slawChunk_1429 : slawChunk 1429 = true := by decide +kernel
theorem slawChunk_1430 : slawChunk 1430 = true := by decide +kernel
theorem slawChunk_1431 : slawChunk 1431 = true := by decide +kernel
theorem slawC_178 (k : Nat) (h1 : 1424 ≤ k) (h2 : k < 1432) : slawChunk k = true := by
  if e1424 : k = 1424 then subst e1424; exact slawChunk_1424 else
  if e1425 : k = 1425 then subst e1425; exact slawChunk_1425 else
  if e1426 : k = 1426 then subst e1426; exact slawChunk_1426 else
  if e1427 : k = 1427 then subst e1427; exact slawChunk_1427 else
  if e1428 : k = 1428 then subst e1428; exact slawChunk_1428 else
  if e1429 : k = 1429 then subst e1429; exact slawChunk_1429 else
  if e1430 : k = 1430 then subst e1430; exact slawChunk_1430 else
  if e1431 : k = 1431 then subst e1431; exact slawChunk_1431 else
  omega
end D2
