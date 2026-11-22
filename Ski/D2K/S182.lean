import Ski.D2Base
import Ski.D2K.S181
/-! Generated.  S-law of D: chunks 1456..1463 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_1456 : slawChunk 1456 = true := by decide +kernel
theorem slawChunk_1457 : slawChunk 1457 = true := by decide +kernel
theorem slawChunk_1458 : slawChunk 1458 = true := by decide +kernel
theorem slawChunk_1459 : slawChunk 1459 = true := by decide +kernel
theorem slawChunk_1460 : slawChunk 1460 = true := by decide +kernel
theorem slawChunk_1461 : slawChunk 1461 = true := by decide +kernel
theorem slawChunk_1462 : slawChunk 1462 = true := by decide +kernel
theorem slawChunk_1463 : slawChunk 1463 = true := by decide +kernel
theorem slawC_182 (k : Nat) (h1 : 1456 ≤ k) (h2 : k < 1464) : slawChunk k = true := by
  if e1456 : k = 1456 then subst e1456; exact slawChunk_1456 else
  if e1457 : k = 1457 then subst e1457; exact slawChunk_1457 else
  if e1458 : k = 1458 then subst e1458; exact slawChunk_1458 else
  if e1459 : k = 1459 then subst e1459; exact slawChunk_1459 else
  if e1460 : k = 1460 then subst e1460; exact slawChunk_1460 else
  if e1461 : k = 1461 then subst e1461; exact slawChunk_1461 else
  if e1462 : k = 1462 then subst e1462; exact slawChunk_1462 else
  if e1463 : k = 1463 then subst e1463; exact slawChunk_1463 else
  omega
end D2
