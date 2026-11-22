import Ski.D2Base
import Ski.D2K.S184
/-! Generated.  S-law of D: chunks 1480..1487 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_1480 : slawChunk 1480 = true := by decide +kernel
theorem slawChunk_1481 : slawChunk 1481 = true := by decide +kernel
theorem slawChunk_1482 : slawChunk 1482 = true := by decide +kernel
theorem slawChunk_1483 : slawChunk 1483 = true := by decide +kernel
theorem slawChunk_1484 : slawChunk 1484 = true := by decide +kernel
theorem slawChunk_1485 : slawChunk 1485 = true := by decide +kernel
theorem slawChunk_1486 : slawChunk 1486 = true := by decide +kernel
theorem slawChunk_1487 : slawChunk 1487 = true := by decide +kernel
theorem slawC_185 (k : Nat) (h1 : 1480 ≤ k) (h2 : k < 1488) : slawChunk k = true := by
  if e1480 : k = 1480 then subst e1480; exact slawChunk_1480 else
  if e1481 : k = 1481 then subst e1481; exact slawChunk_1481 else
  if e1482 : k = 1482 then subst e1482; exact slawChunk_1482 else
  if e1483 : k = 1483 then subst e1483; exact slawChunk_1483 else
  if e1484 : k = 1484 then subst e1484; exact slawChunk_1484 else
  if e1485 : k = 1485 then subst e1485; exact slawChunk_1485 else
  if e1486 : k = 1486 then subst e1486; exact slawChunk_1486 else
  if e1487 : k = 1487 then subst e1487; exact slawChunk_1487 else
  omega
end D2
