import Ski.D2Base
import Ski.D2K.S180
/-! Generated.  S-law of D: chunks 1448..1455 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_1448 : slawChunk 1448 = true := by decide +kernel
theorem slawChunk_1449 : slawChunk 1449 = true := by decide +kernel
theorem slawChunk_1450 : slawChunk 1450 = true := by decide +kernel
theorem slawChunk_1451 : slawChunk 1451 = true := by decide +kernel
theorem slawChunk_1452 : slawChunk 1452 = true := by decide +kernel
theorem slawChunk_1453 : slawChunk 1453 = true := by decide +kernel
theorem slawChunk_1454 : slawChunk 1454 = true := by decide +kernel
theorem slawChunk_1455 : slawChunk 1455 = true := by decide +kernel
theorem slawC_181 (k : Nat) (h1 : 1448 ≤ k) (h2 : k < 1456) : slawChunk k = true := by
  if e1448 : k = 1448 then subst e1448; exact slawChunk_1448 else
  if e1449 : k = 1449 then subst e1449; exact slawChunk_1449 else
  if e1450 : k = 1450 then subst e1450; exact slawChunk_1450 else
  if e1451 : k = 1451 then subst e1451; exact slawChunk_1451 else
  if e1452 : k = 1452 then subst e1452; exact slawChunk_1452 else
  if e1453 : k = 1453 then subst e1453; exact slawChunk_1453 else
  if e1454 : k = 1454 then subst e1454; exact slawChunk_1454 else
  if e1455 : k = 1455 then subst e1455; exact slawChunk_1455 else
  omega
end D2
