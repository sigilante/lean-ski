import Ski.D2Base
import Ski.D2K.S186
/-! Generated.  S-law of D: chunks 1496..1503 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_1496 : slawChunk 1496 = true := by decide +kernel
theorem slawChunk_1497 : slawChunk 1497 = true := by decide +kernel
theorem slawChunk_1498 : slawChunk 1498 = true := by decide +kernel
theorem slawChunk_1499 : slawChunk 1499 = true := by decide +kernel
theorem slawChunk_1500 : slawChunk 1500 = true := by decide +kernel
theorem slawChunk_1501 : slawChunk 1501 = true := by decide +kernel
theorem slawChunk_1502 : slawChunk 1502 = true := by decide +kernel
theorem slawChunk_1503 : slawChunk 1503 = true := by decide +kernel
theorem slawC_187 (k : Nat) (h1 : 1496 ≤ k) (h2 : k < 1504) : slawChunk k = true := by
  if e1496 : k = 1496 then subst e1496; exact slawChunk_1496 else
  if e1497 : k = 1497 then subst e1497; exact slawChunk_1497 else
  if e1498 : k = 1498 then subst e1498; exact slawChunk_1498 else
  if e1499 : k = 1499 then subst e1499; exact slawChunk_1499 else
  if e1500 : k = 1500 then subst e1500; exact slawChunk_1500 else
  if e1501 : k = 1501 then subst e1501; exact slawChunk_1501 else
  if e1502 : k = 1502 then subst e1502; exact slawChunk_1502 else
  if e1503 : k = 1503 then subst e1503; exact slawChunk_1503 else
  omega
end D2
