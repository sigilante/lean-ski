import Ski.D2Base
import Ski.D2K.S183
/-! Generated.  S-law of D: chunks 1472..1479 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_1472 : slawChunk 1472 = true := by decide +kernel
theorem slawChunk_1473 : slawChunk 1473 = true := by decide +kernel
theorem slawChunk_1474 : slawChunk 1474 = true := by decide +kernel
theorem slawChunk_1475 : slawChunk 1475 = true := by decide +kernel
theorem slawChunk_1476 : slawChunk 1476 = true := by decide +kernel
theorem slawChunk_1477 : slawChunk 1477 = true := by decide +kernel
theorem slawChunk_1478 : slawChunk 1478 = true := by decide +kernel
theorem slawChunk_1479 : slawChunk 1479 = true := by decide +kernel
theorem slawC_184 (k : Nat) (h1 : 1472 ≤ k) (h2 : k < 1480) : slawChunk k = true := by
  if e1472 : k = 1472 then subst e1472; exact slawChunk_1472 else
  if e1473 : k = 1473 then subst e1473; exact slawChunk_1473 else
  if e1474 : k = 1474 then subst e1474; exact slawChunk_1474 else
  if e1475 : k = 1475 then subst e1475; exact slawChunk_1475 else
  if e1476 : k = 1476 then subst e1476; exact slawChunk_1476 else
  if e1477 : k = 1477 then subst e1477; exact slawChunk_1477 else
  if e1478 : k = 1478 then subst e1478; exact slawChunk_1478 else
  if e1479 : k = 1479 then subst e1479; exact slawChunk_1479 else
  omega
end D2
