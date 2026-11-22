import Ski.D2Base
import Ski.D2K.S193
/-! Generated.  S-law of D: chunks 1552..1559 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_1552 : slawChunk 1552 = true := by decide +kernel
theorem slawChunk_1553 : slawChunk 1553 = true := by decide +kernel
theorem slawChunk_1554 : slawChunk 1554 = true := by decide +kernel
theorem slawChunk_1555 : slawChunk 1555 = true := by decide +kernel
theorem slawChunk_1556 : slawChunk 1556 = true := by decide +kernel
theorem slawChunk_1557 : slawChunk 1557 = true := by decide +kernel
theorem slawChunk_1558 : slawChunk 1558 = true := by decide +kernel
theorem slawChunk_1559 : slawChunk 1559 = true := by decide +kernel
theorem slawC_194 (k : Nat) (h1 : 1552 ≤ k) (h2 : k < 1560) : slawChunk k = true := by
  if e1552 : k = 1552 then subst e1552; exact slawChunk_1552 else
  if e1553 : k = 1553 then subst e1553; exact slawChunk_1553 else
  if e1554 : k = 1554 then subst e1554; exact slawChunk_1554 else
  if e1555 : k = 1555 then subst e1555; exact slawChunk_1555 else
  if e1556 : k = 1556 then subst e1556; exact slawChunk_1556 else
  if e1557 : k = 1557 then subst e1557; exact slawChunk_1557 else
  if e1558 : k = 1558 then subst e1558; exact slawChunk_1558 else
  if e1559 : k = 1559 then subst e1559; exact slawChunk_1559 else
  omega
end D2
