import Ski.D2Base
import Ski.D2K.S192
/-! Generated.  S-law of D: chunks 1544..1551 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_1544 : slawChunk 1544 = true := by decide +kernel
theorem slawChunk_1545 : slawChunk 1545 = true := by decide +kernel
theorem slawChunk_1546 : slawChunk 1546 = true := by decide +kernel
theorem slawChunk_1547 : slawChunk 1547 = true := by decide +kernel
theorem slawChunk_1548 : slawChunk 1548 = true := by decide +kernel
theorem slawChunk_1549 : slawChunk 1549 = true := by decide +kernel
theorem slawChunk_1550 : slawChunk 1550 = true := by decide +kernel
theorem slawChunk_1551 : slawChunk 1551 = true := by decide +kernel
theorem slawC_193 (k : Nat) (h1 : 1544 ≤ k) (h2 : k < 1552) : slawChunk k = true := by
  if e1544 : k = 1544 then subst e1544; exact slawChunk_1544 else
  if e1545 : k = 1545 then subst e1545; exact slawChunk_1545 else
  if e1546 : k = 1546 then subst e1546; exact slawChunk_1546 else
  if e1547 : k = 1547 then subst e1547; exact slawChunk_1547 else
  if e1548 : k = 1548 then subst e1548; exact slawChunk_1548 else
  if e1549 : k = 1549 then subst e1549; exact slawChunk_1549 else
  if e1550 : k = 1550 then subst e1550; exact slawChunk_1550 else
  if e1551 : k = 1551 then subst e1551; exact slawChunk_1551 else
  omega
end D2
