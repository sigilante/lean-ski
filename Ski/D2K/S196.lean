import Ski.D2Base
import Ski.D2K.S195
/-! Generated.  S-law of D: chunks 1568..1575 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_1568 : slawChunk 1568 = true := by decide +kernel
theorem slawChunk_1569 : slawChunk 1569 = true := by decide +kernel
theorem slawChunk_1570 : slawChunk 1570 = true := by decide +kernel
theorem slawChunk_1571 : slawChunk 1571 = true := by decide +kernel
theorem slawChunk_1572 : slawChunk 1572 = true := by decide +kernel
theorem slawChunk_1573 : slawChunk 1573 = true := by decide +kernel
theorem slawChunk_1574 : slawChunk 1574 = true := by decide +kernel
theorem slawChunk_1575 : slawChunk 1575 = true := by decide +kernel
theorem slawC_196 (k : Nat) (h1 : 1568 ≤ k) (h2 : k < 1576) : slawChunk k = true := by
  if e1568 : k = 1568 then subst e1568; exact slawChunk_1568 else
  if e1569 : k = 1569 then subst e1569; exact slawChunk_1569 else
  if e1570 : k = 1570 then subst e1570; exact slawChunk_1570 else
  if e1571 : k = 1571 then subst e1571; exact slawChunk_1571 else
  if e1572 : k = 1572 then subst e1572; exact slawChunk_1572 else
  if e1573 : k = 1573 then subst e1573; exact slawChunk_1573 else
  if e1574 : k = 1574 then subst e1574; exact slawChunk_1574 else
  if e1575 : k = 1575 then subst e1575; exact slawChunk_1575 else
  omega
end D2
