import Ski.D2Base
import Ski.D2K.S202
/-! Generated.  S-law of D: chunks 1624..1631 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_1624 : slawChunk 1624 = true := by decide +kernel
theorem slawChunk_1625 : slawChunk 1625 = true := by decide +kernel
theorem slawChunk_1626 : slawChunk 1626 = true := by decide +kernel
theorem slawChunk_1627 : slawChunk 1627 = true := by decide +kernel
theorem slawChunk_1628 : slawChunk 1628 = true := by decide +kernel
theorem slawChunk_1629 : slawChunk 1629 = true := by decide +kernel
theorem slawChunk_1630 : slawChunk 1630 = true := by decide +kernel
theorem slawChunk_1631 : slawChunk 1631 = true := by decide +kernel
theorem slawC_203 (k : Nat) (h1 : 1624 ≤ k) (h2 : k < 1632) : slawChunk k = true := by
  if e1624 : k = 1624 then subst e1624; exact slawChunk_1624 else
  if e1625 : k = 1625 then subst e1625; exact slawChunk_1625 else
  if e1626 : k = 1626 then subst e1626; exact slawChunk_1626 else
  if e1627 : k = 1627 then subst e1627; exact slawChunk_1627 else
  if e1628 : k = 1628 then subst e1628; exact slawChunk_1628 else
  if e1629 : k = 1629 then subst e1629; exact slawChunk_1629 else
  if e1630 : k = 1630 then subst e1630; exact slawChunk_1630 else
  if e1631 : k = 1631 then subst e1631; exact slawChunk_1631 else
  omega
end D2
