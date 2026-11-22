import Ski.D2Base
import Ski.D2K.S203
/-! Generated.  S-law of D: chunks 1632..1639 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_1632 : slawChunk 1632 = true := by decide +kernel
theorem slawChunk_1633 : slawChunk 1633 = true := by decide +kernel
theorem slawChunk_1634 : slawChunk 1634 = true := by decide +kernel
theorem slawChunk_1635 : slawChunk 1635 = true := by decide +kernel
theorem slawChunk_1636 : slawChunk 1636 = true := by decide +kernel
theorem slawChunk_1637 : slawChunk 1637 = true := by decide +kernel
theorem slawChunk_1638 : slawChunk 1638 = true := by decide +kernel
theorem slawChunk_1639 : slawChunk 1639 = true := by decide +kernel
theorem slawC_204 (k : Nat) (h1 : 1632 ≤ k) (h2 : k < 1640) : slawChunk k = true := by
  if e1632 : k = 1632 then subst e1632; exact slawChunk_1632 else
  if e1633 : k = 1633 then subst e1633; exact slawChunk_1633 else
  if e1634 : k = 1634 then subst e1634; exact slawChunk_1634 else
  if e1635 : k = 1635 then subst e1635; exact slawChunk_1635 else
  if e1636 : k = 1636 then subst e1636; exact slawChunk_1636 else
  if e1637 : k = 1637 then subst e1637; exact slawChunk_1637 else
  if e1638 : k = 1638 then subst e1638; exact slawChunk_1638 else
  if e1639 : k = 1639 then subst e1639; exact slawChunk_1639 else
  omega
end D2
