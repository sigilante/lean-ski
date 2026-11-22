import Ski.D2Base
import Ski.D2K.S207
/-! Generated.  S-law of D: chunks 1664..1671 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_1664 : slawChunk 1664 = true := by decide +kernel
theorem slawChunk_1665 : slawChunk 1665 = true := by decide +kernel
theorem slawChunk_1666 : slawChunk 1666 = true := by decide +kernel
theorem slawChunk_1667 : slawChunk 1667 = true := by decide +kernel
theorem slawChunk_1668 : slawChunk 1668 = true := by decide +kernel
theorem slawChunk_1669 : slawChunk 1669 = true := by decide +kernel
theorem slawChunk_1670 : slawChunk 1670 = true := by decide +kernel
theorem slawChunk_1671 : slawChunk 1671 = true := by decide +kernel
theorem slawC_208 (k : Nat) (h1 : 1664 ≤ k) (h2 : k < 1672) : slawChunk k = true := by
  if e1664 : k = 1664 then subst e1664; exact slawChunk_1664 else
  if e1665 : k = 1665 then subst e1665; exact slawChunk_1665 else
  if e1666 : k = 1666 then subst e1666; exact slawChunk_1666 else
  if e1667 : k = 1667 then subst e1667; exact slawChunk_1667 else
  if e1668 : k = 1668 then subst e1668; exact slawChunk_1668 else
  if e1669 : k = 1669 then subst e1669; exact slawChunk_1669 else
  if e1670 : k = 1670 then subst e1670; exact slawChunk_1670 else
  if e1671 : k = 1671 then subst e1671; exact slawChunk_1671 else
  omega
end D2
