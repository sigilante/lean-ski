import Ski.D2Base
import Ski.D2K.S216
/-! Generated.  S-law of D: chunks 1736..1743 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_1736 : slawChunk 1736 = true := by decide +kernel
theorem slawChunk_1737 : slawChunk 1737 = true := by decide +kernel
theorem slawChunk_1738 : slawChunk 1738 = true := by decide +kernel
theorem slawChunk_1739 : slawChunk 1739 = true := by decide +kernel
theorem slawChunk_1740 : slawChunk 1740 = true := by decide +kernel
theorem slawChunk_1741 : slawChunk 1741 = true := by decide +kernel
theorem slawChunk_1742 : slawChunk 1742 = true := by decide +kernel
theorem slawChunk_1743 : slawChunk 1743 = true := by decide +kernel
theorem slawC_217 (k : Nat) (h1 : 1736 ≤ k) (h2 : k < 1744) : slawChunk k = true := by
  if e1736 : k = 1736 then subst e1736; exact slawChunk_1736 else
  if e1737 : k = 1737 then subst e1737; exact slawChunk_1737 else
  if e1738 : k = 1738 then subst e1738; exact slawChunk_1738 else
  if e1739 : k = 1739 then subst e1739; exact slawChunk_1739 else
  if e1740 : k = 1740 then subst e1740; exact slawChunk_1740 else
  if e1741 : k = 1741 then subst e1741; exact slawChunk_1741 else
  if e1742 : k = 1742 then subst e1742; exact slawChunk_1742 else
  if e1743 : k = 1743 then subst e1743; exact slawChunk_1743 else
  omega
end D2
