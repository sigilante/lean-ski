import Ski.D2Base
import Ski.D2K.S217
/-! Generated.  S-law of D: chunks 1744..1751 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_1744 : slawChunk 1744 = true := by decide +kernel
theorem slawChunk_1745 : slawChunk 1745 = true := by decide +kernel
theorem slawChunk_1746 : slawChunk 1746 = true := by decide +kernel
theorem slawChunk_1747 : slawChunk 1747 = true := by decide +kernel
theorem slawChunk_1748 : slawChunk 1748 = true := by decide +kernel
theorem slawChunk_1749 : slawChunk 1749 = true := by decide +kernel
theorem slawChunk_1750 : slawChunk 1750 = true := by decide +kernel
theorem slawChunk_1751 : slawChunk 1751 = true := by decide +kernel
theorem slawC_218 (k : Nat) (h1 : 1744 ≤ k) (h2 : k < 1752) : slawChunk k = true := by
  if e1744 : k = 1744 then subst e1744; exact slawChunk_1744 else
  if e1745 : k = 1745 then subst e1745; exact slawChunk_1745 else
  if e1746 : k = 1746 then subst e1746; exact slawChunk_1746 else
  if e1747 : k = 1747 then subst e1747; exact slawChunk_1747 else
  if e1748 : k = 1748 then subst e1748; exact slawChunk_1748 else
  if e1749 : k = 1749 then subst e1749; exact slawChunk_1749 else
  if e1750 : k = 1750 then subst e1750; exact slawChunk_1750 else
  if e1751 : k = 1751 then subst e1751; exact slawChunk_1751 else
  omega
end D2
