import Ski.D2Base
import Ski.D2K.S213
/-! Generated.  S-law of D: chunks 1712..1719 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_1712 : slawChunk 1712 = true := by decide +kernel
theorem slawChunk_1713 : slawChunk 1713 = true := by decide +kernel
theorem slawChunk_1714 : slawChunk 1714 = true := by decide +kernel
theorem slawChunk_1715 : slawChunk 1715 = true := by decide +kernel
theorem slawChunk_1716 : slawChunk 1716 = true := by decide +kernel
theorem slawChunk_1717 : slawChunk 1717 = true := by decide +kernel
theorem slawChunk_1718 : slawChunk 1718 = true := by decide +kernel
theorem slawChunk_1719 : slawChunk 1719 = true := by decide +kernel
theorem slawC_214 (k : Nat) (h1 : 1712 ≤ k) (h2 : k < 1720) : slawChunk k = true := by
  if e1712 : k = 1712 then subst e1712; exact slawChunk_1712 else
  if e1713 : k = 1713 then subst e1713; exact slawChunk_1713 else
  if e1714 : k = 1714 then subst e1714; exact slawChunk_1714 else
  if e1715 : k = 1715 then subst e1715; exact slawChunk_1715 else
  if e1716 : k = 1716 then subst e1716; exact slawChunk_1716 else
  if e1717 : k = 1717 then subst e1717; exact slawChunk_1717 else
  if e1718 : k = 1718 then subst e1718; exact slawChunk_1718 else
  if e1719 : k = 1719 then subst e1719; exact slawChunk_1719 else
  omega
end D2
