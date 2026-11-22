import Ski.D2Base
import Ski.D2K.S219
/-! Generated.  S-law of D: chunks 1760..1767 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_1760 : slawChunk 1760 = true := by decide +kernel
theorem slawChunk_1761 : slawChunk 1761 = true := by decide +kernel
theorem slawChunk_1762 : slawChunk 1762 = true := by decide +kernel
theorem slawChunk_1763 : slawChunk 1763 = true := by decide +kernel
theorem slawChunk_1764 : slawChunk 1764 = true := by decide +kernel
theorem slawChunk_1765 : slawChunk 1765 = true := by decide +kernel
theorem slawChunk_1766 : slawChunk 1766 = true := by decide +kernel
theorem slawChunk_1767 : slawChunk 1767 = true := by decide +kernel
theorem slawC_220 (k : Nat) (h1 : 1760 ≤ k) (h2 : k < 1768) : slawChunk k = true := by
  if e1760 : k = 1760 then subst e1760; exact slawChunk_1760 else
  if e1761 : k = 1761 then subst e1761; exact slawChunk_1761 else
  if e1762 : k = 1762 then subst e1762; exact slawChunk_1762 else
  if e1763 : k = 1763 then subst e1763; exact slawChunk_1763 else
  if e1764 : k = 1764 then subst e1764; exact slawChunk_1764 else
  if e1765 : k = 1765 then subst e1765; exact slawChunk_1765 else
  if e1766 : k = 1766 then subst e1766; exact slawChunk_1766 else
  if e1767 : k = 1767 then subst e1767; exact slawChunk_1767 else
  omega
end D2
