import Ski.D2Base
import Ski.D2K.S220
/-! Generated.  S-law of D: chunks 1768..1775 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_1768 : slawChunk 1768 = true := by decide +kernel
theorem slawChunk_1769 : slawChunk 1769 = true := by decide +kernel
theorem slawChunk_1770 : slawChunk 1770 = true := by decide +kernel
theorem slawChunk_1771 : slawChunk 1771 = true := by decide +kernel
theorem slawChunk_1772 : slawChunk 1772 = true := by decide +kernel
theorem slawChunk_1773 : slawChunk 1773 = true := by decide +kernel
theorem slawChunk_1774 : slawChunk 1774 = true := by decide +kernel
theorem slawChunk_1775 : slawChunk 1775 = true := by decide +kernel
theorem slawC_221 (k : Nat) (h1 : 1768 ≤ k) (h2 : k < 1776) : slawChunk k = true := by
  if e1768 : k = 1768 then subst e1768; exact slawChunk_1768 else
  if e1769 : k = 1769 then subst e1769; exact slawChunk_1769 else
  if e1770 : k = 1770 then subst e1770; exact slawChunk_1770 else
  if e1771 : k = 1771 then subst e1771; exact slawChunk_1771 else
  if e1772 : k = 1772 then subst e1772; exact slawChunk_1772 else
  if e1773 : k = 1773 then subst e1773; exact slawChunk_1773 else
  if e1774 : k = 1774 then subst e1774; exact slawChunk_1774 else
  if e1775 : k = 1775 then subst e1775; exact slawChunk_1775 else
  omega
end D2
