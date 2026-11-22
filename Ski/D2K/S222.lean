import Ski.D2Base
import Ski.D2K.S221
/-! Generated.  S-law of D: chunks 1776..1783 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_1776 : slawChunk 1776 = true := by decide +kernel
theorem slawChunk_1777 : slawChunk 1777 = true := by decide +kernel
theorem slawChunk_1778 : slawChunk 1778 = true := by decide +kernel
theorem slawChunk_1779 : slawChunk 1779 = true := by decide +kernel
theorem slawChunk_1780 : slawChunk 1780 = true := by decide +kernel
theorem slawChunk_1781 : slawChunk 1781 = true := by decide +kernel
theorem slawChunk_1782 : slawChunk 1782 = true := by decide +kernel
theorem slawChunk_1783 : slawChunk 1783 = true := by decide +kernel
theorem slawC_222 (k : Nat) (h1 : 1776 ≤ k) (h2 : k < 1784) : slawChunk k = true := by
  if e1776 : k = 1776 then subst e1776; exact slawChunk_1776 else
  if e1777 : k = 1777 then subst e1777; exact slawChunk_1777 else
  if e1778 : k = 1778 then subst e1778; exact slawChunk_1778 else
  if e1779 : k = 1779 then subst e1779; exact slawChunk_1779 else
  if e1780 : k = 1780 then subst e1780; exact slawChunk_1780 else
  if e1781 : k = 1781 then subst e1781; exact slawChunk_1781 else
  if e1782 : k = 1782 then subst e1782; exact slawChunk_1782 else
  if e1783 : k = 1783 then subst e1783; exact slawChunk_1783 else
  omega
end D2
