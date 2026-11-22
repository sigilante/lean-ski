import Ski.D2Base
import Ski.D2K.S222
/-! Generated.  S-law of D: chunks 1784..1791 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_1784 : slawChunk 1784 = true := by decide +kernel
theorem slawChunk_1785 : slawChunk 1785 = true := by decide +kernel
theorem slawChunk_1786 : slawChunk 1786 = true := by decide +kernel
theorem slawChunk_1787 : slawChunk 1787 = true := by decide +kernel
theorem slawChunk_1788 : slawChunk 1788 = true := by decide +kernel
theorem slawChunk_1789 : slawChunk 1789 = true := by decide +kernel
theorem slawChunk_1790 : slawChunk 1790 = true := by decide +kernel
theorem slawChunk_1791 : slawChunk 1791 = true := by decide +kernel
theorem slawC_223 (k : Nat) (h1 : 1784 ≤ k) (h2 : k < 1792) : slawChunk k = true := by
  if e1784 : k = 1784 then subst e1784; exact slawChunk_1784 else
  if e1785 : k = 1785 then subst e1785; exact slawChunk_1785 else
  if e1786 : k = 1786 then subst e1786; exact slawChunk_1786 else
  if e1787 : k = 1787 then subst e1787; exact slawChunk_1787 else
  if e1788 : k = 1788 then subst e1788; exact slawChunk_1788 else
  if e1789 : k = 1789 then subst e1789; exact slawChunk_1789 else
  if e1790 : k = 1790 then subst e1790; exact slawChunk_1790 else
  if e1791 : k = 1791 then subst e1791; exact slawChunk_1791 else
  omega
end D2
