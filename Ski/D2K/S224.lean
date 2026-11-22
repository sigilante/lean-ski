import Ski.D2Base
import Ski.D2K.S223
/-! Generated.  S-law of D: chunks 1792..1799 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_1792 : slawChunk 1792 = true := by decide +kernel
theorem slawChunk_1793 : slawChunk 1793 = true := by decide +kernel
theorem slawChunk_1794 : slawChunk 1794 = true := by decide +kernel
theorem slawChunk_1795 : slawChunk 1795 = true := by decide +kernel
theorem slawChunk_1796 : slawChunk 1796 = true := by decide +kernel
theorem slawChunk_1797 : slawChunk 1797 = true := by decide +kernel
theorem slawChunk_1798 : slawChunk 1798 = true := by decide +kernel
theorem slawChunk_1799 : slawChunk 1799 = true := by decide +kernel
theorem slawC_224 (k : Nat) (h1 : 1792 ≤ k) (h2 : k < 1800) : slawChunk k = true := by
  if e1792 : k = 1792 then subst e1792; exact slawChunk_1792 else
  if e1793 : k = 1793 then subst e1793; exact slawChunk_1793 else
  if e1794 : k = 1794 then subst e1794; exact slawChunk_1794 else
  if e1795 : k = 1795 then subst e1795; exact slawChunk_1795 else
  if e1796 : k = 1796 then subst e1796; exact slawChunk_1796 else
  if e1797 : k = 1797 then subst e1797; exact slawChunk_1797 else
  if e1798 : k = 1798 then subst e1798; exact slawChunk_1798 else
  if e1799 : k = 1799 then subst e1799; exact slawChunk_1799 else
  omega
end D2
