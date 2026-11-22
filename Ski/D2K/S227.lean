import Ski.D2Base
import Ski.D2K.S226
/-! Generated.  S-law of D: chunks 1816..1823 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_1816 : slawChunk 1816 = true := by decide +kernel
theorem slawChunk_1817 : slawChunk 1817 = true := by decide +kernel
theorem slawChunk_1818 : slawChunk 1818 = true := by decide +kernel
theorem slawChunk_1819 : slawChunk 1819 = true := by decide +kernel
theorem slawChunk_1820 : slawChunk 1820 = true := by decide +kernel
theorem slawChunk_1821 : slawChunk 1821 = true := by decide +kernel
theorem slawChunk_1822 : slawChunk 1822 = true := by decide +kernel
theorem slawChunk_1823 : slawChunk 1823 = true := by decide +kernel
theorem slawC_227 (k : Nat) (h1 : 1816 ≤ k) (h2 : k < 1824) : slawChunk k = true := by
  if e1816 : k = 1816 then subst e1816; exact slawChunk_1816 else
  if e1817 : k = 1817 then subst e1817; exact slawChunk_1817 else
  if e1818 : k = 1818 then subst e1818; exact slawChunk_1818 else
  if e1819 : k = 1819 then subst e1819; exact slawChunk_1819 else
  if e1820 : k = 1820 then subst e1820; exact slawChunk_1820 else
  if e1821 : k = 1821 then subst e1821; exact slawChunk_1821 else
  if e1822 : k = 1822 then subst e1822; exact slawChunk_1822 else
  if e1823 : k = 1823 then subst e1823; exact slawChunk_1823 else
  omega
end D2
