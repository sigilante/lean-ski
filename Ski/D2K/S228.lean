import Ski.D2Base
import Ski.D2K.S227
/-! Generated.  S-law of D: chunks 1824..1831 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_1824 : slawChunk 1824 = true := by decide +kernel
theorem slawChunk_1825 : slawChunk 1825 = true := by decide +kernel
theorem slawChunk_1826 : slawChunk 1826 = true := by decide +kernel
theorem slawChunk_1827 : slawChunk 1827 = true := by decide +kernel
theorem slawChunk_1828 : slawChunk 1828 = true := by decide +kernel
theorem slawChunk_1829 : slawChunk 1829 = true := by decide +kernel
theorem slawChunk_1830 : slawChunk 1830 = true := by decide +kernel
theorem slawChunk_1831 : slawChunk 1831 = true := by decide +kernel
theorem slawC_228 (k : Nat) (h1 : 1824 ≤ k) (h2 : k < 1832) : slawChunk k = true := by
  if e1824 : k = 1824 then subst e1824; exact slawChunk_1824 else
  if e1825 : k = 1825 then subst e1825; exact slawChunk_1825 else
  if e1826 : k = 1826 then subst e1826; exact slawChunk_1826 else
  if e1827 : k = 1827 then subst e1827; exact slawChunk_1827 else
  if e1828 : k = 1828 then subst e1828; exact slawChunk_1828 else
  if e1829 : k = 1829 then subst e1829; exact slawChunk_1829 else
  if e1830 : k = 1830 then subst e1830; exact slawChunk_1830 else
  if e1831 : k = 1831 then subst e1831; exact slawChunk_1831 else
  omega
end D2
