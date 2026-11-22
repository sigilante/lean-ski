import Ski.D2Base
import Ski.D2K.S228
/-! Generated.  S-law of D: chunks 1832..1839 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_1832 : slawChunk 1832 = true := by decide +kernel
theorem slawChunk_1833 : slawChunk 1833 = true := by decide +kernel
theorem slawChunk_1834 : slawChunk 1834 = true := by decide +kernel
theorem slawChunk_1835 : slawChunk 1835 = true := by decide +kernel
theorem slawChunk_1836 : slawChunk 1836 = true := by decide +kernel
theorem slawChunk_1837 : slawChunk 1837 = true := by decide +kernel
theorem slawChunk_1838 : slawChunk 1838 = true := by decide +kernel
theorem slawChunk_1839 : slawChunk 1839 = true := by decide +kernel
theorem slawC_229 (k : Nat) (h1 : 1832 ≤ k) (h2 : k < 1840) : slawChunk k = true := by
  if e1832 : k = 1832 then subst e1832; exact slawChunk_1832 else
  if e1833 : k = 1833 then subst e1833; exact slawChunk_1833 else
  if e1834 : k = 1834 then subst e1834; exact slawChunk_1834 else
  if e1835 : k = 1835 then subst e1835; exact slawChunk_1835 else
  if e1836 : k = 1836 then subst e1836; exact slawChunk_1836 else
  if e1837 : k = 1837 then subst e1837; exact slawChunk_1837 else
  if e1838 : k = 1838 then subst e1838; exact slawChunk_1838 else
  if e1839 : k = 1839 then subst e1839; exact slawChunk_1839 else
  omega
end D2
