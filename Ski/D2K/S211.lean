import Ski.D2Base
import Ski.D2K.S210
/-! Generated.  S-law of D: chunks 1688..1695 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_1688 : slawChunk 1688 = true := by decide +kernel
theorem slawChunk_1689 : slawChunk 1689 = true := by decide +kernel
theorem slawChunk_1690 : slawChunk 1690 = true := by decide +kernel
theorem slawChunk_1691 : slawChunk 1691 = true := by decide +kernel
theorem slawChunk_1692 : slawChunk 1692 = true := by decide +kernel
theorem slawChunk_1693 : slawChunk 1693 = true := by decide +kernel
theorem slawChunk_1694 : slawChunk 1694 = true := by decide +kernel
theorem slawChunk_1695 : slawChunk 1695 = true := by decide +kernel
theorem slawC_211 (k : Nat) (h1 : 1688 ≤ k) (h2 : k < 1696) : slawChunk k = true := by
  if e1688 : k = 1688 then subst e1688; exact slawChunk_1688 else
  if e1689 : k = 1689 then subst e1689; exact slawChunk_1689 else
  if e1690 : k = 1690 then subst e1690; exact slawChunk_1690 else
  if e1691 : k = 1691 then subst e1691; exact slawChunk_1691 else
  if e1692 : k = 1692 then subst e1692; exact slawChunk_1692 else
  if e1693 : k = 1693 then subst e1693; exact slawChunk_1693 else
  if e1694 : k = 1694 then subst e1694; exact slawChunk_1694 else
  if e1695 : k = 1695 then subst e1695; exact slawChunk_1695 else
  omega
end D2
