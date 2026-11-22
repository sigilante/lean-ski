import Ski.D2Base
import Ski.D2K.S211
/-! Generated.  S-law of D: chunks 1696..1703 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_1696 : slawChunk 1696 = true := by decide +kernel
theorem slawChunk_1697 : slawChunk 1697 = true := by decide +kernel
theorem slawChunk_1698 : slawChunk 1698 = true := by decide +kernel
theorem slawChunk_1699 : slawChunk 1699 = true := by decide +kernel
theorem slawChunk_1700 : slawChunk 1700 = true := by decide +kernel
theorem slawChunk_1701 : slawChunk 1701 = true := by decide +kernel
theorem slawChunk_1702 : slawChunk 1702 = true := by decide +kernel
theorem slawChunk_1703 : slawChunk 1703 = true := by decide +kernel
theorem slawC_212 (k : Nat) (h1 : 1696 ≤ k) (h2 : k < 1704) : slawChunk k = true := by
  if e1696 : k = 1696 then subst e1696; exact slawChunk_1696 else
  if e1697 : k = 1697 then subst e1697; exact slawChunk_1697 else
  if e1698 : k = 1698 then subst e1698; exact slawChunk_1698 else
  if e1699 : k = 1699 then subst e1699; exact slawChunk_1699 else
  if e1700 : k = 1700 then subst e1700; exact slawChunk_1700 else
  if e1701 : k = 1701 then subst e1701; exact slawChunk_1701 else
  if e1702 : k = 1702 then subst e1702; exact slawChunk_1702 else
  if e1703 : k = 1703 then subst e1703; exact slawChunk_1703 else
  omega
end D2
