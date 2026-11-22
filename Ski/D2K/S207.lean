import Ski.D2Base
import Ski.D2K.S206
/-! Generated.  S-law of D: chunks 1656..1663 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_1656 : slawChunk 1656 = true := by decide +kernel
theorem slawChunk_1657 : slawChunk 1657 = true := by decide +kernel
theorem slawChunk_1658 : slawChunk 1658 = true := by decide +kernel
theorem slawChunk_1659 : slawChunk 1659 = true := by decide +kernel
theorem slawChunk_1660 : slawChunk 1660 = true := by decide +kernel
theorem slawChunk_1661 : slawChunk 1661 = true := by decide +kernel
theorem slawChunk_1662 : slawChunk 1662 = true := by decide +kernel
theorem slawChunk_1663 : slawChunk 1663 = true := by decide +kernel
theorem slawC_207 (k : Nat) (h1 : 1656 ≤ k) (h2 : k < 1664) : slawChunk k = true := by
  if e1656 : k = 1656 then subst e1656; exact slawChunk_1656 else
  if e1657 : k = 1657 then subst e1657; exact slawChunk_1657 else
  if e1658 : k = 1658 then subst e1658; exact slawChunk_1658 else
  if e1659 : k = 1659 then subst e1659; exact slawChunk_1659 else
  if e1660 : k = 1660 then subst e1660; exact slawChunk_1660 else
  if e1661 : k = 1661 then subst e1661; exact slawChunk_1661 else
  if e1662 : k = 1662 then subst e1662; exact slawChunk_1662 else
  if e1663 : k = 1663 then subst e1663; exact slawChunk_1663 else
  omega
end D2
