import Ski.D2Base
import Ski.D2K.S214
/-! Generated.  S-law of D: chunks 1720..1727 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_1720 : slawChunk 1720 = true := by decide +kernel
theorem slawChunk_1721 : slawChunk 1721 = true := by decide +kernel
theorem slawChunk_1722 : slawChunk 1722 = true := by decide +kernel
theorem slawChunk_1723 : slawChunk 1723 = true := by decide +kernel
theorem slawChunk_1724 : slawChunk 1724 = true := by decide +kernel
theorem slawChunk_1725 : slawChunk 1725 = true := by decide +kernel
theorem slawChunk_1726 : slawChunk 1726 = true := by decide +kernel
theorem slawChunk_1727 : slawChunk 1727 = true := by decide +kernel
theorem slawC_215 (k : Nat) (h1 : 1720 ≤ k) (h2 : k < 1728) : slawChunk k = true := by
  if e1720 : k = 1720 then subst e1720; exact slawChunk_1720 else
  if e1721 : k = 1721 then subst e1721; exact slawChunk_1721 else
  if e1722 : k = 1722 then subst e1722; exact slawChunk_1722 else
  if e1723 : k = 1723 then subst e1723; exact slawChunk_1723 else
  if e1724 : k = 1724 then subst e1724; exact slawChunk_1724 else
  if e1725 : k = 1725 then subst e1725; exact slawChunk_1725 else
  if e1726 : k = 1726 then subst e1726; exact slawChunk_1726 else
  if e1727 : k = 1727 then subst e1727; exact slawChunk_1727 else
  omega
end D2
