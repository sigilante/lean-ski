import Ski.D2Base
import Ski.D2K.S197
/-! Generated.  S-law of D: chunks 1584..1591 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_1584 : slawChunk 1584 = true := by decide +kernel
theorem slawChunk_1585 : slawChunk 1585 = true := by decide +kernel
theorem slawChunk_1586 : slawChunk 1586 = true := by decide +kernel
theorem slawChunk_1587 : slawChunk 1587 = true := by decide +kernel
theorem slawChunk_1588 : slawChunk 1588 = true := by decide +kernel
theorem slawChunk_1589 : slawChunk 1589 = true := by decide +kernel
theorem slawChunk_1590 : slawChunk 1590 = true := by decide +kernel
theorem slawChunk_1591 : slawChunk 1591 = true := by decide +kernel
theorem slawC_198 (k : Nat) (h1 : 1584 ≤ k) (h2 : k < 1592) : slawChunk k = true := by
  if e1584 : k = 1584 then subst e1584; exact slawChunk_1584 else
  if e1585 : k = 1585 then subst e1585; exact slawChunk_1585 else
  if e1586 : k = 1586 then subst e1586; exact slawChunk_1586 else
  if e1587 : k = 1587 then subst e1587; exact slawChunk_1587 else
  if e1588 : k = 1588 then subst e1588; exact slawChunk_1588 else
  if e1589 : k = 1589 then subst e1589; exact slawChunk_1589 else
  if e1590 : k = 1590 then subst e1590; exact slawChunk_1590 else
  if e1591 : k = 1591 then subst e1591; exact slawChunk_1591 else
  omega
end D2
