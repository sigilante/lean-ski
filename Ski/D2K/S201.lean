import Ski.D2Base
import Ski.D2K.S200
/-! Generated.  S-law of D: chunks 1608..1615 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_1608 : slawChunk 1608 = true := by decide +kernel
theorem slawChunk_1609 : slawChunk 1609 = true := by decide +kernel
theorem slawChunk_1610 : slawChunk 1610 = true := by decide +kernel
theorem slawChunk_1611 : slawChunk 1611 = true := by decide +kernel
theorem slawChunk_1612 : slawChunk 1612 = true := by decide +kernel
theorem slawChunk_1613 : slawChunk 1613 = true := by decide +kernel
theorem slawChunk_1614 : slawChunk 1614 = true := by decide +kernel
theorem slawChunk_1615 : slawChunk 1615 = true := by decide +kernel
theorem slawC_201 (k : Nat) (h1 : 1608 ≤ k) (h2 : k < 1616) : slawChunk k = true := by
  if e1608 : k = 1608 then subst e1608; exact slawChunk_1608 else
  if e1609 : k = 1609 then subst e1609; exact slawChunk_1609 else
  if e1610 : k = 1610 then subst e1610; exact slawChunk_1610 else
  if e1611 : k = 1611 then subst e1611; exact slawChunk_1611 else
  if e1612 : k = 1612 then subst e1612; exact slawChunk_1612 else
  if e1613 : k = 1613 then subst e1613; exact slawChunk_1613 else
  if e1614 : k = 1614 then subst e1614; exact slawChunk_1614 else
  if e1615 : k = 1615 then subst e1615; exact slawChunk_1615 else
  omega
end D2
