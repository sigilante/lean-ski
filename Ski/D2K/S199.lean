import Ski.D2Base
import Ski.D2K.S198
/-! Generated.  S-law of D: chunks 1592..1599 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_1592 : slawChunk 1592 = true := by decide +kernel
theorem slawChunk_1593 : slawChunk 1593 = true := by decide +kernel
theorem slawChunk_1594 : slawChunk 1594 = true := by decide +kernel
theorem slawChunk_1595 : slawChunk 1595 = true := by decide +kernel
theorem slawChunk_1596 : slawChunk 1596 = true := by decide +kernel
theorem slawChunk_1597 : slawChunk 1597 = true := by decide +kernel
theorem slawChunk_1598 : slawChunk 1598 = true := by decide +kernel
theorem slawChunk_1599 : slawChunk 1599 = true := by decide +kernel
theorem slawC_199 (k : Nat) (h1 : 1592 ≤ k) (h2 : k < 1600) : slawChunk k = true := by
  if e1592 : k = 1592 then subst e1592; exact slawChunk_1592 else
  if e1593 : k = 1593 then subst e1593; exact slawChunk_1593 else
  if e1594 : k = 1594 then subst e1594; exact slawChunk_1594 else
  if e1595 : k = 1595 then subst e1595; exact slawChunk_1595 else
  if e1596 : k = 1596 then subst e1596; exact slawChunk_1596 else
  if e1597 : k = 1597 then subst e1597; exact slawChunk_1597 else
  if e1598 : k = 1598 then subst e1598; exact slawChunk_1598 else
  if e1599 : k = 1599 then subst e1599; exact slawChunk_1599 else
  omega
end D2
