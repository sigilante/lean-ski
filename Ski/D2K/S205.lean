import Ski.D2Base
import Ski.D2K.S204
/-! Generated.  S-law of D: chunks 1640..1647 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_1640 : slawChunk 1640 = true := by decide +kernel
theorem slawChunk_1641 : slawChunk 1641 = true := by decide +kernel
theorem slawChunk_1642 : slawChunk 1642 = true := by decide +kernel
theorem slawChunk_1643 : slawChunk 1643 = true := by decide +kernel
theorem slawChunk_1644 : slawChunk 1644 = true := by decide +kernel
theorem slawChunk_1645 : slawChunk 1645 = true := by decide +kernel
theorem slawChunk_1646 : slawChunk 1646 = true := by decide +kernel
theorem slawChunk_1647 : slawChunk 1647 = true := by decide +kernel
theorem slawC_205 (k : Nat) (h1 : 1640 ≤ k) (h2 : k < 1648) : slawChunk k = true := by
  if e1640 : k = 1640 then subst e1640; exact slawChunk_1640 else
  if e1641 : k = 1641 then subst e1641; exact slawChunk_1641 else
  if e1642 : k = 1642 then subst e1642; exact slawChunk_1642 else
  if e1643 : k = 1643 then subst e1643; exact slawChunk_1643 else
  if e1644 : k = 1644 then subst e1644; exact slawChunk_1644 else
  if e1645 : k = 1645 then subst e1645; exact slawChunk_1645 else
  if e1646 : k = 1646 then subst e1646; exact slawChunk_1646 else
  if e1647 : k = 1647 then subst e1647; exact slawChunk_1647 else
  omega
end D2
