import Ski.D2Base
import Ski.D2K.S205
/-! Generated.  S-law of D: chunks 1648..1655 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_1648 : slawChunk 1648 = true := by decide +kernel
theorem slawChunk_1649 : slawChunk 1649 = true := by decide +kernel
theorem slawChunk_1650 : slawChunk 1650 = true := by decide +kernel
theorem slawChunk_1651 : slawChunk 1651 = true := by decide +kernel
theorem slawChunk_1652 : slawChunk 1652 = true := by decide +kernel
theorem slawChunk_1653 : slawChunk 1653 = true := by decide +kernel
theorem slawChunk_1654 : slawChunk 1654 = true := by decide +kernel
theorem slawChunk_1655 : slawChunk 1655 = true := by decide +kernel
theorem slawC_206 (k : Nat) (h1 : 1648 ≤ k) (h2 : k < 1656) : slawChunk k = true := by
  if e1648 : k = 1648 then subst e1648; exact slawChunk_1648 else
  if e1649 : k = 1649 then subst e1649; exact slawChunk_1649 else
  if e1650 : k = 1650 then subst e1650; exact slawChunk_1650 else
  if e1651 : k = 1651 then subst e1651; exact slawChunk_1651 else
  if e1652 : k = 1652 then subst e1652; exact slawChunk_1652 else
  if e1653 : k = 1653 then subst e1653; exact slawChunk_1653 else
  if e1654 : k = 1654 then subst e1654; exact slawChunk_1654 else
  if e1655 : k = 1655 then subst e1655; exact slawChunk_1655 else
  omega
end D2
