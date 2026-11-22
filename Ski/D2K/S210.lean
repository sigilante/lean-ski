import Ski.D2Base
import Ski.D2K.S209
/-! Generated.  S-law of D: chunks 1680..1687 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_1680 : slawChunk 1680 = true := by decide +kernel
theorem slawChunk_1681 : slawChunk 1681 = true := by decide +kernel
theorem slawChunk_1682 : slawChunk 1682 = true := by decide +kernel
theorem slawChunk_1683 : slawChunk 1683 = true := by decide +kernel
theorem slawChunk_1684 : slawChunk 1684 = true := by decide +kernel
theorem slawChunk_1685 : slawChunk 1685 = true := by decide +kernel
theorem slawChunk_1686 : slawChunk 1686 = true := by decide +kernel
theorem slawChunk_1687 : slawChunk 1687 = true := by decide +kernel
theorem slawC_210 (k : Nat) (h1 : 1680 ≤ k) (h2 : k < 1688) : slawChunk k = true := by
  if e1680 : k = 1680 then subst e1680; exact slawChunk_1680 else
  if e1681 : k = 1681 then subst e1681; exact slawChunk_1681 else
  if e1682 : k = 1682 then subst e1682; exact slawChunk_1682 else
  if e1683 : k = 1683 then subst e1683; exact slawChunk_1683 else
  if e1684 : k = 1684 then subst e1684; exact slawChunk_1684 else
  if e1685 : k = 1685 then subst e1685; exact slawChunk_1685 else
  if e1686 : k = 1686 then subst e1686; exact slawChunk_1686 else
  if e1687 : k = 1687 then subst e1687; exact slawChunk_1687 else
  omega
end D2
