import Ski.D2Base
import Ski.D2K.S208
/-! Generated.  S-law of D: chunks 1672..1679 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_1672 : slawChunk 1672 = true := by decide +kernel
theorem slawChunk_1673 : slawChunk 1673 = true := by decide +kernel
theorem slawChunk_1674 : slawChunk 1674 = true := by decide +kernel
theorem slawChunk_1675 : slawChunk 1675 = true := by decide +kernel
theorem slawChunk_1676 : slawChunk 1676 = true := by decide +kernel
theorem slawChunk_1677 : slawChunk 1677 = true := by decide +kernel
theorem slawChunk_1678 : slawChunk 1678 = true := by decide +kernel
theorem slawChunk_1679 : slawChunk 1679 = true := by decide +kernel
theorem slawC_209 (k : Nat) (h1 : 1672 ≤ k) (h2 : k < 1680) : slawChunk k = true := by
  if e1672 : k = 1672 then subst e1672; exact slawChunk_1672 else
  if e1673 : k = 1673 then subst e1673; exact slawChunk_1673 else
  if e1674 : k = 1674 then subst e1674; exact slawChunk_1674 else
  if e1675 : k = 1675 then subst e1675; exact slawChunk_1675 else
  if e1676 : k = 1676 then subst e1676; exact slawChunk_1676 else
  if e1677 : k = 1677 then subst e1677; exact slawChunk_1677 else
  if e1678 : k = 1678 then subst e1678; exact slawChunk_1678 else
  if e1679 : k = 1679 then subst e1679; exact slawChunk_1679 else
  omega
end D2
