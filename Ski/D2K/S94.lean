import Ski.D2Base
import Ski.D2K.S93
/-! Generated.  S-law of D: chunks 752..759 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_752 : slawChunk 752 = true := by decide +kernel
theorem slawChunk_753 : slawChunk 753 = true := by decide +kernel
theorem slawChunk_754 : slawChunk 754 = true := by decide +kernel
theorem slawChunk_755 : slawChunk 755 = true := by decide +kernel
theorem slawChunk_756 : slawChunk 756 = true := by decide +kernel
theorem slawChunk_757 : slawChunk 757 = true := by decide +kernel
theorem slawChunk_758 : slawChunk 758 = true := by decide +kernel
theorem slawChunk_759 : slawChunk 759 = true := by decide +kernel
theorem slawC_94 (k : Nat) (h1 : 752 ≤ k) (h2 : k < 760) : slawChunk k = true := by
  if e752 : k = 752 then subst e752; exact slawChunk_752 else
  if e753 : k = 753 then subst e753; exact slawChunk_753 else
  if e754 : k = 754 then subst e754; exact slawChunk_754 else
  if e755 : k = 755 then subst e755; exact slawChunk_755 else
  if e756 : k = 756 then subst e756; exact slawChunk_756 else
  if e757 : k = 757 then subst e757; exact slawChunk_757 else
  if e758 : k = 758 then subst e758; exact slawChunk_758 else
  if e759 : k = 759 then subst e759; exact slawChunk_759 else
  omega
end D2
