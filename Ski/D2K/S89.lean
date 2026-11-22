import Ski.D2Base
import Ski.D2K.S88
/-! Generated.  S-law of D: chunks 712..719 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_712 : slawChunk 712 = true := by decide +kernel
theorem slawChunk_713 : slawChunk 713 = true := by decide +kernel
theorem slawChunk_714 : slawChunk 714 = true := by decide +kernel
theorem slawChunk_715 : slawChunk 715 = true := by decide +kernel
theorem slawChunk_716 : slawChunk 716 = true := by decide +kernel
theorem slawChunk_717 : slawChunk 717 = true := by decide +kernel
theorem slawChunk_718 : slawChunk 718 = true := by decide +kernel
theorem slawChunk_719 : slawChunk 719 = true := by decide +kernel
theorem slawC_89 (k : Nat) (h1 : 712 ≤ k) (h2 : k < 720) : slawChunk k = true := by
  if e712 : k = 712 then subst e712; exact slawChunk_712 else
  if e713 : k = 713 then subst e713; exact slawChunk_713 else
  if e714 : k = 714 then subst e714; exact slawChunk_714 else
  if e715 : k = 715 then subst e715; exact slawChunk_715 else
  if e716 : k = 716 then subst e716; exact slawChunk_716 else
  if e717 : k = 717 then subst e717; exact slawChunk_717 else
  if e718 : k = 718 then subst e718; exact slawChunk_718 else
  if e719 : k = 719 then subst e719; exact slawChunk_719 else
  omega
end D2
