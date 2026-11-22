import Ski.D2Base
import Ski.D2K.S338
/-! Generated.  S-law of D: chunks 2712..2719 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_2712 : slawChunk 2712 = true := by decide +kernel
theorem slawChunk_2713 : slawChunk 2713 = true := by decide +kernel
theorem slawChunk_2714 : slawChunk 2714 = true := by decide +kernel
theorem slawChunk_2715 : slawChunk 2715 = true := by decide +kernel
theorem slawChunk_2716 : slawChunk 2716 = true := by decide +kernel
theorem slawChunk_2717 : slawChunk 2717 = true := by decide +kernel
theorem slawChunk_2718 : slawChunk 2718 = true := by decide +kernel
theorem slawChunk_2719 : slawChunk 2719 = true := by decide +kernel
theorem slawC_339 (k : Nat) (h1 : 2712 ≤ k) (h2 : k < 2720) : slawChunk k = true := by
  if e2712 : k = 2712 then subst e2712; exact slawChunk_2712 else
  if e2713 : k = 2713 then subst e2713; exact slawChunk_2713 else
  if e2714 : k = 2714 then subst e2714; exact slawChunk_2714 else
  if e2715 : k = 2715 then subst e2715; exact slawChunk_2715 else
  if e2716 : k = 2716 then subst e2716; exact slawChunk_2716 else
  if e2717 : k = 2717 then subst e2717; exact slawChunk_2717 else
  if e2718 : k = 2718 then subst e2718; exact slawChunk_2718 else
  if e2719 : k = 2719 then subst e2719; exact slawChunk_2719 else
  omega
end D2
