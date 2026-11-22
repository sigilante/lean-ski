import Ski.D2Base
import Ski.D2K.S80
/-! Generated.  S-law of D: chunks 648..655 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_648 : slawChunk 648 = true := by decide +kernel
theorem slawChunk_649 : slawChunk 649 = true := by decide +kernel
theorem slawChunk_650 : slawChunk 650 = true := by decide +kernel
theorem slawChunk_651 : slawChunk 651 = true := by decide +kernel
theorem slawChunk_652 : slawChunk 652 = true := by decide +kernel
theorem slawChunk_653 : slawChunk 653 = true := by decide +kernel
theorem slawChunk_654 : slawChunk 654 = true := by decide +kernel
theorem slawChunk_655 : slawChunk 655 = true := by decide +kernel
theorem slawC_81 (k : Nat) (h1 : 648 ≤ k) (h2 : k < 656) : slawChunk k = true := by
  if e648 : k = 648 then subst e648; exact slawChunk_648 else
  if e649 : k = 649 then subst e649; exact slawChunk_649 else
  if e650 : k = 650 then subst e650; exact slawChunk_650 else
  if e651 : k = 651 then subst e651; exact slawChunk_651 else
  if e652 : k = 652 then subst e652; exact slawChunk_652 else
  if e653 : k = 653 then subst e653; exact slawChunk_653 else
  if e654 : k = 654 then subst e654; exact slawChunk_654 else
  if e655 : k = 655 then subst e655; exact slawChunk_655 else
  omega
end D2
