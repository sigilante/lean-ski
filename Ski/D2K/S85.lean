import Ski.D2Base
import Ski.D2K.S84
/-! Generated.  S-law of D: chunks 680..687 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_680 : slawChunk 680 = true := by decide +kernel
theorem slawChunk_681 : slawChunk 681 = true := by decide +kernel
theorem slawChunk_682 : slawChunk 682 = true := by decide +kernel
theorem slawChunk_683 : slawChunk 683 = true := by decide +kernel
theorem slawChunk_684 : slawChunk 684 = true := by decide +kernel
theorem slawChunk_685 : slawChunk 685 = true := by decide +kernel
theorem slawChunk_686 : slawChunk 686 = true := by decide +kernel
theorem slawChunk_687 : slawChunk 687 = true := by decide +kernel
theorem slawC_85 (k : Nat) (h1 : 680 ≤ k) (h2 : k < 688) : slawChunk k = true := by
  if e680 : k = 680 then subst e680; exact slawChunk_680 else
  if e681 : k = 681 then subst e681; exact slawChunk_681 else
  if e682 : k = 682 then subst e682; exact slawChunk_682 else
  if e683 : k = 683 then subst e683; exact slawChunk_683 else
  if e684 : k = 684 then subst e684; exact slawChunk_684 else
  if e685 : k = 685 then subst e685; exact slawChunk_685 else
  if e686 : k = 686 then subst e686; exact slawChunk_686 else
  if e687 : k = 687 then subst e687; exact slawChunk_687 else
  omega
end D2
