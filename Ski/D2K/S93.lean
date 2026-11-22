import Ski.D2Base
import Ski.D2K.S92
/-! Generated.  S-law of D: chunks 744..751 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_744 : slawChunk 744 = true := by decide +kernel
theorem slawChunk_745 : slawChunk 745 = true := by decide +kernel
theorem slawChunk_746 : slawChunk 746 = true := by decide +kernel
theorem slawChunk_747 : slawChunk 747 = true := by decide +kernel
theorem slawChunk_748 : slawChunk 748 = true := by decide +kernel
theorem slawChunk_749 : slawChunk 749 = true := by decide +kernel
theorem slawChunk_750 : slawChunk 750 = true := by decide +kernel
theorem slawChunk_751 : slawChunk 751 = true := by decide +kernel
theorem slawC_93 (k : Nat) (h1 : 744 ≤ k) (h2 : k < 752) : slawChunk k = true := by
  if e744 : k = 744 then subst e744; exact slawChunk_744 else
  if e745 : k = 745 then subst e745; exact slawChunk_745 else
  if e746 : k = 746 then subst e746; exact slawChunk_746 else
  if e747 : k = 747 then subst e747; exact slawChunk_747 else
  if e748 : k = 748 then subst e748; exact slawChunk_748 else
  if e749 : k = 749 then subst e749; exact slawChunk_749 else
  if e750 : k = 750 then subst e750; exact slawChunk_750 else
  if e751 : k = 751 then subst e751; exact slawChunk_751 else
  omega
end D2
