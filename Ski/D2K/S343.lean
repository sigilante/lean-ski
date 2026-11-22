import Ski.D2Base
import Ski.D2K.S342
/-! Generated.  S-law of D: chunks 2744..2751 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_2744 : slawChunk 2744 = true := by decide +kernel
theorem slawChunk_2745 : slawChunk 2745 = true := by decide +kernel
theorem slawChunk_2746 : slawChunk 2746 = true := by decide +kernel
theorem slawChunk_2747 : slawChunk 2747 = true := by decide +kernel
theorem slawChunk_2748 : slawChunk 2748 = true := by decide +kernel
theorem slawChunk_2749 : slawChunk 2749 = true := by decide +kernel
theorem slawChunk_2750 : slawChunk 2750 = true := by decide +kernel
theorem slawChunk_2751 : slawChunk 2751 = true := by decide +kernel
theorem slawC_343 (k : Nat) (h1 : 2744 ≤ k) (h2 : k < 2752) : slawChunk k = true := by
  if e2744 : k = 2744 then subst e2744; exact slawChunk_2744 else
  if e2745 : k = 2745 then subst e2745; exact slawChunk_2745 else
  if e2746 : k = 2746 then subst e2746; exact slawChunk_2746 else
  if e2747 : k = 2747 then subst e2747; exact slawChunk_2747 else
  if e2748 : k = 2748 then subst e2748; exact slawChunk_2748 else
  if e2749 : k = 2749 then subst e2749; exact slawChunk_2749 else
  if e2750 : k = 2750 then subst e2750; exact slawChunk_2750 else
  if e2751 : k = 2751 then subst e2751; exact slawChunk_2751 else
  omega
end D2
