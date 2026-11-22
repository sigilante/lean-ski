import Ski.D2Base
import Ski.D2K.S335
/-! Generated.  S-law of D: chunks 2688..2695 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_2688 : slawChunk 2688 = true := by decide +kernel
theorem slawChunk_2689 : slawChunk 2689 = true := by decide +kernel
theorem slawChunk_2690 : slawChunk 2690 = true := by decide +kernel
theorem slawChunk_2691 : slawChunk 2691 = true := by decide +kernel
theorem slawChunk_2692 : slawChunk 2692 = true := by decide +kernel
theorem slawChunk_2693 : slawChunk 2693 = true := by decide +kernel
theorem slawChunk_2694 : slawChunk 2694 = true := by decide +kernel
theorem slawChunk_2695 : slawChunk 2695 = true := by decide +kernel
theorem slawC_336 (k : Nat) (h1 : 2688 ≤ k) (h2 : k < 2696) : slawChunk k = true := by
  if e2688 : k = 2688 then subst e2688; exact slawChunk_2688 else
  if e2689 : k = 2689 then subst e2689; exact slawChunk_2689 else
  if e2690 : k = 2690 then subst e2690; exact slawChunk_2690 else
  if e2691 : k = 2691 then subst e2691; exact slawChunk_2691 else
  if e2692 : k = 2692 then subst e2692; exact slawChunk_2692 else
  if e2693 : k = 2693 then subst e2693; exact slawChunk_2693 else
  if e2694 : k = 2694 then subst e2694; exact slawChunk_2694 else
  if e2695 : k = 2695 then subst e2695; exact slawChunk_2695 else
  omega
end D2
