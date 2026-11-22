import Ski.D2Base
import Ski.D2K.S328
/-! Generated.  S-law of D: chunks 2632..2639 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_2632 : slawChunk 2632 = true := by decide +kernel
theorem slawChunk_2633 : slawChunk 2633 = true := by decide +kernel
theorem slawChunk_2634 : slawChunk 2634 = true := by decide +kernel
theorem slawChunk_2635 : slawChunk 2635 = true := by decide +kernel
theorem slawChunk_2636 : slawChunk 2636 = true := by decide +kernel
theorem slawChunk_2637 : slawChunk 2637 = true := by decide +kernel
theorem slawChunk_2638 : slawChunk 2638 = true := by decide +kernel
theorem slawChunk_2639 : slawChunk 2639 = true := by decide +kernel
theorem slawC_329 (k : Nat) (h1 : 2632 ≤ k) (h2 : k < 2640) : slawChunk k = true := by
  if e2632 : k = 2632 then subst e2632; exact slawChunk_2632 else
  if e2633 : k = 2633 then subst e2633; exact slawChunk_2633 else
  if e2634 : k = 2634 then subst e2634; exact slawChunk_2634 else
  if e2635 : k = 2635 then subst e2635; exact slawChunk_2635 else
  if e2636 : k = 2636 then subst e2636; exact slawChunk_2636 else
  if e2637 : k = 2637 then subst e2637; exact slawChunk_2637 else
  if e2638 : k = 2638 then subst e2638; exact slawChunk_2638 else
  if e2639 : k = 2639 then subst e2639; exact slawChunk_2639 else
  omega
end D2
