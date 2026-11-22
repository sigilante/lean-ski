import Ski.D2Base
import Ski.D2K.S325
/-! Generated.  S-law of D: chunks 2608..2615 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_2608 : slawChunk 2608 = true := by decide +kernel
theorem slawChunk_2609 : slawChunk 2609 = true := by decide +kernel
theorem slawChunk_2610 : slawChunk 2610 = true := by decide +kernel
theorem slawChunk_2611 : slawChunk 2611 = true := by decide +kernel
theorem slawChunk_2612 : slawChunk 2612 = true := by decide +kernel
theorem slawChunk_2613 : slawChunk 2613 = true := by decide +kernel
theorem slawChunk_2614 : slawChunk 2614 = true := by decide +kernel
theorem slawChunk_2615 : slawChunk 2615 = true := by decide +kernel
theorem slawC_326 (k : Nat) (h1 : 2608 ≤ k) (h2 : k < 2616) : slawChunk k = true := by
  if e2608 : k = 2608 then subst e2608; exact slawChunk_2608 else
  if e2609 : k = 2609 then subst e2609; exact slawChunk_2609 else
  if e2610 : k = 2610 then subst e2610; exact slawChunk_2610 else
  if e2611 : k = 2611 then subst e2611; exact slawChunk_2611 else
  if e2612 : k = 2612 then subst e2612; exact slawChunk_2612 else
  if e2613 : k = 2613 then subst e2613; exact slawChunk_2613 else
  if e2614 : k = 2614 then subst e2614; exact slawChunk_2614 else
  if e2615 : k = 2615 then subst e2615; exact slawChunk_2615 else
  omega
end D2
