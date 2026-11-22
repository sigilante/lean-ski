import Ski.D2Base
import Ski.D2K.S316
/-! Generated.  S-law of D: chunks 2536..2543 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_2536 : slawChunk 2536 = true := by decide +kernel
theorem slawChunk_2537 : slawChunk 2537 = true := by decide +kernel
theorem slawChunk_2538 : slawChunk 2538 = true := by decide +kernel
theorem slawChunk_2539 : slawChunk 2539 = true := by decide +kernel
theorem slawChunk_2540 : slawChunk 2540 = true := by decide +kernel
theorem slawChunk_2541 : slawChunk 2541 = true := by decide +kernel
theorem slawChunk_2542 : slawChunk 2542 = true := by decide +kernel
theorem slawChunk_2543 : slawChunk 2543 = true := by decide +kernel
theorem slawC_317 (k : Nat) (h1 : 2536 ≤ k) (h2 : k < 2544) : slawChunk k = true := by
  if e2536 : k = 2536 then subst e2536; exact slawChunk_2536 else
  if e2537 : k = 2537 then subst e2537; exact slawChunk_2537 else
  if e2538 : k = 2538 then subst e2538; exact slawChunk_2538 else
  if e2539 : k = 2539 then subst e2539; exact slawChunk_2539 else
  if e2540 : k = 2540 then subst e2540; exact slawChunk_2540 else
  if e2541 : k = 2541 then subst e2541; exact slawChunk_2541 else
  if e2542 : k = 2542 then subst e2542; exact slawChunk_2542 else
  if e2543 : k = 2543 then subst e2543; exact slawChunk_2543 else
  omega
end D2
