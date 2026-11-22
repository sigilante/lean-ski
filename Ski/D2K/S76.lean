import Ski.D2Base
import Ski.D2K.S75
/-! Generated.  S-law of D: chunks 608..615 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_608 : slawChunk 608 = true := by decide +kernel
theorem slawChunk_609 : slawChunk 609 = true := by decide +kernel
theorem slawChunk_610 : slawChunk 610 = true := by decide +kernel
theorem slawChunk_611 : slawChunk 611 = true := by decide +kernel
theorem slawChunk_612 : slawChunk 612 = true := by decide +kernel
theorem slawChunk_613 : slawChunk 613 = true := by decide +kernel
theorem slawChunk_614 : slawChunk 614 = true := by decide +kernel
theorem slawChunk_615 : slawChunk 615 = true := by decide +kernel
theorem slawC_76 (k : Nat) (h1 : 608 ≤ k) (h2 : k < 616) : slawChunk k = true := by
  if e608 : k = 608 then subst e608; exact slawChunk_608 else
  if e609 : k = 609 then subst e609; exact slawChunk_609 else
  if e610 : k = 610 then subst e610; exact slawChunk_610 else
  if e611 : k = 611 then subst e611; exact slawChunk_611 else
  if e612 : k = 612 then subst e612; exact slawChunk_612 else
  if e613 : k = 613 then subst e613; exact slawChunk_613 else
  if e614 : k = 614 then subst e614; exact slawChunk_614 else
  if e615 : k = 615 then subst e615; exact slawChunk_615 else
  omega
end D2
