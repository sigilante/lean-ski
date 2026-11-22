import Ski.D2Base
import Ski.D2K.S64
/-! Generated.  S-law of D: chunks 520..527 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_520 : slawChunk 520 = true := by decide +kernel
theorem slawChunk_521 : slawChunk 521 = true := by decide +kernel
theorem slawChunk_522 : slawChunk 522 = true := by decide +kernel
theorem slawChunk_523 : slawChunk 523 = true := by decide +kernel
theorem slawChunk_524 : slawChunk 524 = true := by decide +kernel
theorem slawChunk_525 : slawChunk 525 = true := by decide +kernel
theorem slawChunk_526 : slawChunk 526 = true := by decide +kernel
theorem slawChunk_527 : slawChunk 527 = true := by decide +kernel
theorem slawC_65 (k : Nat) (h1 : 520 ≤ k) (h2 : k < 528) : slawChunk k = true := by
  if e520 : k = 520 then subst e520; exact slawChunk_520 else
  if e521 : k = 521 then subst e521; exact slawChunk_521 else
  if e522 : k = 522 then subst e522; exact slawChunk_522 else
  if e523 : k = 523 then subst e523; exact slawChunk_523 else
  if e524 : k = 524 then subst e524; exact slawChunk_524 else
  if e525 : k = 525 then subst e525; exact slawChunk_525 else
  if e526 : k = 526 then subst e526; exact slawChunk_526 else
  if e527 : k = 527 then subst e527; exact slawChunk_527 else
  omega
end D2
