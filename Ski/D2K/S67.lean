import Ski.D2Base
import Ski.D2K.S66
/-! Generated.  S-law of D: chunks 536..543 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_536 : slawChunk 536 = true := by decide +kernel
theorem slawChunk_537 : slawChunk 537 = true := by decide +kernel
theorem slawChunk_538 : slawChunk 538 = true := by decide +kernel
theorem slawChunk_539 : slawChunk 539 = true := by decide +kernel
theorem slawChunk_540 : slawChunk 540 = true := by decide +kernel
theorem slawChunk_541 : slawChunk 541 = true := by decide +kernel
theorem slawChunk_542 : slawChunk 542 = true := by decide +kernel
theorem slawChunk_543 : slawChunk 543 = true := by decide +kernel
theorem slawC_67 (k : Nat) (h1 : 536 ≤ k) (h2 : k < 544) : slawChunk k = true := by
  if e536 : k = 536 then subst e536; exact slawChunk_536 else
  if e537 : k = 537 then subst e537; exact slawChunk_537 else
  if e538 : k = 538 then subst e538; exact slawChunk_538 else
  if e539 : k = 539 then subst e539; exact slawChunk_539 else
  if e540 : k = 540 then subst e540; exact slawChunk_540 else
  if e541 : k = 541 then subst e541; exact slawChunk_541 else
  if e542 : k = 542 then subst e542; exact slawChunk_542 else
  if e543 : k = 543 then subst e543; exact slawChunk_543 else
  omega
end D2
