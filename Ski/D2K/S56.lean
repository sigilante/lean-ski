import Ski.D2Base
import Ski.D2K.S55
/-! Generated.  S-law of D: chunks 448..455 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_448 : slawChunk 448 = true := by decide +kernel
theorem slawChunk_449 : slawChunk 449 = true := by decide +kernel
theorem slawChunk_450 : slawChunk 450 = true := by decide +kernel
theorem slawChunk_451 : slawChunk 451 = true := by decide +kernel
theorem slawChunk_452 : slawChunk 452 = true := by decide +kernel
theorem slawChunk_453 : slawChunk 453 = true := by decide +kernel
theorem slawChunk_454 : slawChunk 454 = true := by decide +kernel
theorem slawChunk_455 : slawChunk 455 = true := by decide +kernel
theorem slawC_56 (k : Nat) (h1 : 448 ≤ k) (h2 : k < 456) : slawChunk k = true := by
  if e448 : k = 448 then subst e448; exact slawChunk_448 else
  if e449 : k = 449 then subst e449; exact slawChunk_449 else
  if e450 : k = 450 then subst e450; exact slawChunk_450 else
  if e451 : k = 451 then subst e451; exact slawChunk_451 else
  if e452 : k = 452 then subst e452; exact slawChunk_452 else
  if e453 : k = 453 then subst e453; exact slawChunk_453 else
  if e454 : k = 454 then subst e454; exact slawChunk_454 else
  if e455 : k = 455 then subst e455; exact slawChunk_455 else
  omega
end D2
