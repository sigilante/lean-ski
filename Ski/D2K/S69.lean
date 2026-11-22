import Ski.D2Base
import Ski.D2K.S68
/-! Generated.  S-law of D: chunks 552..559 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_552 : slawChunk 552 = true := by decide +kernel
theorem slawChunk_553 : slawChunk 553 = true := by decide +kernel
theorem slawChunk_554 : slawChunk 554 = true := by decide +kernel
theorem slawChunk_555 : slawChunk 555 = true := by decide +kernel
theorem slawChunk_556 : slawChunk 556 = true := by decide +kernel
theorem slawChunk_557 : slawChunk 557 = true := by decide +kernel
theorem slawChunk_558 : slawChunk 558 = true := by decide +kernel
theorem slawChunk_559 : slawChunk 559 = true := by decide +kernel
theorem slawC_69 (k : Nat) (h1 : 552 ≤ k) (h2 : k < 560) : slawChunk k = true := by
  if e552 : k = 552 then subst e552; exact slawChunk_552 else
  if e553 : k = 553 then subst e553; exact slawChunk_553 else
  if e554 : k = 554 then subst e554; exact slawChunk_554 else
  if e555 : k = 555 then subst e555; exact slawChunk_555 else
  if e556 : k = 556 then subst e556; exact slawChunk_556 else
  if e557 : k = 557 then subst e557; exact slawChunk_557 else
  if e558 : k = 558 then subst e558; exact slawChunk_558 else
  if e559 : k = 559 then subst e559; exact slawChunk_559 else
  omega
end D2
