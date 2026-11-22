import Ski.D2Base
import Ski.D2K.S69
/-! Generated.  S-law of D: chunks 560..567 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_560 : slawChunk 560 = true := by decide +kernel
theorem slawChunk_561 : slawChunk 561 = true := by decide +kernel
theorem slawChunk_562 : slawChunk 562 = true := by decide +kernel
theorem slawChunk_563 : slawChunk 563 = true := by decide +kernel
theorem slawChunk_564 : slawChunk 564 = true := by decide +kernel
theorem slawChunk_565 : slawChunk 565 = true := by decide +kernel
theorem slawChunk_566 : slawChunk 566 = true := by decide +kernel
theorem slawChunk_567 : slawChunk 567 = true := by decide +kernel
theorem slawC_70 (k : Nat) (h1 : 560 ≤ k) (h2 : k < 568) : slawChunk k = true := by
  if e560 : k = 560 then subst e560; exact slawChunk_560 else
  if e561 : k = 561 then subst e561; exact slawChunk_561 else
  if e562 : k = 562 then subst e562; exact slawChunk_562 else
  if e563 : k = 563 then subst e563; exact slawChunk_563 else
  if e564 : k = 564 then subst e564; exact slawChunk_564 else
  if e565 : k = 565 then subst e565; exact slawChunk_565 else
  if e566 : k = 566 then subst e566; exact slawChunk_566 else
  if e567 : k = 567 then subst e567; exact slawChunk_567 else
  omega
end D2
