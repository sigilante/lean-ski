import Ski.D2Base
import Ski.D2K.S319
/-! Generated.  S-law of D: chunks 2560..2567 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_2560 : slawChunk 2560 = true := by decide +kernel
theorem slawChunk_2561 : slawChunk 2561 = true := by decide +kernel
theorem slawChunk_2562 : slawChunk 2562 = true := by decide +kernel
theorem slawChunk_2563 : slawChunk 2563 = true := by decide +kernel
theorem slawChunk_2564 : slawChunk 2564 = true := by decide +kernel
theorem slawChunk_2565 : slawChunk 2565 = true := by decide +kernel
theorem slawChunk_2566 : slawChunk 2566 = true := by decide +kernel
theorem slawChunk_2567 : slawChunk 2567 = true := by decide +kernel
theorem slawC_320 (k : Nat) (h1 : 2560 ≤ k) (h2 : k < 2568) : slawChunk k = true := by
  if e2560 : k = 2560 then subst e2560; exact slawChunk_2560 else
  if e2561 : k = 2561 then subst e2561; exact slawChunk_2561 else
  if e2562 : k = 2562 then subst e2562; exact slawChunk_2562 else
  if e2563 : k = 2563 then subst e2563; exact slawChunk_2563 else
  if e2564 : k = 2564 then subst e2564; exact slawChunk_2564 else
  if e2565 : k = 2565 then subst e2565; exact slawChunk_2565 else
  if e2566 : k = 2566 then subst e2566; exact slawChunk_2566 else
  if e2567 : k = 2567 then subst e2567; exact slawChunk_2567 else
  omega
end D2
