import Ski.D2Base
import Ski.D2K.S311
/-! Generated.  S-law of D: chunks 2496..2503 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_2496 : slawChunk 2496 = true := by decide +kernel
theorem slawChunk_2497 : slawChunk 2497 = true := by decide +kernel
theorem slawChunk_2498 : slawChunk 2498 = true := by decide +kernel
theorem slawChunk_2499 : slawChunk 2499 = true := by decide +kernel
theorem slawChunk_2500 : slawChunk 2500 = true := by decide +kernel
theorem slawChunk_2501 : slawChunk 2501 = true := by decide +kernel
theorem slawChunk_2502 : slawChunk 2502 = true := by decide +kernel
theorem slawChunk_2503 : slawChunk 2503 = true := by decide +kernel
theorem slawC_312 (k : Nat) (h1 : 2496 ≤ k) (h2 : k < 2504) : slawChunk k = true := by
  if e2496 : k = 2496 then subst e2496; exact slawChunk_2496 else
  if e2497 : k = 2497 then subst e2497; exact slawChunk_2497 else
  if e2498 : k = 2498 then subst e2498; exact slawChunk_2498 else
  if e2499 : k = 2499 then subst e2499; exact slawChunk_2499 else
  if e2500 : k = 2500 then subst e2500; exact slawChunk_2500 else
  if e2501 : k = 2501 then subst e2501; exact slawChunk_2501 else
  if e2502 : k = 2502 then subst e2502; exact slawChunk_2502 else
  if e2503 : k = 2503 then subst e2503; exact slawChunk_2503 else
  omega
end D2
