import Ski.D2Base
import Ski.D2K.S48
/-! Generated.  S-law of D: chunks 392..399 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_392 : slawChunk 392 = true := by decide +kernel
theorem slawChunk_393 : slawChunk 393 = true := by decide +kernel
theorem slawChunk_394 : slawChunk 394 = true := by decide +kernel
theorem slawChunk_395 : slawChunk 395 = true := by decide +kernel
theorem slawChunk_396 : slawChunk 396 = true := by decide +kernel
theorem slawChunk_397 : slawChunk 397 = true := by decide +kernel
theorem slawChunk_398 : slawChunk 398 = true := by decide +kernel
theorem slawChunk_399 : slawChunk 399 = true := by decide +kernel
theorem slawC_49 (k : Nat) (h1 : 392 ≤ k) (h2 : k < 400) : slawChunk k = true := by
  if e392 : k = 392 then subst e392; exact slawChunk_392 else
  if e393 : k = 393 then subst e393; exact slawChunk_393 else
  if e394 : k = 394 then subst e394; exact slawChunk_394 else
  if e395 : k = 395 then subst e395; exact slawChunk_395 else
  if e396 : k = 396 then subst e396; exact slawChunk_396 else
  if e397 : k = 397 then subst e397; exact slawChunk_397 else
  if e398 : k = 398 then subst e398; exact slawChunk_398 else
  if e399 : k = 399 then subst e399; exact slawChunk_399 else
  omega
end D2
