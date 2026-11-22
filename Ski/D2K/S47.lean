import Ski.D2Base
import Ski.D2K.S46
/-! Generated.  S-law of D: chunks 376..383 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_376 : slawChunk 376 = true := by decide +kernel
theorem slawChunk_377 : slawChunk 377 = true := by decide +kernel
theorem slawChunk_378 : slawChunk 378 = true := by decide +kernel
theorem slawChunk_379 : slawChunk 379 = true := by decide +kernel
theorem slawChunk_380 : slawChunk 380 = true := by decide +kernel
theorem slawChunk_381 : slawChunk 381 = true := by decide +kernel
theorem slawChunk_382 : slawChunk 382 = true := by decide +kernel
theorem slawChunk_383 : slawChunk 383 = true := by decide +kernel
theorem slawC_47 (k : Nat) (h1 : 376 ≤ k) (h2 : k < 384) : slawChunk k = true := by
  if e376 : k = 376 then subst e376; exact slawChunk_376 else
  if e377 : k = 377 then subst e377; exact slawChunk_377 else
  if e378 : k = 378 then subst e378; exact slawChunk_378 else
  if e379 : k = 379 then subst e379; exact slawChunk_379 else
  if e380 : k = 380 then subst e380; exact slawChunk_380 else
  if e381 : k = 381 then subst e381; exact slawChunk_381 else
  if e382 : k = 382 then subst e382; exact slawChunk_382 else
  if e383 : k = 383 then subst e383; exact slawChunk_383 else
  omega
end D2
