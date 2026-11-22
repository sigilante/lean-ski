import Ski.D2Base
import Ski.D2K.S53
/-! Generated.  S-law of D: chunks 432..439 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_432 : slawChunk 432 = true := by decide +kernel
theorem slawChunk_433 : slawChunk 433 = true := by decide +kernel
theorem slawChunk_434 : slawChunk 434 = true := by decide +kernel
theorem slawChunk_435 : slawChunk 435 = true := by decide +kernel
theorem slawChunk_436 : slawChunk 436 = true := by decide +kernel
theorem slawChunk_437 : slawChunk 437 = true := by decide +kernel
theorem slawChunk_438 : slawChunk 438 = true := by decide +kernel
theorem slawChunk_439 : slawChunk 439 = true := by decide +kernel
theorem slawC_54 (k : Nat) (h1 : 432 ≤ k) (h2 : k < 440) : slawChunk k = true := by
  if e432 : k = 432 then subst e432; exact slawChunk_432 else
  if e433 : k = 433 then subst e433; exact slawChunk_433 else
  if e434 : k = 434 then subst e434; exact slawChunk_434 else
  if e435 : k = 435 then subst e435; exact slawChunk_435 else
  if e436 : k = 436 then subst e436; exact slawChunk_436 else
  if e437 : k = 437 then subst e437; exact slawChunk_437 else
  if e438 : k = 438 then subst e438; exact slawChunk_438 else
  if e439 : k = 439 then subst e439; exact slawChunk_439 else
  omega
end D2
