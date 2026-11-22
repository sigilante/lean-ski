import Ski.D2Base
import Ski.D2K.S42
/-! Generated.  S-law of D: chunks 344..351 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_344 : slawChunk 344 = true := by decide +kernel
theorem slawChunk_345 : slawChunk 345 = true := by decide +kernel
theorem slawChunk_346 : slawChunk 346 = true := by decide +kernel
theorem slawChunk_347 : slawChunk 347 = true := by decide +kernel
theorem slawChunk_348 : slawChunk 348 = true := by decide +kernel
theorem slawChunk_349 : slawChunk 349 = true := by decide +kernel
theorem slawChunk_350 : slawChunk 350 = true := by decide +kernel
theorem slawChunk_351 : slawChunk 351 = true := by decide +kernel
theorem slawC_43 (k : Nat) (h1 : 344 ≤ k) (h2 : k < 352) : slawChunk k = true := by
  if e344 : k = 344 then subst e344; exact slawChunk_344 else
  if e345 : k = 345 then subst e345; exact slawChunk_345 else
  if e346 : k = 346 then subst e346; exact slawChunk_346 else
  if e347 : k = 347 then subst e347; exact slawChunk_347 else
  if e348 : k = 348 then subst e348; exact slawChunk_348 else
  if e349 : k = 349 then subst e349; exact slawChunk_349 else
  if e350 : k = 350 then subst e350; exact slawChunk_350 else
  if e351 : k = 351 then subst e351; exact slawChunk_351 else
  omega
end D2
