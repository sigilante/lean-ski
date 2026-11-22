import Ski.D2Base
import Ski.D2K.S293
/-! Generated.  S-law of D: chunks 2352..2359 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_2352 : slawChunk 2352 = true := by decide +kernel
theorem slawChunk_2353 : slawChunk 2353 = true := by decide +kernel
theorem slawChunk_2354 : slawChunk 2354 = true := by decide +kernel
theorem slawChunk_2355 : slawChunk 2355 = true := by decide +kernel
theorem slawChunk_2356 : slawChunk 2356 = true := by decide +kernel
theorem slawChunk_2357 : slawChunk 2357 = true := by decide +kernel
theorem slawChunk_2358 : slawChunk 2358 = true := by decide +kernel
theorem slawChunk_2359 : slawChunk 2359 = true := by decide +kernel
theorem slawC_294 (k : Nat) (h1 : 2352 ≤ k) (h2 : k < 2360) : slawChunk k = true := by
  if e2352 : k = 2352 then subst e2352; exact slawChunk_2352 else
  if e2353 : k = 2353 then subst e2353; exact slawChunk_2353 else
  if e2354 : k = 2354 then subst e2354; exact slawChunk_2354 else
  if e2355 : k = 2355 then subst e2355; exact slawChunk_2355 else
  if e2356 : k = 2356 then subst e2356; exact slawChunk_2356 else
  if e2357 : k = 2357 then subst e2357; exact slawChunk_2357 else
  if e2358 : k = 2358 then subst e2358; exact slawChunk_2358 else
  if e2359 : k = 2359 then subst e2359; exact slawChunk_2359 else
  omega
end D2
