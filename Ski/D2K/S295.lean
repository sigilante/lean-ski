import Ski.D2Base
import Ski.D2K.S294
/-! Generated.  S-law of D: chunks 2360..2367 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_2360 : slawChunk 2360 = true := by decide +kernel
theorem slawChunk_2361 : slawChunk 2361 = true := by decide +kernel
theorem slawChunk_2362 : slawChunk 2362 = true := by decide +kernel
theorem slawChunk_2363 : slawChunk 2363 = true := by decide +kernel
theorem slawChunk_2364 : slawChunk 2364 = true := by decide +kernel
theorem slawChunk_2365 : slawChunk 2365 = true := by decide +kernel
theorem slawChunk_2366 : slawChunk 2366 = true := by decide +kernel
theorem slawChunk_2367 : slawChunk 2367 = true := by decide +kernel
theorem slawC_295 (k : Nat) (h1 : 2360 ≤ k) (h2 : k < 2368) : slawChunk k = true := by
  if e2360 : k = 2360 then subst e2360; exact slawChunk_2360 else
  if e2361 : k = 2361 then subst e2361; exact slawChunk_2361 else
  if e2362 : k = 2362 then subst e2362; exact slawChunk_2362 else
  if e2363 : k = 2363 then subst e2363; exact slawChunk_2363 else
  if e2364 : k = 2364 then subst e2364; exact slawChunk_2364 else
  if e2365 : k = 2365 then subst e2365; exact slawChunk_2365 else
  if e2366 : k = 2366 then subst e2366; exact slawChunk_2366 else
  if e2367 : k = 2367 then subst e2367; exact slawChunk_2367 else
  omega
end D2
