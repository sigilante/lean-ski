import Ski.D2Base
import Ski.D2K.S298
/-! Generated.  S-law of D: chunks 2392..2399 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_2392 : slawChunk 2392 = true := by decide +kernel
theorem slawChunk_2393 : slawChunk 2393 = true := by decide +kernel
theorem slawChunk_2394 : slawChunk 2394 = true := by decide +kernel
theorem slawChunk_2395 : slawChunk 2395 = true := by decide +kernel
theorem slawChunk_2396 : slawChunk 2396 = true := by decide +kernel
theorem slawChunk_2397 : slawChunk 2397 = true := by decide +kernel
theorem slawChunk_2398 : slawChunk 2398 = true := by decide +kernel
theorem slawChunk_2399 : slawChunk 2399 = true := by decide +kernel
theorem slawC_299 (k : Nat) (h1 : 2392 ≤ k) (h2 : k < 2400) : slawChunk k = true := by
  if e2392 : k = 2392 then subst e2392; exact slawChunk_2392 else
  if e2393 : k = 2393 then subst e2393; exact slawChunk_2393 else
  if e2394 : k = 2394 then subst e2394; exact slawChunk_2394 else
  if e2395 : k = 2395 then subst e2395; exact slawChunk_2395 else
  if e2396 : k = 2396 then subst e2396; exact slawChunk_2396 else
  if e2397 : k = 2397 then subst e2397; exact slawChunk_2397 else
  if e2398 : k = 2398 then subst e2398; exact slawChunk_2398 else
  if e2399 : k = 2399 then subst e2399; exact slawChunk_2399 else
  omega
end D2
