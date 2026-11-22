import Ski.D2Base
import Ski.D2K.S297
/-! Generated.  S-law of D: chunks 2384..2391 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_2384 : slawChunk 2384 = true := by decide +kernel
theorem slawChunk_2385 : slawChunk 2385 = true := by decide +kernel
theorem slawChunk_2386 : slawChunk 2386 = true := by decide +kernel
theorem slawChunk_2387 : slawChunk 2387 = true := by decide +kernel
theorem slawChunk_2388 : slawChunk 2388 = true := by decide +kernel
theorem slawChunk_2389 : slawChunk 2389 = true := by decide +kernel
theorem slawChunk_2390 : slawChunk 2390 = true := by decide +kernel
theorem slawChunk_2391 : slawChunk 2391 = true := by decide +kernel
theorem slawC_298 (k : Nat) (h1 : 2384 ≤ k) (h2 : k < 2392) : slawChunk k = true := by
  if e2384 : k = 2384 then subst e2384; exact slawChunk_2384 else
  if e2385 : k = 2385 then subst e2385; exact slawChunk_2385 else
  if e2386 : k = 2386 then subst e2386; exact slawChunk_2386 else
  if e2387 : k = 2387 then subst e2387; exact slawChunk_2387 else
  if e2388 : k = 2388 then subst e2388; exact slawChunk_2388 else
  if e2389 : k = 2389 then subst e2389; exact slawChunk_2389 else
  if e2390 : k = 2390 then subst e2390; exact slawChunk_2390 else
  if e2391 : k = 2391 then subst e2391; exact slawChunk_2391 else
  omega
end D2
