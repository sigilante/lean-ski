import Ski.D2Base
import Ski.D2K.S295
/-! Generated.  S-law of D: chunks 2368..2375 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_2368 : slawChunk 2368 = true := by decide +kernel
theorem slawChunk_2369 : slawChunk 2369 = true := by decide +kernel
theorem slawChunk_2370 : slawChunk 2370 = true := by decide +kernel
theorem slawChunk_2371 : slawChunk 2371 = true := by decide +kernel
theorem slawChunk_2372 : slawChunk 2372 = true := by decide +kernel
theorem slawChunk_2373 : slawChunk 2373 = true := by decide +kernel
theorem slawChunk_2374 : slawChunk 2374 = true := by decide +kernel
theorem slawChunk_2375 : slawChunk 2375 = true := by decide +kernel
theorem slawC_296 (k : Nat) (h1 : 2368 ≤ k) (h2 : k < 2376) : slawChunk k = true := by
  if e2368 : k = 2368 then subst e2368; exact slawChunk_2368 else
  if e2369 : k = 2369 then subst e2369; exact slawChunk_2369 else
  if e2370 : k = 2370 then subst e2370; exact slawChunk_2370 else
  if e2371 : k = 2371 then subst e2371; exact slawChunk_2371 else
  if e2372 : k = 2372 then subst e2372; exact slawChunk_2372 else
  if e2373 : k = 2373 then subst e2373; exact slawChunk_2373 else
  if e2374 : k = 2374 then subst e2374; exact slawChunk_2374 else
  if e2375 : k = 2375 then subst e2375; exact slawChunk_2375 else
  omega
end D2
