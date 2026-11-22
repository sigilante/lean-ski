import Ski.D2Base
import Ski.D2K.S296
/-! Generated.  S-law of D: chunks 2376..2383 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_2376 : slawChunk 2376 = true := by decide +kernel
theorem slawChunk_2377 : slawChunk 2377 = true := by decide +kernel
theorem slawChunk_2378 : slawChunk 2378 = true := by decide +kernel
theorem slawChunk_2379 : slawChunk 2379 = true := by decide +kernel
theorem slawChunk_2380 : slawChunk 2380 = true := by decide +kernel
theorem slawChunk_2381 : slawChunk 2381 = true := by decide +kernel
theorem slawChunk_2382 : slawChunk 2382 = true := by decide +kernel
theorem slawChunk_2383 : slawChunk 2383 = true := by decide +kernel
theorem slawC_297 (k : Nat) (h1 : 2376 ≤ k) (h2 : k < 2384) : slawChunk k = true := by
  if e2376 : k = 2376 then subst e2376; exact slawChunk_2376 else
  if e2377 : k = 2377 then subst e2377; exact slawChunk_2377 else
  if e2378 : k = 2378 then subst e2378; exact slawChunk_2378 else
  if e2379 : k = 2379 then subst e2379; exact slawChunk_2379 else
  if e2380 : k = 2380 then subst e2380; exact slawChunk_2380 else
  if e2381 : k = 2381 then subst e2381; exact slawChunk_2381 else
  if e2382 : k = 2382 then subst e2382; exact slawChunk_2382 else
  if e2383 : k = 2383 then subst e2383; exact slawChunk_2383 else
  omega
end D2
