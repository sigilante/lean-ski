import Ski.D2Base
import Ski.D2K.S310
/-! Generated.  S-law of D: chunks 2488..2495 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_2488 : slawChunk 2488 = true := by decide +kernel
theorem slawChunk_2489 : slawChunk 2489 = true := by decide +kernel
theorem slawChunk_2490 : slawChunk 2490 = true := by decide +kernel
theorem slawChunk_2491 : slawChunk 2491 = true := by decide +kernel
theorem slawChunk_2492 : slawChunk 2492 = true := by decide +kernel
theorem slawChunk_2493 : slawChunk 2493 = true := by decide +kernel
theorem slawChunk_2494 : slawChunk 2494 = true := by decide +kernel
theorem slawChunk_2495 : slawChunk 2495 = true := by decide +kernel
theorem slawC_311 (k : Nat) (h1 : 2488 ≤ k) (h2 : k < 2496) : slawChunk k = true := by
  if e2488 : k = 2488 then subst e2488; exact slawChunk_2488 else
  if e2489 : k = 2489 then subst e2489; exact slawChunk_2489 else
  if e2490 : k = 2490 then subst e2490; exact slawChunk_2490 else
  if e2491 : k = 2491 then subst e2491; exact slawChunk_2491 else
  if e2492 : k = 2492 then subst e2492; exact slawChunk_2492 else
  if e2493 : k = 2493 then subst e2493; exact slawChunk_2493 else
  if e2494 : k = 2494 then subst e2494; exact slawChunk_2494 else
  if e2495 : k = 2495 then subst e2495; exact slawChunk_2495 else
  omega
end D2
