import Ski.D2Base
import Ski.D2K.S315
/-! Generated.  S-law of D: chunks 2528..2535 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_2528 : slawChunk 2528 = true := by decide +kernel
theorem slawChunk_2529 : slawChunk 2529 = true := by decide +kernel
theorem slawChunk_2530 : slawChunk 2530 = true := by decide +kernel
theorem slawChunk_2531 : slawChunk 2531 = true := by decide +kernel
theorem slawChunk_2532 : slawChunk 2532 = true := by decide +kernel
theorem slawChunk_2533 : slawChunk 2533 = true := by decide +kernel
theorem slawChunk_2534 : slawChunk 2534 = true := by decide +kernel
theorem slawChunk_2535 : slawChunk 2535 = true := by decide +kernel
theorem slawC_316 (k : Nat) (h1 : 2528 ≤ k) (h2 : k < 2536) : slawChunk k = true := by
  if e2528 : k = 2528 then subst e2528; exact slawChunk_2528 else
  if e2529 : k = 2529 then subst e2529; exact slawChunk_2529 else
  if e2530 : k = 2530 then subst e2530; exact slawChunk_2530 else
  if e2531 : k = 2531 then subst e2531; exact slawChunk_2531 else
  if e2532 : k = 2532 then subst e2532; exact slawChunk_2532 else
  if e2533 : k = 2533 then subst e2533; exact slawChunk_2533 else
  if e2534 : k = 2534 then subst e2534; exact slawChunk_2534 else
  if e2535 : k = 2535 then subst e2535; exact slawChunk_2535 else
  omega
end D2
