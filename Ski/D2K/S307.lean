import Ski.D2Base
import Ski.D2K.S306
/-! Generated.  S-law of D: chunks 2456..2463 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_2456 : slawChunk 2456 = true := by decide +kernel
theorem slawChunk_2457 : slawChunk 2457 = true := by decide +kernel
theorem slawChunk_2458 : slawChunk 2458 = true := by decide +kernel
theorem slawChunk_2459 : slawChunk 2459 = true := by decide +kernel
theorem slawChunk_2460 : slawChunk 2460 = true := by decide +kernel
theorem slawChunk_2461 : slawChunk 2461 = true := by decide +kernel
theorem slawChunk_2462 : slawChunk 2462 = true := by decide +kernel
theorem slawChunk_2463 : slawChunk 2463 = true := by decide +kernel
theorem slawC_307 (k : Nat) (h1 : 2456 ≤ k) (h2 : k < 2464) : slawChunk k = true := by
  if e2456 : k = 2456 then subst e2456; exact slawChunk_2456 else
  if e2457 : k = 2457 then subst e2457; exact slawChunk_2457 else
  if e2458 : k = 2458 then subst e2458; exact slawChunk_2458 else
  if e2459 : k = 2459 then subst e2459; exact slawChunk_2459 else
  if e2460 : k = 2460 then subst e2460; exact slawChunk_2460 else
  if e2461 : k = 2461 then subst e2461; exact slawChunk_2461 else
  if e2462 : k = 2462 then subst e2462; exact slawChunk_2462 else
  if e2463 : k = 2463 then subst e2463; exact slawChunk_2463 else
  omega
end D2
