import Ski.D2Base
import Ski.D2K.S314
/-! Generated.  S-law of D: chunks 2520..2527 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_2520 : slawChunk 2520 = true := by decide +kernel
theorem slawChunk_2521 : slawChunk 2521 = true := by decide +kernel
theorem slawChunk_2522 : slawChunk 2522 = true := by decide +kernel
theorem slawChunk_2523 : slawChunk 2523 = true := by decide +kernel
theorem slawChunk_2524 : slawChunk 2524 = true := by decide +kernel
theorem slawChunk_2525 : slawChunk 2525 = true := by decide +kernel
theorem slawChunk_2526 : slawChunk 2526 = true := by decide +kernel
theorem slawChunk_2527 : slawChunk 2527 = true := by decide +kernel
theorem slawC_315 (k : Nat) (h1 : 2520 ≤ k) (h2 : k < 2528) : slawChunk k = true := by
  if e2520 : k = 2520 then subst e2520; exact slawChunk_2520 else
  if e2521 : k = 2521 then subst e2521; exact slawChunk_2521 else
  if e2522 : k = 2522 then subst e2522; exact slawChunk_2522 else
  if e2523 : k = 2523 then subst e2523; exact slawChunk_2523 else
  if e2524 : k = 2524 then subst e2524; exact slawChunk_2524 else
  if e2525 : k = 2525 then subst e2525; exact slawChunk_2525 else
  if e2526 : k = 2526 then subst e2526; exact slawChunk_2526 else
  if e2527 : k = 2527 then subst e2527; exact slawChunk_2527 else
  omega
end D2
