import Ski.D2Base
import Ski.D2K.S305
/-! Generated.  S-law of D: chunks 2448..2455 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_2448 : slawChunk 2448 = true := by decide +kernel
theorem slawChunk_2449 : slawChunk 2449 = true := by decide +kernel
theorem slawChunk_2450 : slawChunk 2450 = true := by decide +kernel
theorem slawChunk_2451 : slawChunk 2451 = true := by decide +kernel
theorem slawChunk_2452 : slawChunk 2452 = true := by decide +kernel
theorem slawChunk_2453 : slawChunk 2453 = true := by decide +kernel
theorem slawChunk_2454 : slawChunk 2454 = true := by decide +kernel
theorem slawChunk_2455 : slawChunk 2455 = true := by decide +kernel
theorem slawC_306 (k : Nat) (h1 : 2448 ≤ k) (h2 : k < 2456) : slawChunk k = true := by
  if e2448 : k = 2448 then subst e2448; exact slawChunk_2448 else
  if e2449 : k = 2449 then subst e2449; exact slawChunk_2449 else
  if e2450 : k = 2450 then subst e2450; exact slawChunk_2450 else
  if e2451 : k = 2451 then subst e2451; exact slawChunk_2451 else
  if e2452 : k = 2452 then subst e2452; exact slawChunk_2452 else
  if e2453 : k = 2453 then subst e2453; exact slawChunk_2453 else
  if e2454 : k = 2454 then subst e2454; exact slawChunk_2454 else
  if e2455 : k = 2455 then subst e2455; exact slawChunk_2455 else
  omega
end D2
