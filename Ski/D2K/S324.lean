import Ski.D2Base
import Ski.D2K.S323
/-! Generated.  S-law of D: chunks 2592..2599 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_2592 : slawChunk 2592 = true := by decide +kernel
theorem slawChunk_2593 : slawChunk 2593 = true := by decide +kernel
theorem slawChunk_2594 : slawChunk 2594 = true := by decide +kernel
theorem slawChunk_2595 : slawChunk 2595 = true := by decide +kernel
theorem slawChunk_2596 : slawChunk 2596 = true := by decide +kernel
theorem slawChunk_2597 : slawChunk 2597 = true := by decide +kernel
theorem slawChunk_2598 : slawChunk 2598 = true := by decide +kernel
theorem slawChunk_2599 : slawChunk 2599 = true := by decide +kernel
theorem slawC_324 (k : Nat) (h1 : 2592 ≤ k) (h2 : k < 2600) : slawChunk k = true := by
  if e2592 : k = 2592 then subst e2592; exact slawChunk_2592 else
  if e2593 : k = 2593 then subst e2593; exact slawChunk_2593 else
  if e2594 : k = 2594 then subst e2594; exact slawChunk_2594 else
  if e2595 : k = 2595 then subst e2595; exact slawChunk_2595 else
  if e2596 : k = 2596 then subst e2596; exact slawChunk_2596 else
  if e2597 : k = 2597 then subst e2597; exact slawChunk_2597 else
  if e2598 : k = 2598 then subst e2598; exact slawChunk_2598 else
  if e2599 : k = 2599 then subst e2599; exact slawChunk_2599 else
  omega
end D2
