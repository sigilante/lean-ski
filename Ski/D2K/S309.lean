import Ski.D2Base
import Ski.D2K.S308
/-! Generated.  S-law of D: chunks 2472..2479 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_2472 : slawChunk 2472 = true := by decide +kernel
theorem slawChunk_2473 : slawChunk 2473 = true := by decide +kernel
theorem slawChunk_2474 : slawChunk 2474 = true := by decide +kernel
theorem slawChunk_2475 : slawChunk 2475 = true := by decide +kernel
theorem slawChunk_2476 : slawChunk 2476 = true := by decide +kernel
theorem slawChunk_2477 : slawChunk 2477 = true := by decide +kernel
theorem slawChunk_2478 : slawChunk 2478 = true := by decide +kernel
theorem slawChunk_2479 : slawChunk 2479 = true := by decide +kernel
theorem slawC_309 (k : Nat) (h1 : 2472 ≤ k) (h2 : k < 2480) : slawChunk k = true := by
  if e2472 : k = 2472 then subst e2472; exact slawChunk_2472 else
  if e2473 : k = 2473 then subst e2473; exact slawChunk_2473 else
  if e2474 : k = 2474 then subst e2474; exact slawChunk_2474 else
  if e2475 : k = 2475 then subst e2475; exact slawChunk_2475 else
  if e2476 : k = 2476 then subst e2476; exact slawChunk_2476 else
  if e2477 : k = 2477 then subst e2477; exact slawChunk_2477 else
  if e2478 : k = 2478 then subst e2478; exact slawChunk_2478 else
  if e2479 : k = 2479 then subst e2479; exact slawChunk_2479 else
  omega
end D2
