import Ski.D2Base
import Ski.D2K.S309
/-! Generated.  S-law of D: chunks 2480..2487 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_2480 : slawChunk 2480 = true := by decide +kernel
theorem slawChunk_2481 : slawChunk 2481 = true := by decide +kernel
theorem slawChunk_2482 : slawChunk 2482 = true := by decide +kernel
theorem slawChunk_2483 : slawChunk 2483 = true := by decide +kernel
theorem slawChunk_2484 : slawChunk 2484 = true := by decide +kernel
theorem slawChunk_2485 : slawChunk 2485 = true := by decide +kernel
theorem slawChunk_2486 : slawChunk 2486 = true := by decide +kernel
theorem slawChunk_2487 : slawChunk 2487 = true := by decide +kernel
theorem slawC_310 (k : Nat) (h1 : 2480 ≤ k) (h2 : k < 2488) : slawChunk k = true := by
  if e2480 : k = 2480 then subst e2480; exact slawChunk_2480 else
  if e2481 : k = 2481 then subst e2481; exact slawChunk_2481 else
  if e2482 : k = 2482 then subst e2482; exact slawChunk_2482 else
  if e2483 : k = 2483 then subst e2483; exact slawChunk_2483 else
  if e2484 : k = 2484 then subst e2484; exact slawChunk_2484 else
  if e2485 : k = 2485 then subst e2485; exact slawChunk_2485 else
  if e2486 : k = 2486 then subst e2486; exact slawChunk_2486 else
  if e2487 : k = 2487 then subst e2487; exact slawChunk_2487 else
  omega
end D2
