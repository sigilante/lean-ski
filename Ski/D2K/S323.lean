import Ski.D2Base
import Ski.D2K.S322
/-! Generated.  S-law of D: chunks 2584..2591 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_2584 : slawChunk 2584 = true := by decide +kernel
theorem slawChunk_2585 : slawChunk 2585 = true := by decide +kernel
theorem slawChunk_2586 : slawChunk 2586 = true := by decide +kernel
theorem slawChunk_2587 : slawChunk 2587 = true := by decide +kernel
theorem slawChunk_2588 : slawChunk 2588 = true := by decide +kernel
theorem slawChunk_2589 : slawChunk 2589 = true := by decide +kernel
theorem slawChunk_2590 : slawChunk 2590 = true := by decide +kernel
theorem slawChunk_2591 : slawChunk 2591 = true := by decide +kernel
theorem slawC_323 (k : Nat) (h1 : 2584 ≤ k) (h2 : k < 2592) : slawChunk k = true := by
  if e2584 : k = 2584 then subst e2584; exact slawChunk_2584 else
  if e2585 : k = 2585 then subst e2585; exact slawChunk_2585 else
  if e2586 : k = 2586 then subst e2586; exact slawChunk_2586 else
  if e2587 : k = 2587 then subst e2587; exact slawChunk_2587 else
  if e2588 : k = 2588 then subst e2588; exact slawChunk_2588 else
  if e2589 : k = 2589 then subst e2589; exact slawChunk_2589 else
  if e2590 : k = 2590 then subst e2590; exact slawChunk_2590 else
  if e2591 : k = 2591 then subst e2591; exact slawChunk_2591 else
  omega
end D2
