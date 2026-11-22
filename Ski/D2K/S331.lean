import Ski.D2Base
import Ski.D2K.S330
/-! Generated.  S-law of D: chunks 2648..2655 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_2648 : slawChunk 2648 = true := by decide +kernel
theorem slawChunk_2649 : slawChunk 2649 = true := by decide +kernel
theorem slawChunk_2650 : slawChunk 2650 = true := by decide +kernel
theorem slawChunk_2651 : slawChunk 2651 = true := by decide +kernel
theorem slawChunk_2652 : slawChunk 2652 = true := by decide +kernel
theorem slawChunk_2653 : slawChunk 2653 = true := by decide +kernel
theorem slawChunk_2654 : slawChunk 2654 = true := by decide +kernel
theorem slawChunk_2655 : slawChunk 2655 = true := by decide +kernel
theorem slawC_331 (k : Nat) (h1 : 2648 ≤ k) (h2 : k < 2656) : slawChunk k = true := by
  if e2648 : k = 2648 then subst e2648; exact slawChunk_2648 else
  if e2649 : k = 2649 then subst e2649; exact slawChunk_2649 else
  if e2650 : k = 2650 then subst e2650; exact slawChunk_2650 else
  if e2651 : k = 2651 then subst e2651; exact slawChunk_2651 else
  if e2652 : k = 2652 then subst e2652; exact slawChunk_2652 else
  if e2653 : k = 2653 then subst e2653; exact slawChunk_2653 else
  if e2654 : k = 2654 then subst e2654; exact slawChunk_2654 else
  if e2655 : k = 2655 then subst e2655; exact slawChunk_2655 else
  omega
end D2
