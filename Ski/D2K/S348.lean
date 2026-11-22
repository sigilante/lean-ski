import Ski.D2Base
import Ski.D2K.S347
/-! Generated.  S-law of D: chunks 2784..2791 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_2784 : slawChunk 2784 = true := by decide +kernel
theorem slawChunk_2785 : slawChunk 2785 = true := by decide +kernel
theorem slawChunk_2786 : slawChunk 2786 = true := by decide +kernel
theorem slawChunk_2787 : slawChunk 2787 = true := by decide +kernel
theorem slawChunk_2788 : slawChunk 2788 = true := by decide +kernel
theorem slawChunk_2789 : slawChunk 2789 = true := by decide +kernel
theorem slawChunk_2790 : slawChunk 2790 = true := by decide +kernel
theorem slawChunk_2791 : slawChunk 2791 = true := by decide +kernel
theorem slawC_348 (k : Nat) (h1 : 2784 ≤ k) (h2 : k < 2792) : slawChunk k = true := by
  if e2784 : k = 2784 then subst e2784; exact slawChunk_2784 else
  if e2785 : k = 2785 then subst e2785; exact slawChunk_2785 else
  if e2786 : k = 2786 then subst e2786; exact slawChunk_2786 else
  if e2787 : k = 2787 then subst e2787; exact slawChunk_2787 else
  if e2788 : k = 2788 then subst e2788; exact slawChunk_2788 else
  if e2789 : k = 2789 then subst e2789; exact slawChunk_2789 else
  if e2790 : k = 2790 then subst e2790; exact slawChunk_2790 else
  if e2791 : k = 2791 then subst e2791; exact slawChunk_2791 else
  omega
end D2
