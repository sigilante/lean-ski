import Ski.D2Base
import Ski.D2K.S334
/-! Generated.  S-law of D: chunks 2680..2687 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_2680 : slawChunk 2680 = true := by decide +kernel
theorem slawChunk_2681 : slawChunk 2681 = true := by decide +kernel
theorem slawChunk_2682 : slawChunk 2682 = true := by decide +kernel
theorem slawChunk_2683 : slawChunk 2683 = true := by decide +kernel
theorem slawChunk_2684 : slawChunk 2684 = true := by decide +kernel
theorem slawChunk_2685 : slawChunk 2685 = true := by decide +kernel
theorem slawChunk_2686 : slawChunk 2686 = true := by decide +kernel
theorem slawChunk_2687 : slawChunk 2687 = true := by decide +kernel
theorem slawC_335 (k : Nat) (h1 : 2680 ≤ k) (h2 : k < 2688) : slawChunk k = true := by
  if e2680 : k = 2680 then subst e2680; exact slawChunk_2680 else
  if e2681 : k = 2681 then subst e2681; exact slawChunk_2681 else
  if e2682 : k = 2682 then subst e2682; exact slawChunk_2682 else
  if e2683 : k = 2683 then subst e2683; exact slawChunk_2683 else
  if e2684 : k = 2684 then subst e2684; exact slawChunk_2684 else
  if e2685 : k = 2685 then subst e2685; exact slawChunk_2685 else
  if e2686 : k = 2686 then subst e2686; exact slawChunk_2686 else
  if e2687 : k = 2687 then subst e2687; exact slawChunk_2687 else
  omega
end D2
