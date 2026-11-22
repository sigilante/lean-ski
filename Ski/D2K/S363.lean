import Ski.D2Base
import Ski.D2K.S362
/-! Generated.  S-law of D: chunks 2904..2911 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_2904 : slawChunk 2904 = true := by decide +kernel
theorem slawChunk_2905 : slawChunk 2905 = true := by decide +kernel
theorem slawChunk_2906 : slawChunk 2906 = true := by decide +kernel
theorem slawChunk_2907 : slawChunk 2907 = true := by decide +kernel
theorem slawChunk_2908 : slawChunk 2908 = true := by decide +kernel
theorem slawChunk_2909 : slawChunk 2909 = true := by decide +kernel
theorem slawChunk_2910 : slawChunk 2910 = true := by decide +kernel
theorem slawChunk_2911 : slawChunk 2911 = true := by decide +kernel
theorem slawC_363 (k : Nat) (h1 : 2904 ≤ k) (h2 : k < 2912) : slawChunk k = true := by
  if e2904 : k = 2904 then subst e2904; exact slawChunk_2904 else
  if e2905 : k = 2905 then subst e2905; exact slawChunk_2905 else
  if e2906 : k = 2906 then subst e2906; exact slawChunk_2906 else
  if e2907 : k = 2907 then subst e2907; exact slawChunk_2907 else
  if e2908 : k = 2908 then subst e2908; exact slawChunk_2908 else
  if e2909 : k = 2909 then subst e2909; exact slawChunk_2909 else
  if e2910 : k = 2910 then subst e2910; exact slawChunk_2910 else
  if e2911 : k = 2911 then subst e2911; exact slawChunk_2911 else
  omega
end D2
