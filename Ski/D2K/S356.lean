import Ski.D2Base
import Ski.D2K.S355
/-! Generated.  S-law of D: chunks 2848..2855 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_2848 : slawChunk 2848 = true := by decide +kernel
theorem slawChunk_2849 : slawChunk 2849 = true := by decide +kernel
theorem slawChunk_2850 : slawChunk 2850 = true := by decide +kernel
theorem slawChunk_2851 : slawChunk 2851 = true := by decide +kernel
theorem slawChunk_2852 : slawChunk 2852 = true := by decide +kernel
theorem slawChunk_2853 : slawChunk 2853 = true := by decide +kernel
theorem slawChunk_2854 : slawChunk 2854 = true := by decide +kernel
theorem slawChunk_2855 : slawChunk 2855 = true := by decide +kernel
theorem slawC_356 (k : Nat) (h1 : 2848 ≤ k) (h2 : k < 2856) : slawChunk k = true := by
  if e2848 : k = 2848 then subst e2848; exact slawChunk_2848 else
  if e2849 : k = 2849 then subst e2849; exact slawChunk_2849 else
  if e2850 : k = 2850 then subst e2850; exact slawChunk_2850 else
  if e2851 : k = 2851 then subst e2851; exact slawChunk_2851 else
  if e2852 : k = 2852 then subst e2852; exact slawChunk_2852 else
  if e2853 : k = 2853 then subst e2853; exact slawChunk_2853 else
  if e2854 : k = 2854 then subst e2854; exact slawChunk_2854 else
  if e2855 : k = 2855 then subst e2855; exact slawChunk_2855 else
  omega
end D2
