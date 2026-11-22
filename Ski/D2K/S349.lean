import Ski.D2Base
import Ski.D2K.S348
/-! Generated.  S-law of D: chunks 2792..2799 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_2792 : slawChunk 2792 = true := by decide +kernel
theorem slawChunk_2793 : slawChunk 2793 = true := by decide +kernel
theorem slawChunk_2794 : slawChunk 2794 = true := by decide +kernel
theorem slawChunk_2795 : slawChunk 2795 = true := by decide +kernel
theorem slawChunk_2796 : slawChunk 2796 = true := by decide +kernel
theorem slawChunk_2797 : slawChunk 2797 = true := by decide +kernel
theorem slawChunk_2798 : slawChunk 2798 = true := by decide +kernel
theorem slawChunk_2799 : slawChunk 2799 = true := by decide +kernel
theorem slawC_349 (k : Nat) (h1 : 2792 ≤ k) (h2 : k < 2800) : slawChunk k = true := by
  if e2792 : k = 2792 then subst e2792; exact slawChunk_2792 else
  if e2793 : k = 2793 then subst e2793; exact slawChunk_2793 else
  if e2794 : k = 2794 then subst e2794; exact slawChunk_2794 else
  if e2795 : k = 2795 then subst e2795; exact slawChunk_2795 else
  if e2796 : k = 2796 then subst e2796; exact slawChunk_2796 else
  if e2797 : k = 2797 then subst e2797; exact slawChunk_2797 else
  if e2798 : k = 2798 then subst e2798; exact slawChunk_2798 else
  if e2799 : k = 2799 then subst e2799; exact slawChunk_2799 else
  omega
end D2
