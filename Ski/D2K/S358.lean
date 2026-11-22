import Ski.D2Base
import Ski.D2K.S357
/-! Generated.  S-law of D: chunks 2864..2871 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_2864 : slawChunk 2864 = true := by decide +kernel
theorem slawChunk_2865 : slawChunk 2865 = true := by decide +kernel
theorem slawChunk_2866 : slawChunk 2866 = true := by decide +kernel
theorem slawChunk_2867 : slawChunk 2867 = true := by decide +kernel
theorem slawChunk_2868 : slawChunk 2868 = true := by decide +kernel
theorem slawChunk_2869 : slawChunk 2869 = true := by decide +kernel
theorem slawChunk_2870 : slawChunk 2870 = true := by decide +kernel
theorem slawChunk_2871 : slawChunk 2871 = true := by decide +kernel
theorem slawC_358 (k : Nat) (h1 : 2864 ≤ k) (h2 : k < 2872) : slawChunk k = true := by
  if e2864 : k = 2864 then subst e2864; exact slawChunk_2864 else
  if e2865 : k = 2865 then subst e2865; exact slawChunk_2865 else
  if e2866 : k = 2866 then subst e2866; exact slawChunk_2866 else
  if e2867 : k = 2867 then subst e2867; exact slawChunk_2867 else
  if e2868 : k = 2868 then subst e2868; exact slawChunk_2868 else
  if e2869 : k = 2869 then subst e2869; exact slawChunk_2869 else
  if e2870 : k = 2870 then subst e2870; exact slawChunk_2870 else
  if e2871 : k = 2871 then subst e2871; exact slawChunk_2871 else
  omega
end D2
