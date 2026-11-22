import Ski.D2Base
import Ski.D2K.S360
/-! Generated.  S-law of D: chunks 2888..2895 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_2888 : slawChunk 2888 = true := by decide +kernel
theorem slawChunk_2889 : slawChunk 2889 = true := by decide +kernel
theorem slawChunk_2890 : slawChunk 2890 = true := by decide +kernel
theorem slawChunk_2891 : slawChunk 2891 = true := by decide +kernel
theorem slawChunk_2892 : slawChunk 2892 = true := by decide +kernel
theorem slawChunk_2893 : slawChunk 2893 = true := by decide +kernel
theorem slawChunk_2894 : slawChunk 2894 = true := by decide +kernel
theorem slawChunk_2895 : slawChunk 2895 = true := by decide +kernel
theorem slawC_361 (k : Nat) (h1 : 2888 ≤ k) (h2 : k < 2896) : slawChunk k = true := by
  if e2888 : k = 2888 then subst e2888; exact slawChunk_2888 else
  if e2889 : k = 2889 then subst e2889; exact slawChunk_2889 else
  if e2890 : k = 2890 then subst e2890; exact slawChunk_2890 else
  if e2891 : k = 2891 then subst e2891; exact slawChunk_2891 else
  if e2892 : k = 2892 then subst e2892; exact slawChunk_2892 else
  if e2893 : k = 2893 then subst e2893; exact slawChunk_2893 else
  if e2894 : k = 2894 then subst e2894; exact slawChunk_2894 else
  if e2895 : k = 2895 then subst e2895; exact slawChunk_2895 else
  omega
end D2
