import Ski.D2Base
import Ski.D2K.S110
/-! Generated.  S-law of D: chunks 888..895 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_888 : slawChunk 888 = true := by decide +kernel
theorem slawChunk_889 : slawChunk 889 = true := by decide +kernel
theorem slawChunk_890 : slawChunk 890 = true := by decide +kernel
theorem slawChunk_891 : slawChunk 891 = true := by decide +kernel
theorem slawChunk_892 : slawChunk 892 = true := by decide +kernel
theorem slawChunk_893 : slawChunk 893 = true := by decide +kernel
theorem slawChunk_894 : slawChunk 894 = true := by decide +kernel
theorem slawChunk_895 : slawChunk 895 = true := by decide +kernel
theorem slawC_111 (k : Nat) (h1 : 888 ≤ k) (h2 : k < 896) : slawChunk k = true := by
  if e888 : k = 888 then subst e888; exact slawChunk_888 else
  if e889 : k = 889 then subst e889; exact slawChunk_889 else
  if e890 : k = 890 then subst e890; exact slawChunk_890 else
  if e891 : k = 891 then subst e891; exact slawChunk_891 else
  if e892 : k = 892 then subst e892; exact slawChunk_892 else
  if e893 : k = 893 then subst e893; exact slawChunk_893 else
  if e894 : k = 894 then subst e894; exact slawChunk_894 else
  if e895 : k = 895 then subst e895; exact slawChunk_895 else
  omega
end D2
