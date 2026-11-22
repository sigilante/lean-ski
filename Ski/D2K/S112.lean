import Ski.D2Base
import Ski.D2K.S111
/-! Generated.  S-law of D: chunks 896..903 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_896 : slawChunk 896 = true := by decide +kernel
theorem slawChunk_897 : slawChunk 897 = true := by decide +kernel
theorem slawChunk_898 : slawChunk 898 = true := by decide +kernel
theorem slawChunk_899 : slawChunk 899 = true := by decide +kernel
theorem slawChunk_900 : slawChunk 900 = true := by decide +kernel
theorem slawChunk_901 : slawChunk 901 = true := by decide +kernel
theorem slawChunk_902 : slawChunk 902 = true := by decide +kernel
theorem slawChunk_903 : slawChunk 903 = true := by decide +kernel
theorem slawC_112 (k : Nat) (h1 : 896 ≤ k) (h2 : k < 904) : slawChunk k = true := by
  if e896 : k = 896 then subst e896; exact slawChunk_896 else
  if e897 : k = 897 then subst e897; exact slawChunk_897 else
  if e898 : k = 898 then subst e898; exact slawChunk_898 else
  if e899 : k = 899 then subst e899; exact slawChunk_899 else
  if e900 : k = 900 then subst e900; exact slawChunk_900 else
  if e901 : k = 901 then subst e901; exact slawChunk_901 else
  if e902 : k = 902 then subst e902; exact slawChunk_902 else
  if e903 : k = 903 then subst e903; exact slawChunk_903 else
  omega
end D2
