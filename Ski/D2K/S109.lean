import Ski.D2Base
import Ski.D2K.S108
/-! Generated.  S-law of D: chunks 872..879 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_872 : slawChunk 872 = true := by decide +kernel
theorem slawChunk_873 : slawChunk 873 = true := by decide +kernel
theorem slawChunk_874 : slawChunk 874 = true := by decide +kernel
theorem slawChunk_875 : slawChunk 875 = true := by decide +kernel
theorem slawChunk_876 : slawChunk 876 = true := by decide +kernel
theorem slawChunk_877 : slawChunk 877 = true := by decide +kernel
theorem slawChunk_878 : slawChunk 878 = true := by decide +kernel
theorem slawChunk_879 : slawChunk 879 = true := by decide +kernel
theorem slawC_109 (k : Nat) (h1 : 872 ≤ k) (h2 : k < 880) : slawChunk k = true := by
  if e872 : k = 872 then subst e872; exact slawChunk_872 else
  if e873 : k = 873 then subst e873; exact slawChunk_873 else
  if e874 : k = 874 then subst e874; exact slawChunk_874 else
  if e875 : k = 875 then subst e875; exact slawChunk_875 else
  if e876 : k = 876 then subst e876; exact slawChunk_876 else
  if e877 : k = 877 then subst e877; exact slawChunk_877 else
  if e878 : k = 878 then subst e878; exact slawChunk_878 else
  if e879 : k = 879 then subst e879; exact slawChunk_879 else
  omega
end D2
