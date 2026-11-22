import Ski.D2Base
import Ski.D2K.S358
/-! Generated.  S-law of D: chunks 2872..2879 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_2872 : slawChunk 2872 = true := by decide +kernel
theorem slawChunk_2873 : slawChunk 2873 = true := by decide +kernel
theorem slawChunk_2874 : slawChunk 2874 = true := by decide +kernel
theorem slawChunk_2875 : slawChunk 2875 = true := by decide +kernel
theorem slawChunk_2876 : slawChunk 2876 = true := by decide +kernel
theorem slawChunk_2877 : slawChunk 2877 = true := by decide +kernel
theorem slawChunk_2878 : slawChunk 2878 = true := by decide +kernel
theorem slawChunk_2879 : slawChunk 2879 = true := by decide +kernel
theorem slawC_359 (k : Nat) (h1 : 2872 ≤ k) (h2 : k < 2880) : slawChunk k = true := by
  if e2872 : k = 2872 then subst e2872; exact slawChunk_2872 else
  if e2873 : k = 2873 then subst e2873; exact slawChunk_2873 else
  if e2874 : k = 2874 then subst e2874; exact slawChunk_2874 else
  if e2875 : k = 2875 then subst e2875; exact slawChunk_2875 else
  if e2876 : k = 2876 then subst e2876; exact slawChunk_2876 else
  if e2877 : k = 2877 then subst e2877; exact slawChunk_2877 else
  if e2878 : k = 2878 then subst e2878; exact slawChunk_2878 else
  if e2879 : k = 2879 then subst e2879; exact slawChunk_2879 else
  omega
end D2
