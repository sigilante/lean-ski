import Ski.D2Base
import Ski.D2K.S112
/-! Generated.  S-law of D: chunks 904..911 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_904 : slawChunk 904 = true := by decide +kernel
theorem slawChunk_905 : slawChunk 905 = true := by decide +kernel
theorem slawChunk_906 : slawChunk 906 = true := by decide +kernel
theorem slawChunk_907 : slawChunk 907 = true := by decide +kernel
theorem slawChunk_908 : slawChunk 908 = true := by decide +kernel
theorem slawChunk_909 : slawChunk 909 = true := by decide +kernel
theorem slawChunk_910 : slawChunk 910 = true := by decide +kernel
theorem slawChunk_911 : slawChunk 911 = true := by decide +kernel
theorem slawC_113 (k : Nat) (h1 : 904 ≤ k) (h2 : k < 912) : slawChunk k = true := by
  if e904 : k = 904 then subst e904; exact slawChunk_904 else
  if e905 : k = 905 then subst e905; exact slawChunk_905 else
  if e906 : k = 906 then subst e906; exact slawChunk_906 else
  if e907 : k = 907 then subst e907; exact slawChunk_907 else
  if e908 : k = 908 then subst e908; exact slawChunk_908 else
  if e909 : k = 909 then subst e909; exact slawChunk_909 else
  if e910 : k = 910 then subst e910; exact slawChunk_910 else
  if e911 : k = 911 then subst e911; exact slawChunk_911 else
  omega
end D2
