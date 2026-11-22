import Ski.D2Base
import Ski.D2K.S103
/-! Generated.  S-law of D: chunks 832..839 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_832 : slawChunk 832 = true := by decide +kernel
theorem slawChunk_833 : slawChunk 833 = true := by decide +kernel
theorem slawChunk_834 : slawChunk 834 = true := by decide +kernel
theorem slawChunk_835 : slawChunk 835 = true := by decide +kernel
theorem slawChunk_836 : slawChunk 836 = true := by decide +kernel
theorem slawChunk_837 : slawChunk 837 = true := by decide +kernel
theorem slawChunk_838 : slawChunk 838 = true := by decide +kernel
theorem slawChunk_839 : slawChunk 839 = true := by decide +kernel
theorem slawC_104 (k : Nat) (h1 : 832 ≤ k) (h2 : k < 840) : slawChunk k = true := by
  if e832 : k = 832 then subst e832; exact slawChunk_832 else
  if e833 : k = 833 then subst e833; exact slawChunk_833 else
  if e834 : k = 834 then subst e834; exact slawChunk_834 else
  if e835 : k = 835 then subst e835; exact slawChunk_835 else
  if e836 : k = 836 then subst e836; exact slawChunk_836 else
  if e837 : k = 837 then subst e837; exact slawChunk_837 else
  if e838 : k = 838 then subst e838; exact slawChunk_838 else
  if e839 : k = 839 then subst e839; exact slawChunk_839 else
  omega
end D2
