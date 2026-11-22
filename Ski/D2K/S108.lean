import Ski.D2Base
import Ski.D2K.S107
/-! Generated.  S-law of D: chunks 864..871 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_864 : slawChunk 864 = true := by decide +kernel
theorem slawChunk_865 : slawChunk 865 = true := by decide +kernel
theorem slawChunk_866 : slawChunk 866 = true := by decide +kernel
theorem slawChunk_867 : slawChunk 867 = true := by decide +kernel
theorem slawChunk_868 : slawChunk 868 = true := by decide +kernel
theorem slawChunk_869 : slawChunk 869 = true := by decide +kernel
theorem slawChunk_870 : slawChunk 870 = true := by decide +kernel
theorem slawChunk_871 : slawChunk 871 = true := by decide +kernel
theorem slawC_108 (k : Nat) (h1 : 864 ≤ k) (h2 : k < 872) : slawChunk k = true := by
  if e864 : k = 864 then subst e864; exact slawChunk_864 else
  if e865 : k = 865 then subst e865; exact slawChunk_865 else
  if e866 : k = 866 then subst e866; exact slawChunk_866 else
  if e867 : k = 867 then subst e867; exact slawChunk_867 else
  if e868 : k = 868 then subst e868; exact slawChunk_868 else
  if e869 : k = 869 then subst e869; exact slawChunk_869 else
  if e870 : k = 870 then subst e870; exact slawChunk_870 else
  if e871 : k = 871 then subst e871; exact slawChunk_871 else
  omega
end D2
