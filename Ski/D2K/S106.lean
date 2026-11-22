import Ski.D2Base
import Ski.D2K.S105
/-! Generated.  S-law of D: chunks 848..855 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_848 : slawChunk 848 = true := by decide +kernel
theorem slawChunk_849 : slawChunk 849 = true := by decide +kernel
theorem slawChunk_850 : slawChunk 850 = true := by decide +kernel
theorem slawChunk_851 : slawChunk 851 = true := by decide +kernel
theorem slawChunk_852 : slawChunk 852 = true := by decide +kernel
theorem slawChunk_853 : slawChunk 853 = true := by decide +kernel
theorem slawChunk_854 : slawChunk 854 = true := by decide +kernel
theorem slawChunk_855 : slawChunk 855 = true := by decide +kernel
theorem slawC_106 (k : Nat) (h1 : 848 ≤ k) (h2 : k < 856) : slawChunk k = true := by
  if e848 : k = 848 then subst e848; exact slawChunk_848 else
  if e849 : k = 849 then subst e849; exact slawChunk_849 else
  if e850 : k = 850 then subst e850; exact slawChunk_850 else
  if e851 : k = 851 then subst e851; exact slawChunk_851 else
  if e852 : k = 852 then subst e852; exact slawChunk_852 else
  if e853 : k = 853 then subst e853; exact slawChunk_853 else
  if e854 : k = 854 then subst e854; exact slawChunk_854 else
  if e855 : k = 855 then subst e855; exact slawChunk_855 else
  omega
end D2
