import Ski.D2Base
import Ski.D2K.S94
/-! Generated.  S-law of D: chunks 760..767 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_760 : slawChunk 760 = true := by decide +kernel
theorem slawChunk_761 : slawChunk 761 = true := by decide +kernel
theorem slawChunk_762 : slawChunk 762 = true := by decide +kernel
theorem slawChunk_763 : slawChunk 763 = true := by decide +kernel
theorem slawChunk_764 : slawChunk 764 = true := by decide +kernel
theorem slawChunk_765 : slawChunk 765 = true := by decide +kernel
theorem slawChunk_766 : slawChunk 766 = true := by decide +kernel
theorem slawChunk_767 : slawChunk 767 = true := by decide +kernel
theorem slawC_95 (k : Nat) (h1 : 760 ≤ k) (h2 : k < 768) : slawChunk k = true := by
  if e760 : k = 760 then subst e760; exact slawChunk_760 else
  if e761 : k = 761 then subst e761; exact slawChunk_761 else
  if e762 : k = 762 then subst e762; exact slawChunk_762 else
  if e763 : k = 763 then subst e763; exact slawChunk_763 else
  if e764 : k = 764 then subst e764; exact slawChunk_764 else
  if e765 : k = 765 then subst e765; exact slawChunk_765 else
  if e766 : k = 766 then subst e766; exact slawChunk_766 else
  if e767 : k = 767 then subst e767; exact slawChunk_767 else
  omega
end D2
