import Ski.D2Base
import Ski.D2K.S343
/-! Generated.  S-law of D: chunks 2752..2759 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_2752 : slawChunk 2752 = true := by decide +kernel
theorem slawChunk_2753 : slawChunk 2753 = true := by decide +kernel
theorem slawChunk_2754 : slawChunk 2754 = true := by decide +kernel
theorem slawChunk_2755 : slawChunk 2755 = true := by decide +kernel
theorem slawChunk_2756 : slawChunk 2756 = true := by decide +kernel
theorem slawChunk_2757 : slawChunk 2757 = true := by decide +kernel
theorem slawChunk_2758 : slawChunk 2758 = true := by decide +kernel
theorem slawChunk_2759 : slawChunk 2759 = true := by decide +kernel
theorem slawC_344 (k : Nat) (h1 : 2752 ≤ k) (h2 : k < 2760) : slawChunk k = true := by
  if e2752 : k = 2752 then subst e2752; exact slawChunk_2752 else
  if e2753 : k = 2753 then subst e2753; exact slawChunk_2753 else
  if e2754 : k = 2754 then subst e2754; exact slawChunk_2754 else
  if e2755 : k = 2755 then subst e2755; exact slawChunk_2755 else
  if e2756 : k = 2756 then subst e2756; exact slawChunk_2756 else
  if e2757 : k = 2757 then subst e2757; exact slawChunk_2757 else
  if e2758 : k = 2758 then subst e2758; exact slawChunk_2758 else
  if e2759 : k = 2759 then subst e2759; exact slawChunk_2759 else
  omega
end D2
