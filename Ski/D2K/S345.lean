import Ski.D2Base
import Ski.D2K.S344
/-! Generated.  S-law of D: chunks 2760..2767 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_2760 : slawChunk 2760 = true := by decide +kernel
theorem slawChunk_2761 : slawChunk 2761 = true := by decide +kernel
theorem slawChunk_2762 : slawChunk 2762 = true := by decide +kernel
theorem slawChunk_2763 : slawChunk 2763 = true := by decide +kernel
theorem slawChunk_2764 : slawChunk 2764 = true := by decide +kernel
theorem slawChunk_2765 : slawChunk 2765 = true := by decide +kernel
theorem slawChunk_2766 : slawChunk 2766 = true := by decide +kernel
theorem slawChunk_2767 : slawChunk 2767 = true := by decide +kernel
theorem slawC_345 (k : Nat) (h1 : 2760 ≤ k) (h2 : k < 2768) : slawChunk k = true := by
  if e2760 : k = 2760 then subst e2760; exact slawChunk_2760 else
  if e2761 : k = 2761 then subst e2761; exact slawChunk_2761 else
  if e2762 : k = 2762 then subst e2762; exact slawChunk_2762 else
  if e2763 : k = 2763 then subst e2763; exact slawChunk_2763 else
  if e2764 : k = 2764 then subst e2764; exact slawChunk_2764 else
  if e2765 : k = 2765 then subst e2765; exact slawChunk_2765 else
  if e2766 : k = 2766 then subst e2766; exact slawChunk_2766 else
  if e2767 : k = 2767 then subst e2767; exact slawChunk_2767 else
  omega
end D2
