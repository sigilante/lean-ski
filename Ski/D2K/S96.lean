import Ski.D2Base
import Ski.D2K.S95
/-! Generated.  S-law of D: chunks 768..775 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_768 : slawChunk 768 = true := by decide +kernel
theorem slawChunk_769 : slawChunk 769 = true := by decide +kernel
theorem slawChunk_770 : slawChunk 770 = true := by decide +kernel
theorem slawChunk_771 : slawChunk 771 = true := by decide +kernel
theorem slawChunk_772 : slawChunk 772 = true := by decide +kernel
theorem slawChunk_773 : slawChunk 773 = true := by decide +kernel
theorem slawChunk_774 : slawChunk 774 = true := by decide +kernel
theorem slawChunk_775 : slawChunk 775 = true := by decide +kernel
theorem slawC_96 (k : Nat) (h1 : 768 ≤ k) (h2 : k < 776) : slawChunk k = true := by
  if e768 : k = 768 then subst e768; exact slawChunk_768 else
  if e769 : k = 769 then subst e769; exact slawChunk_769 else
  if e770 : k = 770 then subst e770; exact slawChunk_770 else
  if e771 : k = 771 then subst e771; exact slawChunk_771 else
  if e772 : k = 772 then subst e772; exact slawChunk_772 else
  if e773 : k = 773 then subst e773; exact slawChunk_773 else
  if e774 : k = 774 then subst e774; exact slawChunk_774 else
  if e775 : k = 775 then subst e775; exact slawChunk_775 else
  omega
end D2
