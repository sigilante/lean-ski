import Ski.D2Base
import Ski.D2K.S90
/-! Generated.  S-law of D: chunks 728..735 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_728 : slawChunk 728 = true := by decide +kernel
theorem slawChunk_729 : slawChunk 729 = true := by decide +kernel
theorem slawChunk_730 : slawChunk 730 = true := by decide +kernel
theorem slawChunk_731 : slawChunk 731 = true := by decide +kernel
theorem slawChunk_732 : slawChunk 732 = true := by decide +kernel
theorem slawChunk_733 : slawChunk 733 = true := by decide +kernel
theorem slawChunk_734 : slawChunk 734 = true := by decide +kernel
theorem slawChunk_735 : slawChunk 735 = true := by decide +kernel
theorem slawC_91 (k : Nat) (h1 : 728 ≤ k) (h2 : k < 736) : slawChunk k = true := by
  if e728 : k = 728 then subst e728; exact slawChunk_728 else
  if e729 : k = 729 then subst e729; exact slawChunk_729 else
  if e730 : k = 730 then subst e730; exact slawChunk_730 else
  if e731 : k = 731 then subst e731; exact slawChunk_731 else
  if e732 : k = 732 then subst e732; exact slawChunk_732 else
  if e733 : k = 733 then subst e733; exact slawChunk_733 else
  if e734 : k = 734 then subst e734; exact slawChunk_734 else
  if e735 : k = 735 then subst e735; exact slawChunk_735 else
  omega
end D2
