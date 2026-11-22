import Ski.D2Base
import Ski.D2K.S97
/-! Generated.  S-law of D: chunks 784..791 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_784 : slawChunk 784 = true := by decide +kernel
theorem slawChunk_785 : slawChunk 785 = true := by decide +kernel
theorem slawChunk_786 : slawChunk 786 = true := by decide +kernel
theorem slawChunk_787 : slawChunk 787 = true := by decide +kernel
theorem slawChunk_788 : slawChunk 788 = true := by decide +kernel
theorem slawChunk_789 : slawChunk 789 = true := by decide +kernel
theorem slawChunk_790 : slawChunk 790 = true := by decide +kernel
theorem slawChunk_791 : slawChunk 791 = true := by decide +kernel
theorem slawC_98 (k : Nat) (h1 : 784 ≤ k) (h2 : k < 792) : slawChunk k = true := by
  if e784 : k = 784 then subst e784; exact slawChunk_784 else
  if e785 : k = 785 then subst e785; exact slawChunk_785 else
  if e786 : k = 786 then subst e786; exact slawChunk_786 else
  if e787 : k = 787 then subst e787; exact slawChunk_787 else
  if e788 : k = 788 then subst e788; exact slawChunk_788 else
  if e789 : k = 789 then subst e789; exact slawChunk_789 else
  if e790 : k = 790 then subst e790; exact slawChunk_790 else
  if e791 : k = 791 then subst e791; exact slawChunk_791 else
  omega
end D2
