import Ski.D2Base
import Ski.D2K.S91
/-! Generated.  S-law of D: chunks 736..743 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_736 : slawChunk 736 = true := by decide +kernel
theorem slawChunk_737 : slawChunk 737 = true := by decide +kernel
theorem slawChunk_738 : slawChunk 738 = true := by decide +kernel
theorem slawChunk_739 : slawChunk 739 = true := by decide +kernel
theorem slawChunk_740 : slawChunk 740 = true := by decide +kernel
theorem slawChunk_741 : slawChunk 741 = true := by decide +kernel
theorem slawChunk_742 : slawChunk 742 = true := by decide +kernel
theorem slawChunk_743 : slawChunk 743 = true := by decide +kernel
theorem slawC_92 (k : Nat) (h1 : 736 ≤ k) (h2 : k < 744) : slawChunk k = true := by
  if e736 : k = 736 then subst e736; exact slawChunk_736 else
  if e737 : k = 737 then subst e737; exact slawChunk_737 else
  if e738 : k = 738 then subst e738; exact slawChunk_738 else
  if e739 : k = 739 then subst e739; exact slawChunk_739 else
  if e740 : k = 740 then subst e740; exact slawChunk_740 else
  if e741 : k = 741 then subst e741; exact slawChunk_741 else
  if e742 : k = 742 then subst e742; exact slawChunk_742 else
  if e743 : k = 743 then subst e743; exact slawChunk_743 else
  omega
end D2
