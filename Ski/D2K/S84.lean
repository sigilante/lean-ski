import Ski.D2Base
import Ski.D2K.S83
/-! Generated.  S-law of D: chunks 672..679 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_672 : slawChunk 672 = true := by decide +kernel
theorem slawChunk_673 : slawChunk 673 = true := by decide +kernel
theorem slawChunk_674 : slawChunk 674 = true := by decide +kernel
theorem slawChunk_675 : slawChunk 675 = true := by decide +kernel
theorem slawChunk_676 : slawChunk 676 = true := by decide +kernel
theorem slawChunk_677 : slawChunk 677 = true := by decide +kernel
theorem slawChunk_678 : slawChunk 678 = true := by decide +kernel
theorem slawChunk_679 : slawChunk 679 = true := by decide +kernel
theorem slawC_84 (k : Nat) (h1 : 672 ≤ k) (h2 : k < 680) : slawChunk k = true := by
  if e672 : k = 672 then subst e672; exact slawChunk_672 else
  if e673 : k = 673 then subst e673; exact slawChunk_673 else
  if e674 : k = 674 then subst e674; exact slawChunk_674 else
  if e675 : k = 675 then subst e675; exact slawChunk_675 else
  if e676 : k = 676 then subst e676; exact slawChunk_676 else
  if e677 : k = 677 then subst e677; exact slawChunk_677 else
  if e678 : k = 678 then subst e678; exact slawChunk_678 else
  if e679 : k = 679 then subst e679; exact slawChunk_679 else
  omega
end D2
