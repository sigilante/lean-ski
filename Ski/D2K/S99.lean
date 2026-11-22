import Ski.D2Base
import Ski.D2K.S98
/-! Generated.  S-law of D: chunks 792..799 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_792 : slawChunk 792 = true := by decide +kernel
theorem slawChunk_793 : slawChunk 793 = true := by decide +kernel
theorem slawChunk_794 : slawChunk 794 = true := by decide +kernel
theorem slawChunk_795 : slawChunk 795 = true := by decide +kernel
theorem slawChunk_796 : slawChunk 796 = true := by decide +kernel
theorem slawChunk_797 : slawChunk 797 = true := by decide +kernel
theorem slawChunk_798 : slawChunk 798 = true := by decide +kernel
theorem slawChunk_799 : slawChunk 799 = true := by decide +kernel
theorem slawC_99 (k : Nat) (h1 : 792 ≤ k) (h2 : k < 800) : slawChunk k = true := by
  if e792 : k = 792 then subst e792; exact slawChunk_792 else
  if e793 : k = 793 then subst e793; exact slawChunk_793 else
  if e794 : k = 794 then subst e794; exact slawChunk_794 else
  if e795 : k = 795 then subst e795; exact slawChunk_795 else
  if e796 : k = 796 then subst e796; exact slawChunk_796 else
  if e797 : k = 797 then subst e797; exact slawChunk_797 else
  if e798 : k = 798 then subst e798; exact slawChunk_798 else
  if e799 : k = 799 then subst e799; exact slawChunk_799 else
  omega
end D2
