import Ski.D2Base
import Ski.D2K.S101
/-! Generated.  S-law of D: chunks 816..823 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_816 : slawChunk 816 = true := by decide +kernel
theorem slawChunk_817 : slawChunk 817 = true := by decide +kernel
theorem slawChunk_818 : slawChunk 818 = true := by decide +kernel
theorem slawChunk_819 : slawChunk 819 = true := by decide +kernel
theorem slawChunk_820 : slawChunk 820 = true := by decide +kernel
theorem slawChunk_821 : slawChunk 821 = true := by decide +kernel
theorem slawChunk_822 : slawChunk 822 = true := by decide +kernel
theorem slawChunk_823 : slawChunk 823 = true := by decide +kernel
theorem slawC_102 (k : Nat) (h1 : 816 ≤ k) (h2 : k < 824) : slawChunk k = true := by
  if e816 : k = 816 then subst e816; exact slawChunk_816 else
  if e817 : k = 817 then subst e817; exact slawChunk_817 else
  if e818 : k = 818 then subst e818; exact slawChunk_818 else
  if e819 : k = 819 then subst e819; exact slawChunk_819 else
  if e820 : k = 820 then subst e820; exact slawChunk_820 else
  if e821 : k = 821 then subst e821; exact slawChunk_821 else
  if e822 : k = 822 then subst e822; exact slawChunk_822 else
  if e823 : k = 823 then subst e823; exact slawChunk_823 else
  omega
end D2
