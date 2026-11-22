import Ski.D2Base
import Ski.D2K.S351
/-! Generated.  S-law of D: chunks 2816..2823 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_2816 : slawChunk 2816 = true := by decide +kernel
theorem slawChunk_2817 : slawChunk 2817 = true := by decide +kernel
theorem slawChunk_2818 : slawChunk 2818 = true := by decide +kernel
theorem slawChunk_2819 : slawChunk 2819 = true := by decide +kernel
theorem slawChunk_2820 : slawChunk 2820 = true := by decide +kernel
theorem slawChunk_2821 : slawChunk 2821 = true := by decide +kernel
theorem slawChunk_2822 : slawChunk 2822 = true := by decide +kernel
theorem slawChunk_2823 : slawChunk 2823 = true := by decide +kernel
theorem slawC_352 (k : Nat) (h1 : 2816 ≤ k) (h2 : k < 2824) : slawChunk k = true := by
  if e2816 : k = 2816 then subst e2816; exact slawChunk_2816 else
  if e2817 : k = 2817 then subst e2817; exact slawChunk_2817 else
  if e2818 : k = 2818 then subst e2818; exact slawChunk_2818 else
  if e2819 : k = 2819 then subst e2819; exact slawChunk_2819 else
  if e2820 : k = 2820 then subst e2820; exact slawChunk_2820 else
  if e2821 : k = 2821 then subst e2821; exact slawChunk_2821 else
  if e2822 : k = 2822 then subst e2822; exact slawChunk_2822 else
  if e2823 : k = 2823 then subst e2823; exact slawChunk_2823 else
  omega
end D2
