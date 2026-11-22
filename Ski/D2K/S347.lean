import Ski.D2Base
import Ski.D2K.S346
/-! Generated.  S-law of D: chunks 2776..2783 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_2776 : slawChunk 2776 = true := by decide +kernel
theorem slawChunk_2777 : slawChunk 2777 = true := by decide +kernel
theorem slawChunk_2778 : slawChunk 2778 = true := by decide +kernel
theorem slawChunk_2779 : slawChunk 2779 = true := by decide +kernel
theorem slawChunk_2780 : slawChunk 2780 = true := by decide +kernel
theorem slawChunk_2781 : slawChunk 2781 = true := by decide +kernel
theorem slawChunk_2782 : slawChunk 2782 = true := by decide +kernel
theorem slawChunk_2783 : slawChunk 2783 = true := by decide +kernel
theorem slawC_347 (k : Nat) (h1 : 2776 ≤ k) (h2 : k < 2784) : slawChunk k = true := by
  if e2776 : k = 2776 then subst e2776; exact slawChunk_2776 else
  if e2777 : k = 2777 then subst e2777; exact slawChunk_2777 else
  if e2778 : k = 2778 then subst e2778; exact slawChunk_2778 else
  if e2779 : k = 2779 then subst e2779; exact slawChunk_2779 else
  if e2780 : k = 2780 then subst e2780; exact slawChunk_2780 else
  if e2781 : k = 2781 then subst e2781; exact slawChunk_2781 else
  if e2782 : k = 2782 then subst e2782; exact slawChunk_2782 else
  if e2783 : k = 2783 then subst e2783; exact slawChunk_2783 else
  omega
end D2
