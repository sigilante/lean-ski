import Ski.D2Base
import Ski.D2K.S96
/-! Generated.  S-law of D: chunks 776..783 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_776 : slawChunk 776 = true := by decide +kernel
theorem slawChunk_777 : slawChunk 777 = true := by decide +kernel
theorem slawChunk_778 : slawChunk 778 = true := by decide +kernel
theorem slawChunk_779 : slawChunk 779 = true := by decide +kernel
theorem slawChunk_780 : slawChunk 780 = true := by decide +kernel
theorem slawChunk_781 : slawChunk 781 = true := by decide +kernel
theorem slawChunk_782 : slawChunk 782 = true := by decide +kernel
theorem slawChunk_783 : slawChunk 783 = true := by decide +kernel
theorem slawC_97 (k : Nat) (h1 : 776 ≤ k) (h2 : k < 784) : slawChunk k = true := by
  if e776 : k = 776 then subst e776; exact slawChunk_776 else
  if e777 : k = 777 then subst e777; exact slawChunk_777 else
  if e778 : k = 778 then subst e778; exact slawChunk_778 else
  if e779 : k = 779 then subst e779; exact slawChunk_779 else
  if e780 : k = 780 then subst e780; exact slawChunk_780 else
  if e781 : k = 781 then subst e781; exact slawChunk_781 else
  if e782 : k = 782 then subst e782; exact slawChunk_782 else
  if e783 : k = 783 then subst e783; exact slawChunk_783 else
  omega
end D2
