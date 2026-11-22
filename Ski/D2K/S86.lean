import Ski.D2Base
import Ski.D2K.S85
/-! Generated.  S-law of D: chunks 688..695 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_688 : slawChunk 688 = true := by decide +kernel
theorem slawChunk_689 : slawChunk 689 = true := by decide +kernel
theorem slawChunk_690 : slawChunk 690 = true := by decide +kernel
theorem slawChunk_691 : slawChunk 691 = true := by decide +kernel
theorem slawChunk_692 : slawChunk 692 = true := by decide +kernel
theorem slawChunk_693 : slawChunk 693 = true := by decide +kernel
theorem slawChunk_694 : slawChunk 694 = true := by decide +kernel
theorem slawChunk_695 : slawChunk 695 = true := by decide +kernel
theorem slawC_86 (k : Nat) (h1 : 688 ≤ k) (h2 : k < 696) : slawChunk k = true := by
  if e688 : k = 688 then subst e688; exact slawChunk_688 else
  if e689 : k = 689 then subst e689; exact slawChunk_689 else
  if e690 : k = 690 then subst e690; exact slawChunk_690 else
  if e691 : k = 691 then subst e691; exact slawChunk_691 else
  if e692 : k = 692 then subst e692; exact slawChunk_692 else
  if e693 : k = 693 then subst e693; exact slawChunk_693 else
  if e694 : k = 694 then subst e694; exact slawChunk_694 else
  if e695 : k = 695 then subst e695; exact slawChunk_695 else
  omega
end D2
