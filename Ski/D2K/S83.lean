import Ski.D2Base
import Ski.D2K.S82
/-! Generated.  S-law of D: chunks 664..671 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_664 : slawChunk 664 = true := by decide +kernel
theorem slawChunk_665 : slawChunk 665 = true := by decide +kernel
theorem slawChunk_666 : slawChunk 666 = true := by decide +kernel
theorem slawChunk_667 : slawChunk 667 = true := by decide +kernel
theorem slawChunk_668 : slawChunk 668 = true := by decide +kernel
theorem slawChunk_669 : slawChunk 669 = true := by decide +kernel
theorem slawChunk_670 : slawChunk 670 = true := by decide +kernel
theorem slawChunk_671 : slawChunk 671 = true := by decide +kernel
theorem slawC_83 (k : Nat) (h1 : 664 ≤ k) (h2 : k < 672) : slawChunk k = true := by
  if e664 : k = 664 then subst e664; exact slawChunk_664 else
  if e665 : k = 665 then subst e665; exact slawChunk_665 else
  if e666 : k = 666 then subst e666; exact slawChunk_666 else
  if e667 : k = 667 then subst e667; exact slawChunk_667 else
  if e668 : k = 668 then subst e668; exact slawChunk_668 else
  if e669 : k = 669 then subst e669; exact slawChunk_669 else
  if e670 : k = 670 then subst e670; exact slawChunk_670 else
  if e671 : k = 671 then subst e671; exact slawChunk_671 else
  omega
end D2
