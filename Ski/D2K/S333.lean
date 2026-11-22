import Ski.D2Base
import Ski.D2K.S332
/-! Generated.  S-law of D: chunks 2664..2671 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_2664 : slawChunk 2664 = true := by decide +kernel
theorem slawChunk_2665 : slawChunk 2665 = true := by decide +kernel
theorem slawChunk_2666 : slawChunk 2666 = true := by decide +kernel
theorem slawChunk_2667 : slawChunk 2667 = true := by decide +kernel
theorem slawChunk_2668 : slawChunk 2668 = true := by decide +kernel
theorem slawChunk_2669 : slawChunk 2669 = true := by decide +kernel
theorem slawChunk_2670 : slawChunk 2670 = true := by decide +kernel
theorem slawChunk_2671 : slawChunk 2671 = true := by decide +kernel
theorem slawC_333 (k : Nat) (h1 : 2664 ≤ k) (h2 : k < 2672) : slawChunk k = true := by
  if e2664 : k = 2664 then subst e2664; exact slawChunk_2664 else
  if e2665 : k = 2665 then subst e2665; exact slawChunk_2665 else
  if e2666 : k = 2666 then subst e2666; exact slawChunk_2666 else
  if e2667 : k = 2667 then subst e2667; exact slawChunk_2667 else
  if e2668 : k = 2668 then subst e2668; exact slawChunk_2668 else
  if e2669 : k = 2669 then subst e2669; exact slawChunk_2669 else
  if e2670 : k = 2670 then subst e2670; exact slawChunk_2670 else
  if e2671 : k = 2671 then subst e2671; exact slawChunk_2671 else
  omega
end D2
