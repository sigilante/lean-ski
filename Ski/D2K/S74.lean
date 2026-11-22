import Ski.D2Base
import Ski.D2K.S73
/-! Generated.  S-law of D: chunks 592..599 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_592 : slawChunk 592 = true := by decide +kernel
theorem slawChunk_593 : slawChunk 593 = true := by decide +kernel
theorem slawChunk_594 : slawChunk 594 = true := by decide +kernel
theorem slawChunk_595 : slawChunk 595 = true := by decide +kernel
theorem slawChunk_596 : slawChunk 596 = true := by decide +kernel
theorem slawChunk_597 : slawChunk 597 = true := by decide +kernel
theorem slawChunk_598 : slawChunk 598 = true := by decide +kernel
theorem slawChunk_599 : slawChunk 599 = true := by decide +kernel
theorem slawC_74 (k : Nat) (h1 : 592 ≤ k) (h2 : k < 600) : slawChunk k = true := by
  if e592 : k = 592 then subst e592; exact slawChunk_592 else
  if e593 : k = 593 then subst e593; exact slawChunk_593 else
  if e594 : k = 594 then subst e594; exact slawChunk_594 else
  if e595 : k = 595 then subst e595; exact slawChunk_595 else
  if e596 : k = 596 then subst e596; exact slawChunk_596 else
  if e597 : k = 597 then subst e597; exact slawChunk_597 else
  if e598 : k = 598 then subst e598; exact slawChunk_598 else
  if e599 : k = 599 then subst e599; exact slawChunk_599 else
  omega
end D2
