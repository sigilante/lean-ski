import Ski.D2Base
import Ski.D2K.S81
/-! Generated.  S-law of D: chunks 656..663 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_656 : slawChunk 656 = true := by decide +kernel
theorem slawChunk_657 : slawChunk 657 = true := by decide +kernel
theorem slawChunk_658 : slawChunk 658 = true := by decide +kernel
theorem slawChunk_659 : slawChunk 659 = true := by decide +kernel
theorem slawChunk_660 : slawChunk 660 = true := by decide +kernel
theorem slawChunk_661 : slawChunk 661 = true := by decide +kernel
theorem slawChunk_662 : slawChunk 662 = true := by decide +kernel
theorem slawChunk_663 : slawChunk 663 = true := by decide +kernel
theorem slawC_82 (k : Nat) (h1 : 656 ≤ k) (h2 : k < 664) : slawChunk k = true := by
  if e656 : k = 656 then subst e656; exact slawChunk_656 else
  if e657 : k = 657 then subst e657; exact slawChunk_657 else
  if e658 : k = 658 then subst e658; exact slawChunk_658 else
  if e659 : k = 659 then subst e659; exact slawChunk_659 else
  if e660 : k = 660 then subst e660; exact slawChunk_660 else
  if e661 : k = 661 then subst e661; exact slawChunk_661 else
  if e662 : k = 662 then subst e662; exact slawChunk_662 else
  if e663 : k = 663 then subst e663; exact slawChunk_663 else
  omega
end D2
