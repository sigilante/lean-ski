import Ski.D2Base
import Ski.D2K.S331
/-! Generated.  S-law of D: chunks 2656..2663 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_2656 : slawChunk 2656 = true := by decide +kernel
theorem slawChunk_2657 : slawChunk 2657 = true := by decide +kernel
theorem slawChunk_2658 : slawChunk 2658 = true := by decide +kernel
theorem slawChunk_2659 : slawChunk 2659 = true := by decide +kernel
theorem slawChunk_2660 : slawChunk 2660 = true := by decide +kernel
theorem slawChunk_2661 : slawChunk 2661 = true := by decide +kernel
theorem slawChunk_2662 : slawChunk 2662 = true := by decide +kernel
theorem slawChunk_2663 : slawChunk 2663 = true := by decide +kernel
theorem slawC_332 (k : Nat) (h1 : 2656 ≤ k) (h2 : k < 2664) : slawChunk k = true := by
  if e2656 : k = 2656 then subst e2656; exact slawChunk_2656 else
  if e2657 : k = 2657 then subst e2657; exact slawChunk_2657 else
  if e2658 : k = 2658 then subst e2658; exact slawChunk_2658 else
  if e2659 : k = 2659 then subst e2659; exact slawChunk_2659 else
  if e2660 : k = 2660 then subst e2660; exact slawChunk_2660 else
  if e2661 : k = 2661 then subst e2661; exact slawChunk_2661 else
  if e2662 : k = 2662 then subst e2662; exact slawChunk_2662 else
  if e2663 : k = 2663 then subst e2663; exact slawChunk_2663 else
  omega
end D2
