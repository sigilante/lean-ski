import Ski.D2Base
import Ski.D2K.S349
/-! Generated.  S-law of D: chunks 2800..2807 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_2800 : slawChunk 2800 = true := by decide +kernel
theorem slawChunk_2801 : slawChunk 2801 = true := by decide +kernel
theorem slawChunk_2802 : slawChunk 2802 = true := by decide +kernel
theorem slawChunk_2803 : slawChunk 2803 = true := by decide +kernel
theorem slawChunk_2804 : slawChunk 2804 = true := by decide +kernel
theorem slawChunk_2805 : slawChunk 2805 = true := by decide +kernel
theorem slawChunk_2806 : slawChunk 2806 = true := by decide +kernel
theorem slawChunk_2807 : slawChunk 2807 = true := by decide +kernel
theorem slawC_350 (k : Nat) (h1 : 2800 ≤ k) (h2 : k < 2808) : slawChunk k = true := by
  if e2800 : k = 2800 then subst e2800; exact slawChunk_2800 else
  if e2801 : k = 2801 then subst e2801; exact slawChunk_2801 else
  if e2802 : k = 2802 then subst e2802; exact slawChunk_2802 else
  if e2803 : k = 2803 then subst e2803; exact slawChunk_2803 else
  if e2804 : k = 2804 then subst e2804; exact slawChunk_2804 else
  if e2805 : k = 2805 then subst e2805; exact slawChunk_2805 else
  if e2806 : k = 2806 then subst e2806; exact slawChunk_2806 else
  if e2807 : k = 2807 then subst e2807; exact slawChunk_2807 else
  omega
end D2
