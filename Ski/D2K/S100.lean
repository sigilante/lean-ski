import Ski.D2Base
import Ski.D2K.S99
/-! Generated.  S-law of D: chunks 800..807 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_800 : slawChunk 800 = true := by decide +kernel
theorem slawChunk_801 : slawChunk 801 = true := by decide +kernel
theorem slawChunk_802 : slawChunk 802 = true := by decide +kernel
theorem slawChunk_803 : slawChunk 803 = true := by decide +kernel
theorem slawChunk_804 : slawChunk 804 = true := by decide +kernel
theorem slawChunk_805 : slawChunk 805 = true := by decide +kernel
theorem slawChunk_806 : slawChunk 806 = true := by decide +kernel
theorem slawChunk_807 : slawChunk 807 = true := by decide +kernel
theorem slawC_100 (k : Nat) (h1 : 800 ≤ k) (h2 : k < 808) : slawChunk k = true := by
  if e800 : k = 800 then subst e800; exact slawChunk_800 else
  if e801 : k = 801 then subst e801; exact slawChunk_801 else
  if e802 : k = 802 then subst e802; exact slawChunk_802 else
  if e803 : k = 803 then subst e803; exact slawChunk_803 else
  if e804 : k = 804 then subst e804; exact slawChunk_804 else
  if e805 : k = 805 then subst e805; exact slawChunk_805 else
  if e806 : k = 806 then subst e806; exact slawChunk_806 else
  if e807 : k = 807 then subst e807; exact slawChunk_807 else
  omega
end D2
