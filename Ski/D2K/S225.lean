import Ski.D2Base
import Ski.D2K.S224
/-! Generated.  S-law of D: chunks 1800..1807 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_1800 : slawChunk 1800 = true := by decide +kernel
theorem slawChunk_1801 : slawChunk 1801 = true := by decide +kernel
theorem slawChunk_1802 : slawChunk 1802 = true := by decide +kernel
theorem slawChunk_1803 : slawChunk 1803 = true := by decide +kernel
theorem slawChunk_1804 : slawChunk 1804 = true := by decide +kernel
theorem slawChunk_1805 : slawChunk 1805 = true := by decide +kernel
theorem slawChunk_1806 : slawChunk 1806 = true := by decide +kernel
theorem slawChunk_1807 : slawChunk 1807 = true := by decide +kernel
theorem slawC_225 (k : Nat) (h1 : 1800 ≤ k) (h2 : k < 1808) : slawChunk k = true := by
  if e1800 : k = 1800 then subst e1800; exact slawChunk_1800 else
  if e1801 : k = 1801 then subst e1801; exact slawChunk_1801 else
  if e1802 : k = 1802 then subst e1802; exact slawChunk_1802 else
  if e1803 : k = 1803 then subst e1803; exact slawChunk_1803 else
  if e1804 : k = 1804 then subst e1804; exact slawChunk_1804 else
  if e1805 : k = 1805 then subst e1805; exact slawChunk_1805 else
  if e1806 : k = 1806 then subst e1806; exact slawChunk_1806 else
  if e1807 : k = 1807 then subst e1807; exact slawChunk_1807 else
  omega
end D2
