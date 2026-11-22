import Ski.D2Base
import Ski.D2K.S324
/-! Generated.  S-law of D: chunks 2600..2607 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_2600 : slawChunk 2600 = true := by decide +kernel
theorem slawChunk_2601 : slawChunk 2601 = true := by decide +kernel
theorem slawChunk_2602 : slawChunk 2602 = true := by decide +kernel
theorem slawChunk_2603 : slawChunk 2603 = true := by decide +kernel
theorem slawChunk_2604 : slawChunk 2604 = true := by decide +kernel
theorem slawChunk_2605 : slawChunk 2605 = true := by decide +kernel
theorem slawChunk_2606 : slawChunk 2606 = true := by decide +kernel
theorem slawChunk_2607 : slawChunk 2607 = true := by decide +kernel
theorem slawC_325 (k : Nat) (h1 : 2600 ≤ k) (h2 : k < 2608) : slawChunk k = true := by
  if e2600 : k = 2600 then subst e2600; exact slawChunk_2600 else
  if e2601 : k = 2601 then subst e2601; exact slawChunk_2601 else
  if e2602 : k = 2602 then subst e2602; exact slawChunk_2602 else
  if e2603 : k = 2603 then subst e2603; exact slawChunk_2603 else
  if e2604 : k = 2604 then subst e2604; exact slawChunk_2604 else
  if e2605 : k = 2605 then subst e2605; exact slawChunk_2605 else
  if e2606 : k = 2606 then subst e2606; exact slawChunk_2606 else
  if e2607 : k = 2607 then subst e2607; exact slawChunk_2607 else
  omega
end D2
