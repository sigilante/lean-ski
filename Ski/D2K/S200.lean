import Ski.D2Base
import Ski.D2K.S199
/-! Generated.  S-law of D: chunks 1600..1607 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_1600 : slawChunk 1600 = true := by decide +kernel
theorem slawChunk_1601 : slawChunk 1601 = true := by decide +kernel
theorem slawChunk_1602 : slawChunk 1602 = true := by decide +kernel
theorem slawChunk_1603 : slawChunk 1603 = true := by decide +kernel
theorem slawChunk_1604 : slawChunk 1604 = true := by decide +kernel
theorem slawChunk_1605 : slawChunk 1605 = true := by decide +kernel
theorem slawChunk_1606 : slawChunk 1606 = true := by decide +kernel
theorem slawChunk_1607 : slawChunk 1607 = true := by decide +kernel
theorem slawC_200 (k : Nat) (h1 : 1600 ≤ k) (h2 : k < 1608) : slawChunk k = true := by
  if e1600 : k = 1600 then subst e1600; exact slawChunk_1600 else
  if e1601 : k = 1601 then subst e1601; exact slawChunk_1601 else
  if e1602 : k = 1602 then subst e1602; exact slawChunk_1602 else
  if e1603 : k = 1603 then subst e1603; exact slawChunk_1603 else
  if e1604 : k = 1604 then subst e1604; exact slawChunk_1604 else
  if e1605 : k = 1605 then subst e1605; exact slawChunk_1605 else
  if e1606 : k = 1606 then subst e1606; exact slawChunk_1606 else
  if e1607 : k = 1607 then subst e1607; exact slawChunk_1607 else
  omega
end D2
