import Ski.D2Base
import Ski.D2K.S74
/-! Generated.  S-law of D: chunks 600..607 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_600 : slawChunk 600 = true := by decide +kernel
theorem slawChunk_601 : slawChunk 601 = true := by decide +kernel
theorem slawChunk_602 : slawChunk 602 = true := by decide +kernel
theorem slawChunk_603 : slawChunk 603 = true := by decide +kernel
theorem slawChunk_604 : slawChunk 604 = true := by decide +kernel
theorem slawChunk_605 : slawChunk 605 = true := by decide +kernel
theorem slawChunk_606 : slawChunk 606 = true := by decide +kernel
theorem slawChunk_607 : slawChunk 607 = true := by decide +kernel
theorem slawC_75 (k : Nat) (h1 : 600 ≤ k) (h2 : k < 608) : slawChunk k = true := by
  if e600 : k = 600 then subst e600; exact slawChunk_600 else
  if e601 : k = 601 then subst e601; exact slawChunk_601 else
  if e602 : k = 602 then subst e602; exact slawChunk_602 else
  if e603 : k = 603 then subst e603; exact slawChunk_603 else
  if e604 : k = 604 then subst e604; exact slawChunk_604 else
  if e605 : k = 605 then subst e605; exact slawChunk_605 else
  if e606 : k = 606 then subst e606; exact slawChunk_606 else
  if e607 : k = 607 then subst e607; exact slawChunk_607 else
  omega
end D2
