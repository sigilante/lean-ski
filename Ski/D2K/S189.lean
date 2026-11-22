import Ski.D2Base
import Ski.D2K.S188
/-! Generated.  S-law of D: chunks 1512..1519 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_1512 : slawChunk 1512 = true := by decide +kernel
theorem slawChunk_1513 : slawChunk 1513 = true := by decide +kernel
theorem slawChunk_1514 : slawChunk 1514 = true := by decide +kernel
theorem slawChunk_1515 : slawChunk 1515 = true := by decide +kernel
theorem slawChunk_1516 : slawChunk 1516 = true := by decide +kernel
theorem slawChunk_1517 : slawChunk 1517 = true := by decide +kernel
theorem slawChunk_1518 : slawChunk 1518 = true := by decide +kernel
theorem slawChunk_1519 : slawChunk 1519 = true := by decide +kernel
theorem slawC_189 (k : Nat) (h1 : 1512 ≤ k) (h2 : k < 1520) : slawChunk k = true := by
  if e1512 : k = 1512 then subst e1512; exact slawChunk_1512 else
  if e1513 : k = 1513 then subst e1513; exact slawChunk_1513 else
  if e1514 : k = 1514 then subst e1514; exact slawChunk_1514 else
  if e1515 : k = 1515 then subst e1515; exact slawChunk_1515 else
  if e1516 : k = 1516 then subst e1516; exact slawChunk_1516 else
  if e1517 : k = 1517 then subst e1517; exact slawChunk_1517 else
  if e1518 : k = 1518 then subst e1518; exact slawChunk_1518 else
  if e1519 : k = 1519 then subst e1519; exact slawChunk_1519 else
  omega
end D2
