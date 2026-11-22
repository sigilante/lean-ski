import Ski.D2Base
import Ski.D2K.S182
/-! Generated.  S-law of D: chunks 1464..1471 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_1464 : slawChunk 1464 = true := by decide +kernel
theorem slawChunk_1465 : slawChunk 1465 = true := by decide +kernel
theorem slawChunk_1466 : slawChunk 1466 = true := by decide +kernel
theorem slawChunk_1467 : slawChunk 1467 = true := by decide +kernel
theorem slawChunk_1468 : slawChunk 1468 = true := by decide +kernel
theorem slawChunk_1469 : slawChunk 1469 = true := by decide +kernel
theorem slawChunk_1470 : slawChunk 1470 = true := by decide +kernel
theorem slawChunk_1471 : slawChunk 1471 = true := by decide +kernel
theorem slawC_183 (k : Nat) (h1 : 1464 ≤ k) (h2 : k < 1472) : slawChunk k = true := by
  if e1464 : k = 1464 then subst e1464; exact slawChunk_1464 else
  if e1465 : k = 1465 then subst e1465; exact slawChunk_1465 else
  if e1466 : k = 1466 then subst e1466; exact slawChunk_1466 else
  if e1467 : k = 1467 then subst e1467; exact slawChunk_1467 else
  if e1468 : k = 1468 then subst e1468; exact slawChunk_1468 else
  if e1469 : k = 1469 then subst e1469; exact slawChunk_1469 else
  if e1470 : k = 1470 then subst e1470; exact slawChunk_1470 else
  if e1471 : k = 1471 then subst e1471; exact slawChunk_1471 else
  omega
end D2
