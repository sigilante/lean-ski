import Ski.D2Base
import Ski.D2K.S185
/-! Generated.  S-law of D: chunks 1488..1495 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_1488 : slawChunk 1488 = true := by decide +kernel
theorem slawChunk_1489 : slawChunk 1489 = true := by decide +kernel
theorem slawChunk_1490 : slawChunk 1490 = true := by decide +kernel
theorem slawChunk_1491 : slawChunk 1491 = true := by decide +kernel
theorem slawChunk_1492 : slawChunk 1492 = true := by decide +kernel
theorem slawChunk_1493 : slawChunk 1493 = true := by decide +kernel
theorem slawChunk_1494 : slawChunk 1494 = true := by decide +kernel
theorem slawChunk_1495 : slawChunk 1495 = true := by decide +kernel
theorem slawC_186 (k : Nat) (h1 : 1488 ≤ k) (h2 : k < 1496) : slawChunk k = true := by
  if e1488 : k = 1488 then subst e1488; exact slawChunk_1488 else
  if e1489 : k = 1489 then subst e1489; exact slawChunk_1489 else
  if e1490 : k = 1490 then subst e1490; exact slawChunk_1490 else
  if e1491 : k = 1491 then subst e1491; exact slawChunk_1491 else
  if e1492 : k = 1492 then subst e1492; exact slawChunk_1492 else
  if e1493 : k = 1493 then subst e1493; exact slawChunk_1493 else
  if e1494 : k = 1494 then subst e1494; exact slawChunk_1494 else
  if e1495 : k = 1495 then subst e1495; exact slawChunk_1495 else
  omega
end D2
