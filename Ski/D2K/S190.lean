import Ski.D2Base
import Ski.D2K.S189
/-! Generated.  S-law of D: chunks 1520..1527 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_1520 : slawChunk 1520 = true := by decide +kernel
theorem slawChunk_1521 : slawChunk 1521 = true := by decide +kernel
theorem slawChunk_1522 : slawChunk 1522 = true := by decide +kernel
theorem slawChunk_1523 : slawChunk 1523 = true := by decide +kernel
theorem slawChunk_1524 : slawChunk 1524 = true := by decide +kernel
theorem slawChunk_1525 : slawChunk 1525 = true := by decide +kernel
theorem slawChunk_1526 : slawChunk 1526 = true := by decide +kernel
theorem slawChunk_1527 : slawChunk 1527 = true := by decide +kernel
theorem slawC_190 (k : Nat) (h1 : 1520 ≤ k) (h2 : k < 1528) : slawChunk k = true := by
  if e1520 : k = 1520 then subst e1520; exact slawChunk_1520 else
  if e1521 : k = 1521 then subst e1521; exact slawChunk_1521 else
  if e1522 : k = 1522 then subst e1522; exact slawChunk_1522 else
  if e1523 : k = 1523 then subst e1523; exact slawChunk_1523 else
  if e1524 : k = 1524 then subst e1524; exact slawChunk_1524 else
  if e1525 : k = 1525 then subst e1525; exact slawChunk_1525 else
  if e1526 : k = 1526 then subst e1526; exact slawChunk_1526 else
  if e1527 : k = 1527 then subst e1527; exact slawChunk_1527 else
  omega
end D2
