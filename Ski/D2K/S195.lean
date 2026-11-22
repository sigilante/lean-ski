import Ski.D2Base
import Ski.D2K.S194
/-! Generated.  S-law of D: chunks 1560..1567 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_1560 : slawChunk 1560 = true := by decide +kernel
theorem slawChunk_1561 : slawChunk 1561 = true := by decide +kernel
theorem slawChunk_1562 : slawChunk 1562 = true := by decide +kernel
theorem slawChunk_1563 : slawChunk 1563 = true := by decide +kernel
theorem slawChunk_1564 : slawChunk 1564 = true := by decide +kernel
theorem slawChunk_1565 : slawChunk 1565 = true := by decide +kernel
theorem slawChunk_1566 : slawChunk 1566 = true := by decide +kernel
theorem slawChunk_1567 : slawChunk 1567 = true := by decide +kernel
theorem slawC_195 (k : Nat) (h1 : 1560 ≤ k) (h2 : k < 1568) : slawChunk k = true := by
  if e1560 : k = 1560 then subst e1560; exact slawChunk_1560 else
  if e1561 : k = 1561 then subst e1561; exact slawChunk_1561 else
  if e1562 : k = 1562 then subst e1562; exact slawChunk_1562 else
  if e1563 : k = 1563 then subst e1563; exact slawChunk_1563 else
  if e1564 : k = 1564 then subst e1564; exact slawChunk_1564 else
  if e1565 : k = 1565 then subst e1565; exact slawChunk_1565 else
  if e1566 : k = 1566 then subst e1566; exact slawChunk_1566 else
  if e1567 : k = 1567 then subst e1567; exact slawChunk_1567 else
  omega
end D2
