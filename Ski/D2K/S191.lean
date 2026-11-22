import Ski.D2Base
import Ski.D2K.S190
/-! Generated.  S-law of D: chunks 1528..1535 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_1528 : slawChunk 1528 = true := by decide +kernel
theorem slawChunk_1529 : slawChunk 1529 = true := by decide +kernel
theorem slawChunk_1530 : slawChunk 1530 = true := by decide +kernel
theorem slawChunk_1531 : slawChunk 1531 = true := by decide +kernel
theorem slawChunk_1532 : slawChunk 1532 = true := by decide +kernel
theorem slawChunk_1533 : slawChunk 1533 = true := by decide +kernel
theorem slawChunk_1534 : slawChunk 1534 = true := by decide +kernel
theorem slawChunk_1535 : slawChunk 1535 = true := by decide +kernel
theorem slawC_191 (k : Nat) (h1 : 1528 ≤ k) (h2 : k < 1536) : slawChunk k = true := by
  if e1528 : k = 1528 then subst e1528; exact slawChunk_1528 else
  if e1529 : k = 1529 then subst e1529; exact slawChunk_1529 else
  if e1530 : k = 1530 then subst e1530; exact slawChunk_1530 else
  if e1531 : k = 1531 then subst e1531; exact slawChunk_1531 else
  if e1532 : k = 1532 then subst e1532; exact slawChunk_1532 else
  if e1533 : k = 1533 then subst e1533; exact slawChunk_1533 else
  if e1534 : k = 1534 then subst e1534; exact slawChunk_1534 else
  if e1535 : k = 1535 then subst e1535; exact slawChunk_1535 else
  omega
end D2
