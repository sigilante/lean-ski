import Ski.D2Base
import Ski.D2K.S178
/-! Generated.  S-law of D: chunks 1432..1439 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_1432 : slawChunk 1432 = true := by decide +kernel
theorem slawChunk_1433 : slawChunk 1433 = true := by decide +kernel
theorem slawChunk_1434 : slawChunk 1434 = true := by decide +kernel
theorem slawChunk_1435 : slawChunk 1435 = true := by decide +kernel
theorem slawChunk_1436 : slawChunk 1436 = true := by decide +kernel
theorem slawChunk_1437 : slawChunk 1437 = true := by decide +kernel
theorem slawChunk_1438 : slawChunk 1438 = true := by decide +kernel
theorem slawChunk_1439 : slawChunk 1439 = true := by decide +kernel
theorem slawC_179 (k : Nat) (h1 : 1432 ≤ k) (h2 : k < 1440) : slawChunk k = true := by
  if e1432 : k = 1432 then subst e1432; exact slawChunk_1432 else
  if e1433 : k = 1433 then subst e1433; exact slawChunk_1433 else
  if e1434 : k = 1434 then subst e1434; exact slawChunk_1434 else
  if e1435 : k = 1435 then subst e1435; exact slawChunk_1435 else
  if e1436 : k = 1436 then subst e1436; exact slawChunk_1436 else
  if e1437 : k = 1437 then subst e1437; exact slawChunk_1437 else
  if e1438 : k = 1438 then subst e1438; exact slawChunk_1438 else
  if e1439 : k = 1439 then subst e1439; exact slawChunk_1439 else
  omega
end D2
