import Ski.D2Base
import Ski.D2K.S187
/-! Generated.  S-law of D: chunks 1504..1511 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_1504 : slawChunk 1504 = true := by decide +kernel
theorem slawChunk_1505 : slawChunk 1505 = true := by decide +kernel
theorem slawChunk_1506 : slawChunk 1506 = true := by decide +kernel
theorem slawChunk_1507 : slawChunk 1507 = true := by decide +kernel
theorem slawChunk_1508 : slawChunk 1508 = true := by decide +kernel
theorem slawChunk_1509 : slawChunk 1509 = true := by decide +kernel
theorem slawChunk_1510 : slawChunk 1510 = true := by decide +kernel
theorem slawChunk_1511 : slawChunk 1511 = true := by decide +kernel
theorem slawC_188 (k : Nat) (h1 : 1504 ≤ k) (h2 : k < 1512) : slawChunk k = true := by
  if e1504 : k = 1504 then subst e1504; exact slawChunk_1504 else
  if e1505 : k = 1505 then subst e1505; exact slawChunk_1505 else
  if e1506 : k = 1506 then subst e1506; exact slawChunk_1506 else
  if e1507 : k = 1507 then subst e1507; exact slawChunk_1507 else
  if e1508 : k = 1508 then subst e1508; exact slawChunk_1508 else
  if e1509 : k = 1509 then subst e1509; exact slawChunk_1509 else
  if e1510 : k = 1510 then subst e1510; exact slawChunk_1510 else
  if e1511 : k = 1511 then subst e1511; exact slawChunk_1511 else
  omega
end D2
