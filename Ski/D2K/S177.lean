import Ski.D2Base
import Ski.D2K.S176
/-! Generated.  S-law of D: chunks 1416..1423 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_1416 : slawChunk 1416 = true := by decide +kernel
theorem slawChunk_1417 : slawChunk 1417 = true := by decide +kernel
theorem slawChunk_1418 : slawChunk 1418 = true := by decide +kernel
theorem slawChunk_1419 : slawChunk 1419 = true := by decide +kernel
theorem slawChunk_1420 : slawChunk 1420 = true := by decide +kernel
theorem slawChunk_1421 : slawChunk 1421 = true := by decide +kernel
theorem slawChunk_1422 : slawChunk 1422 = true := by decide +kernel
theorem slawChunk_1423 : slawChunk 1423 = true := by decide +kernel
theorem slawC_177 (k : Nat) (h1 : 1416 ≤ k) (h2 : k < 1424) : slawChunk k = true := by
  if e1416 : k = 1416 then subst e1416; exact slawChunk_1416 else
  if e1417 : k = 1417 then subst e1417; exact slawChunk_1417 else
  if e1418 : k = 1418 then subst e1418; exact slawChunk_1418 else
  if e1419 : k = 1419 then subst e1419; exact slawChunk_1419 else
  if e1420 : k = 1420 then subst e1420; exact slawChunk_1420 else
  if e1421 : k = 1421 then subst e1421; exact slawChunk_1421 else
  if e1422 : k = 1422 then subst e1422; exact slawChunk_1422 else
  if e1423 : k = 1423 then subst e1423; exact slawChunk_1423 else
  omega
end D2
