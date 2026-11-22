import Ski.D2Base
import Ski.D2K.S173
/-! Generated.  S-law of D: chunks 1392..1399 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_1392 : slawChunk 1392 = true := by decide +kernel
theorem slawChunk_1393 : slawChunk 1393 = true := by decide +kernel
theorem slawChunk_1394 : slawChunk 1394 = true := by decide +kernel
theorem slawChunk_1395 : slawChunk 1395 = true := by decide +kernel
theorem slawChunk_1396 : slawChunk 1396 = true := by decide +kernel
theorem slawChunk_1397 : slawChunk 1397 = true := by decide +kernel
theorem slawChunk_1398 : slawChunk 1398 = true := by decide +kernel
theorem slawChunk_1399 : slawChunk 1399 = true := by decide +kernel
theorem slawC_174 (k : Nat) (h1 : 1392 ≤ k) (h2 : k < 1400) : slawChunk k = true := by
  if e1392 : k = 1392 then subst e1392; exact slawChunk_1392 else
  if e1393 : k = 1393 then subst e1393; exact slawChunk_1393 else
  if e1394 : k = 1394 then subst e1394; exact slawChunk_1394 else
  if e1395 : k = 1395 then subst e1395; exact slawChunk_1395 else
  if e1396 : k = 1396 then subst e1396; exact slawChunk_1396 else
  if e1397 : k = 1397 then subst e1397; exact slawChunk_1397 else
  if e1398 : k = 1398 then subst e1398; exact slawChunk_1398 else
  if e1399 : k = 1399 then subst e1399; exact slawChunk_1399 else
  omega
end D2
