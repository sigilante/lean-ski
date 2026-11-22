import Ski.D2Base
import Ski.D2K.S175
/-! Generated.  S-law of D: chunks 1408..1415 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_1408 : slawChunk 1408 = true := by decide +kernel
theorem slawChunk_1409 : slawChunk 1409 = true := by decide +kernel
theorem slawChunk_1410 : slawChunk 1410 = true := by decide +kernel
theorem slawChunk_1411 : slawChunk 1411 = true := by decide +kernel
theorem slawChunk_1412 : slawChunk 1412 = true := by decide +kernel
theorem slawChunk_1413 : slawChunk 1413 = true := by decide +kernel
theorem slawChunk_1414 : slawChunk 1414 = true := by decide +kernel
theorem slawChunk_1415 : slawChunk 1415 = true := by decide +kernel
theorem slawC_176 (k : Nat) (h1 : 1408 ≤ k) (h2 : k < 1416) : slawChunk k = true := by
  if e1408 : k = 1408 then subst e1408; exact slawChunk_1408 else
  if e1409 : k = 1409 then subst e1409; exact slawChunk_1409 else
  if e1410 : k = 1410 then subst e1410; exact slawChunk_1410 else
  if e1411 : k = 1411 then subst e1411; exact slawChunk_1411 else
  if e1412 : k = 1412 then subst e1412; exact slawChunk_1412 else
  if e1413 : k = 1413 then subst e1413; exact slawChunk_1413 else
  if e1414 : k = 1414 then subst e1414; exact slawChunk_1414 else
  if e1415 : k = 1415 then subst e1415; exact slawChunk_1415 else
  omega
end D2
