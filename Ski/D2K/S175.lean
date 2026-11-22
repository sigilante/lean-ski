import Ski.D2Base
import Ski.D2K.S174
/-! Generated.  S-law of D: chunks 1400..1407 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_1400 : slawChunk 1400 = true := by decide +kernel
theorem slawChunk_1401 : slawChunk 1401 = true := by decide +kernel
theorem slawChunk_1402 : slawChunk 1402 = true := by decide +kernel
theorem slawChunk_1403 : slawChunk 1403 = true := by decide +kernel
theorem slawChunk_1404 : slawChunk 1404 = true := by decide +kernel
theorem slawChunk_1405 : slawChunk 1405 = true := by decide +kernel
theorem slawChunk_1406 : slawChunk 1406 = true := by decide +kernel
theorem slawChunk_1407 : slawChunk 1407 = true := by decide +kernel
theorem slawC_175 (k : Nat) (h1 : 1400 ≤ k) (h2 : k < 1408) : slawChunk k = true := by
  if e1400 : k = 1400 then subst e1400; exact slawChunk_1400 else
  if e1401 : k = 1401 then subst e1401; exact slawChunk_1401 else
  if e1402 : k = 1402 then subst e1402; exact slawChunk_1402 else
  if e1403 : k = 1403 then subst e1403; exact slawChunk_1403 else
  if e1404 : k = 1404 then subst e1404; exact slawChunk_1404 else
  if e1405 : k = 1405 then subst e1405; exact slawChunk_1405 else
  if e1406 : k = 1406 then subst e1406; exact slawChunk_1406 else
  if e1407 : k = 1407 then subst e1407; exact slawChunk_1407 else
  omega
end D2
