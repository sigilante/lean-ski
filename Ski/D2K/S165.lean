import Ski.D2Base
import Ski.D2K.S164
/-! Generated.  S-law of D: chunks 1320..1327 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_1320 : slawChunk 1320 = true := by decide +kernel
theorem slawChunk_1321 : slawChunk 1321 = true := by decide +kernel
theorem slawChunk_1322 : slawChunk 1322 = true := by decide +kernel
theorem slawChunk_1323 : slawChunk 1323 = true := by decide +kernel
theorem slawChunk_1324 : slawChunk 1324 = true := by decide +kernel
theorem slawChunk_1325 : slawChunk 1325 = true := by decide +kernel
theorem slawChunk_1326 : slawChunk 1326 = true := by decide +kernel
theorem slawChunk_1327 : slawChunk 1327 = true := by decide +kernel
theorem slawC_165 (k : Nat) (h1 : 1320 ≤ k) (h2 : k < 1328) : slawChunk k = true := by
  if e1320 : k = 1320 then subst e1320; exact slawChunk_1320 else
  if e1321 : k = 1321 then subst e1321; exact slawChunk_1321 else
  if e1322 : k = 1322 then subst e1322; exact slawChunk_1322 else
  if e1323 : k = 1323 then subst e1323; exact slawChunk_1323 else
  if e1324 : k = 1324 then subst e1324; exact slawChunk_1324 else
  if e1325 : k = 1325 then subst e1325; exact slawChunk_1325 else
  if e1326 : k = 1326 then subst e1326; exact slawChunk_1326 else
  if e1327 : k = 1327 then subst e1327; exact slawChunk_1327 else
  omega
end D2
