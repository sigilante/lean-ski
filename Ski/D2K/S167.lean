import Ski.D2Base
import Ski.D2K.S166
/-! Generated.  S-law of D: chunks 1336..1343 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_1336 : slawChunk 1336 = true := by decide +kernel
theorem slawChunk_1337 : slawChunk 1337 = true := by decide +kernel
theorem slawChunk_1338 : slawChunk 1338 = true := by decide +kernel
theorem slawChunk_1339 : slawChunk 1339 = true := by decide +kernel
theorem slawChunk_1340 : slawChunk 1340 = true := by decide +kernel
theorem slawChunk_1341 : slawChunk 1341 = true := by decide +kernel
theorem slawChunk_1342 : slawChunk 1342 = true := by decide +kernel
theorem slawChunk_1343 : slawChunk 1343 = true := by decide +kernel
theorem slawC_167 (k : Nat) (h1 : 1336 ≤ k) (h2 : k < 1344) : slawChunk k = true := by
  if e1336 : k = 1336 then subst e1336; exact slawChunk_1336 else
  if e1337 : k = 1337 then subst e1337; exact slawChunk_1337 else
  if e1338 : k = 1338 then subst e1338; exact slawChunk_1338 else
  if e1339 : k = 1339 then subst e1339; exact slawChunk_1339 else
  if e1340 : k = 1340 then subst e1340; exact slawChunk_1340 else
  if e1341 : k = 1341 then subst e1341; exact slawChunk_1341 else
  if e1342 : k = 1342 then subst e1342; exact slawChunk_1342 else
  if e1343 : k = 1343 then subst e1343; exact slawChunk_1343 else
  omega
end D2
