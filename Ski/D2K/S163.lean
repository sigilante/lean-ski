import Ski.D2Base
import Ski.D2K.S162
/-! Generated.  S-law of D: chunks 1304..1311 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_1304 : slawChunk 1304 = true := by decide +kernel
theorem slawChunk_1305 : slawChunk 1305 = true := by decide +kernel
theorem slawChunk_1306 : slawChunk 1306 = true := by decide +kernel
theorem slawChunk_1307 : slawChunk 1307 = true := by decide +kernel
theorem slawChunk_1308 : slawChunk 1308 = true := by decide +kernel
theorem slawChunk_1309 : slawChunk 1309 = true := by decide +kernel
theorem slawChunk_1310 : slawChunk 1310 = true := by decide +kernel
theorem slawChunk_1311 : slawChunk 1311 = true := by decide +kernel
theorem slawC_163 (k : Nat) (h1 : 1304 ≤ k) (h2 : k < 1312) : slawChunk k = true := by
  if e1304 : k = 1304 then subst e1304; exact slawChunk_1304 else
  if e1305 : k = 1305 then subst e1305; exact slawChunk_1305 else
  if e1306 : k = 1306 then subst e1306; exact slawChunk_1306 else
  if e1307 : k = 1307 then subst e1307; exact slawChunk_1307 else
  if e1308 : k = 1308 then subst e1308; exact slawChunk_1308 else
  if e1309 : k = 1309 then subst e1309; exact slawChunk_1309 else
  if e1310 : k = 1310 then subst e1310; exact slawChunk_1310 else
  if e1311 : k = 1311 then subst e1311; exact slawChunk_1311 else
  omega
end D2
