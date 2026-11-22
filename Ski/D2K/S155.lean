import Ski.D2Base
import Ski.D2K.S154
/-! Generated.  S-law of D: chunks 1240..1247 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_1240 : slawChunk 1240 = true := by decide +kernel
theorem slawChunk_1241 : slawChunk 1241 = true := by decide +kernel
theorem slawChunk_1242 : slawChunk 1242 = true := by decide +kernel
theorem slawChunk_1243 : slawChunk 1243 = true := by decide +kernel
theorem slawChunk_1244 : slawChunk 1244 = true := by decide +kernel
theorem slawChunk_1245 : slawChunk 1245 = true := by decide +kernel
theorem slawChunk_1246 : slawChunk 1246 = true := by decide +kernel
theorem slawChunk_1247 : slawChunk 1247 = true := by decide +kernel
theorem slawC_155 (k : Nat) (h1 : 1240 ≤ k) (h2 : k < 1248) : slawChunk k = true := by
  if e1240 : k = 1240 then subst e1240; exact slawChunk_1240 else
  if e1241 : k = 1241 then subst e1241; exact slawChunk_1241 else
  if e1242 : k = 1242 then subst e1242; exact slawChunk_1242 else
  if e1243 : k = 1243 then subst e1243; exact slawChunk_1243 else
  if e1244 : k = 1244 then subst e1244; exact slawChunk_1244 else
  if e1245 : k = 1245 then subst e1245; exact slawChunk_1245 else
  if e1246 : k = 1246 then subst e1246; exact slawChunk_1246 else
  if e1247 : k = 1247 then subst e1247; exact slawChunk_1247 else
  omega
end D2
