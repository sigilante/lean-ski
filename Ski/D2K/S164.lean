import Ski.D2Base
import Ski.D2K.S163
/-! Generated.  S-law of D: chunks 1312..1319 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_1312 : slawChunk 1312 = true := by decide +kernel
theorem slawChunk_1313 : slawChunk 1313 = true := by decide +kernel
theorem slawChunk_1314 : slawChunk 1314 = true := by decide +kernel
theorem slawChunk_1315 : slawChunk 1315 = true := by decide +kernel
theorem slawChunk_1316 : slawChunk 1316 = true := by decide +kernel
theorem slawChunk_1317 : slawChunk 1317 = true := by decide +kernel
theorem slawChunk_1318 : slawChunk 1318 = true := by decide +kernel
theorem slawChunk_1319 : slawChunk 1319 = true := by decide +kernel
theorem slawC_164 (k : Nat) (h1 : 1312 ≤ k) (h2 : k < 1320) : slawChunk k = true := by
  if e1312 : k = 1312 then subst e1312; exact slawChunk_1312 else
  if e1313 : k = 1313 then subst e1313; exact slawChunk_1313 else
  if e1314 : k = 1314 then subst e1314; exact slawChunk_1314 else
  if e1315 : k = 1315 then subst e1315; exact slawChunk_1315 else
  if e1316 : k = 1316 then subst e1316; exact slawChunk_1316 else
  if e1317 : k = 1317 then subst e1317; exact slawChunk_1317 else
  if e1318 : k = 1318 then subst e1318; exact slawChunk_1318 else
  if e1319 : k = 1319 then subst e1319; exact slawChunk_1319 else
  omega
end D2
