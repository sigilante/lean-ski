import Ski.D2Base
import Ski.D2K.S158
/-! Generated.  S-law of D: chunks 1272..1279 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_1272 : slawChunk 1272 = true := by decide +kernel
theorem slawChunk_1273 : slawChunk 1273 = true := by decide +kernel
theorem slawChunk_1274 : slawChunk 1274 = true := by decide +kernel
theorem slawChunk_1275 : slawChunk 1275 = true := by decide +kernel
theorem slawChunk_1276 : slawChunk 1276 = true := by decide +kernel
theorem slawChunk_1277 : slawChunk 1277 = true := by decide +kernel
theorem slawChunk_1278 : slawChunk 1278 = true := by decide +kernel
theorem slawChunk_1279 : slawChunk 1279 = true := by decide +kernel
theorem slawC_159 (k : Nat) (h1 : 1272 ≤ k) (h2 : k < 1280) : slawChunk k = true := by
  if e1272 : k = 1272 then subst e1272; exact slawChunk_1272 else
  if e1273 : k = 1273 then subst e1273; exact slawChunk_1273 else
  if e1274 : k = 1274 then subst e1274; exact slawChunk_1274 else
  if e1275 : k = 1275 then subst e1275; exact slawChunk_1275 else
  if e1276 : k = 1276 then subst e1276; exact slawChunk_1276 else
  if e1277 : k = 1277 then subst e1277; exact slawChunk_1277 else
  if e1278 : k = 1278 then subst e1278; exact slawChunk_1278 else
  if e1279 : k = 1279 then subst e1279; exact slawChunk_1279 else
  omega
end D2
