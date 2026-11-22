import Ski.D2Base
import Ski.D2K.S161
/-! Generated.  S-law of D: chunks 1296..1303 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_1296 : slawChunk 1296 = true := by decide +kernel
theorem slawChunk_1297 : slawChunk 1297 = true := by decide +kernel
theorem slawChunk_1298 : slawChunk 1298 = true := by decide +kernel
theorem slawChunk_1299 : slawChunk 1299 = true := by decide +kernel
theorem slawChunk_1300 : slawChunk 1300 = true := by decide +kernel
theorem slawChunk_1301 : slawChunk 1301 = true := by decide +kernel
theorem slawChunk_1302 : slawChunk 1302 = true := by decide +kernel
theorem slawChunk_1303 : slawChunk 1303 = true := by decide +kernel
theorem slawC_162 (k : Nat) (h1 : 1296 ≤ k) (h2 : k < 1304) : slawChunk k = true := by
  if e1296 : k = 1296 then subst e1296; exact slawChunk_1296 else
  if e1297 : k = 1297 then subst e1297; exact slawChunk_1297 else
  if e1298 : k = 1298 then subst e1298; exact slawChunk_1298 else
  if e1299 : k = 1299 then subst e1299; exact slawChunk_1299 else
  if e1300 : k = 1300 then subst e1300; exact slawChunk_1300 else
  if e1301 : k = 1301 then subst e1301; exact slawChunk_1301 else
  if e1302 : k = 1302 then subst e1302; exact slawChunk_1302 else
  if e1303 : k = 1303 then subst e1303; exact slawChunk_1303 else
  omega
end D2
