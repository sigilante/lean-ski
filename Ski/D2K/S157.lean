import Ski.D2Base
import Ski.D2K.S156
/-! Generated.  S-law of D: chunks 1256..1263 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_1256 : slawChunk 1256 = true := by decide +kernel
theorem slawChunk_1257 : slawChunk 1257 = true := by decide +kernel
theorem slawChunk_1258 : slawChunk 1258 = true := by decide +kernel
theorem slawChunk_1259 : slawChunk 1259 = true := by decide +kernel
theorem slawChunk_1260 : slawChunk 1260 = true := by decide +kernel
theorem slawChunk_1261 : slawChunk 1261 = true := by decide +kernel
theorem slawChunk_1262 : slawChunk 1262 = true := by decide +kernel
theorem slawChunk_1263 : slawChunk 1263 = true := by decide +kernel
theorem slawC_157 (k : Nat) (h1 : 1256 ≤ k) (h2 : k < 1264) : slawChunk k = true := by
  if e1256 : k = 1256 then subst e1256; exact slawChunk_1256 else
  if e1257 : k = 1257 then subst e1257; exact slawChunk_1257 else
  if e1258 : k = 1258 then subst e1258; exact slawChunk_1258 else
  if e1259 : k = 1259 then subst e1259; exact slawChunk_1259 else
  if e1260 : k = 1260 then subst e1260; exact slawChunk_1260 else
  if e1261 : k = 1261 then subst e1261; exact slawChunk_1261 else
  if e1262 : k = 1262 then subst e1262; exact slawChunk_1262 else
  if e1263 : k = 1263 then subst e1263; exact slawChunk_1263 else
  omega
end D2
