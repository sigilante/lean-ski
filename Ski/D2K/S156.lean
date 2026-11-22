import Ski.D2Base
import Ski.D2K.S155
/-! Generated.  S-law of D: chunks 1248..1255 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_1248 : slawChunk 1248 = true := by decide +kernel
theorem slawChunk_1249 : slawChunk 1249 = true := by decide +kernel
theorem slawChunk_1250 : slawChunk 1250 = true := by decide +kernel
theorem slawChunk_1251 : slawChunk 1251 = true := by decide +kernel
theorem slawChunk_1252 : slawChunk 1252 = true := by decide +kernel
theorem slawChunk_1253 : slawChunk 1253 = true := by decide +kernel
theorem slawChunk_1254 : slawChunk 1254 = true := by decide +kernel
theorem slawChunk_1255 : slawChunk 1255 = true := by decide +kernel
theorem slawC_156 (k : Nat) (h1 : 1248 ≤ k) (h2 : k < 1256) : slawChunk k = true := by
  if e1248 : k = 1248 then subst e1248; exact slawChunk_1248 else
  if e1249 : k = 1249 then subst e1249; exact slawChunk_1249 else
  if e1250 : k = 1250 then subst e1250; exact slawChunk_1250 else
  if e1251 : k = 1251 then subst e1251; exact slawChunk_1251 else
  if e1252 : k = 1252 then subst e1252; exact slawChunk_1252 else
  if e1253 : k = 1253 then subst e1253; exact slawChunk_1253 else
  if e1254 : k = 1254 then subst e1254; exact slawChunk_1254 else
  if e1255 : k = 1255 then subst e1255; exact slawChunk_1255 else
  omega
end D2
