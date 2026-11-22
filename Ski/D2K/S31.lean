import Ski.D2Base
import Ski.D2K.S30
/-! Generated.  S-law of D: chunks 248..255 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_248 : slawChunk 248 = true := by decide +kernel
theorem slawChunk_249 : slawChunk 249 = true := by decide +kernel
theorem slawChunk_250 : slawChunk 250 = true := by decide +kernel
theorem slawChunk_251 : slawChunk 251 = true := by decide +kernel
theorem slawChunk_252 : slawChunk 252 = true := by decide +kernel
theorem slawChunk_253 : slawChunk 253 = true := by decide +kernel
theorem slawChunk_254 : slawChunk 254 = true := by decide +kernel
theorem slawChunk_255 : slawChunk 255 = true := by decide +kernel
theorem slawC_31 (k : Nat) (h1 : 248 ≤ k) (h2 : k < 256) : slawChunk k = true := by
  if e248 : k = 248 then subst e248; exact slawChunk_248 else
  if e249 : k = 249 then subst e249; exact slawChunk_249 else
  if e250 : k = 250 then subst e250; exact slawChunk_250 else
  if e251 : k = 251 then subst e251; exact slawChunk_251 else
  if e252 : k = 252 then subst e252; exact slawChunk_252 else
  if e253 : k = 253 then subst e253; exact slawChunk_253 else
  if e254 : k = 254 then subst e254; exact slawChunk_254 else
  if e255 : k = 255 then subst e255; exact slawChunk_255 else
  omega
end D2
