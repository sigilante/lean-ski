import Ski.D2Base
import Ski.D2K.S31
/-! Generated.  S-law of D: chunks 256..263 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_256 : slawChunk 256 = true := by decide +kernel
theorem slawChunk_257 : slawChunk 257 = true := by decide +kernel
theorem slawChunk_258 : slawChunk 258 = true := by decide +kernel
theorem slawChunk_259 : slawChunk 259 = true := by decide +kernel
theorem slawChunk_260 : slawChunk 260 = true := by decide +kernel
theorem slawChunk_261 : slawChunk 261 = true := by decide +kernel
theorem slawChunk_262 : slawChunk 262 = true := by decide +kernel
theorem slawChunk_263 : slawChunk 263 = true := by decide +kernel
theorem slawC_32 (k : Nat) (h1 : 256 ≤ k) (h2 : k < 264) : slawChunk k = true := by
  if e256 : k = 256 then subst e256; exact slawChunk_256 else
  if e257 : k = 257 then subst e257; exact slawChunk_257 else
  if e258 : k = 258 then subst e258; exact slawChunk_258 else
  if e259 : k = 259 then subst e259; exact slawChunk_259 else
  if e260 : k = 260 then subst e260; exact slawChunk_260 else
  if e261 : k = 261 then subst e261; exact slawChunk_261 else
  if e262 : k = 262 then subst e262; exact slawChunk_262 else
  if e263 : k = 263 then subst e263; exact slawChunk_263 else
  omega
end D2
