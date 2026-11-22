import Ski.D2Base
import Ski.D2K.S32
/-! Generated.  S-law of D: chunks 264..271 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_264 : slawChunk 264 = true := by decide +kernel
theorem slawChunk_265 : slawChunk 265 = true := by decide +kernel
theorem slawChunk_266 : slawChunk 266 = true := by decide +kernel
theorem slawChunk_267 : slawChunk 267 = true := by decide +kernel
theorem slawChunk_268 : slawChunk 268 = true := by decide +kernel
theorem slawChunk_269 : slawChunk 269 = true := by decide +kernel
theorem slawChunk_270 : slawChunk 270 = true := by decide +kernel
theorem slawChunk_271 : slawChunk 271 = true := by decide +kernel
theorem slawC_33 (k : Nat) (h1 : 264 ≤ k) (h2 : k < 272) : slawChunk k = true := by
  if e264 : k = 264 then subst e264; exact slawChunk_264 else
  if e265 : k = 265 then subst e265; exact slawChunk_265 else
  if e266 : k = 266 then subst e266; exact slawChunk_266 else
  if e267 : k = 267 then subst e267; exact slawChunk_267 else
  if e268 : k = 268 then subst e268; exact slawChunk_268 else
  if e269 : k = 269 then subst e269; exact slawChunk_269 else
  if e270 : k = 270 then subst e270; exact slawChunk_270 else
  if e271 : k = 271 then subst e271; exact slawChunk_271 else
  omega
end D2
