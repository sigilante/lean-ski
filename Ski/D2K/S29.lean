import Ski.D2Base
import Ski.D2K.S28
/-! Generated.  S-law of D: chunks 232..239 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_232 : slawChunk 232 = true := by decide +kernel
theorem slawChunk_233 : slawChunk 233 = true := by decide +kernel
theorem slawChunk_234 : slawChunk 234 = true := by decide +kernel
theorem slawChunk_235 : slawChunk 235 = true := by decide +kernel
theorem slawChunk_236 : slawChunk 236 = true := by decide +kernel
theorem slawChunk_237 : slawChunk 237 = true := by decide +kernel
theorem slawChunk_238 : slawChunk 238 = true := by decide +kernel
theorem slawChunk_239 : slawChunk 239 = true := by decide +kernel
theorem slawC_29 (k : Nat) (h1 : 232 ≤ k) (h2 : k < 240) : slawChunk k = true := by
  if e232 : k = 232 then subst e232; exact slawChunk_232 else
  if e233 : k = 233 then subst e233; exact slawChunk_233 else
  if e234 : k = 234 then subst e234; exact slawChunk_234 else
  if e235 : k = 235 then subst e235; exact slawChunk_235 else
  if e236 : k = 236 then subst e236; exact slawChunk_236 else
  if e237 : k = 237 then subst e237; exact slawChunk_237 else
  if e238 : k = 238 then subst e238; exact slawChunk_238 else
  if e239 : k = 239 then subst e239; exact slawChunk_239 else
  omega
end D2
