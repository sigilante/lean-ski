import Ski.D2Base
import Ski.D2K.S34
/-! Generated.  S-law of D: chunks 280..287 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_280 : slawChunk 280 = true := by decide +kernel
theorem slawChunk_281 : slawChunk 281 = true := by decide +kernel
theorem slawChunk_282 : slawChunk 282 = true := by decide +kernel
theorem slawChunk_283 : slawChunk 283 = true := by decide +kernel
theorem slawChunk_284 : slawChunk 284 = true := by decide +kernel
theorem slawChunk_285 : slawChunk 285 = true := by decide +kernel
theorem slawChunk_286 : slawChunk 286 = true := by decide +kernel
theorem slawChunk_287 : slawChunk 287 = true := by decide +kernel
theorem slawC_35 (k : Nat) (h1 : 280 ≤ k) (h2 : k < 288) : slawChunk k = true := by
  if e280 : k = 280 then subst e280; exact slawChunk_280 else
  if e281 : k = 281 then subst e281; exact slawChunk_281 else
  if e282 : k = 282 then subst e282; exact slawChunk_282 else
  if e283 : k = 283 then subst e283; exact slawChunk_283 else
  if e284 : k = 284 then subst e284; exact slawChunk_284 else
  if e285 : k = 285 then subst e285; exact slawChunk_285 else
  if e286 : k = 286 then subst e286; exact slawChunk_286 else
  if e287 : k = 287 then subst e287; exact slawChunk_287 else
  omega
end D2
