import Ski.D2Base
import Ski.D2K.S284
/-! Generated.  S-law of D: chunks 2280..2287 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_2280 : slawChunk 2280 = true := by decide +kernel
theorem slawChunk_2281 : slawChunk 2281 = true := by decide +kernel
theorem slawChunk_2282 : slawChunk 2282 = true := by decide +kernel
theorem slawChunk_2283 : slawChunk 2283 = true := by decide +kernel
theorem slawChunk_2284 : slawChunk 2284 = true := by decide +kernel
theorem slawChunk_2285 : slawChunk 2285 = true := by decide +kernel
theorem slawChunk_2286 : slawChunk 2286 = true := by decide +kernel
theorem slawChunk_2287 : slawChunk 2287 = true := by decide +kernel
theorem slawC_285 (k : Nat) (h1 : 2280 ≤ k) (h2 : k < 2288) : slawChunk k = true := by
  if e2280 : k = 2280 then subst e2280; exact slawChunk_2280 else
  if e2281 : k = 2281 then subst e2281; exact slawChunk_2281 else
  if e2282 : k = 2282 then subst e2282; exact slawChunk_2282 else
  if e2283 : k = 2283 then subst e2283; exact slawChunk_2283 else
  if e2284 : k = 2284 then subst e2284; exact slawChunk_2284 else
  if e2285 : k = 2285 then subst e2285; exact slawChunk_2285 else
  if e2286 : k = 2286 then subst e2286; exact slawChunk_2286 else
  if e2287 : k = 2287 then subst e2287; exact slawChunk_2287 else
  omega
end D2
