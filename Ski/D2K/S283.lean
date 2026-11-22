import Ski.D2Base
import Ski.D2K.S282
/-! Generated.  S-law of D: chunks 2264..2271 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_2264 : slawChunk 2264 = true := by decide +kernel
theorem slawChunk_2265 : slawChunk 2265 = true := by decide +kernel
theorem slawChunk_2266 : slawChunk 2266 = true := by decide +kernel
theorem slawChunk_2267 : slawChunk 2267 = true := by decide +kernel
theorem slawChunk_2268 : slawChunk 2268 = true := by decide +kernel
theorem slawChunk_2269 : slawChunk 2269 = true := by decide +kernel
theorem slawChunk_2270 : slawChunk 2270 = true := by decide +kernel
theorem slawChunk_2271 : slawChunk 2271 = true := by decide +kernel
theorem slawC_283 (k : Nat) (h1 : 2264 ≤ k) (h2 : k < 2272) : slawChunk k = true := by
  if e2264 : k = 2264 then subst e2264; exact slawChunk_2264 else
  if e2265 : k = 2265 then subst e2265; exact slawChunk_2265 else
  if e2266 : k = 2266 then subst e2266; exact slawChunk_2266 else
  if e2267 : k = 2267 then subst e2267; exact slawChunk_2267 else
  if e2268 : k = 2268 then subst e2268; exact slawChunk_2268 else
  if e2269 : k = 2269 then subst e2269; exact slawChunk_2269 else
  if e2270 : k = 2270 then subst e2270; exact slawChunk_2270 else
  if e2271 : k = 2271 then subst e2271; exact slawChunk_2271 else
  omega
end D2
