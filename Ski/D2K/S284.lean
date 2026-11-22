import Ski.D2Base
import Ski.D2K.S283
/-! Generated.  S-law of D: chunks 2272..2279 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_2272 : slawChunk 2272 = true := by decide +kernel
theorem slawChunk_2273 : slawChunk 2273 = true := by decide +kernel
theorem slawChunk_2274 : slawChunk 2274 = true := by decide +kernel
theorem slawChunk_2275 : slawChunk 2275 = true := by decide +kernel
theorem slawChunk_2276 : slawChunk 2276 = true := by decide +kernel
theorem slawChunk_2277 : slawChunk 2277 = true := by decide +kernel
theorem slawChunk_2278 : slawChunk 2278 = true := by decide +kernel
theorem slawChunk_2279 : slawChunk 2279 = true := by decide +kernel
theorem slawC_284 (k : Nat) (h1 : 2272 ≤ k) (h2 : k < 2280) : slawChunk k = true := by
  if e2272 : k = 2272 then subst e2272; exact slawChunk_2272 else
  if e2273 : k = 2273 then subst e2273; exact slawChunk_2273 else
  if e2274 : k = 2274 then subst e2274; exact slawChunk_2274 else
  if e2275 : k = 2275 then subst e2275; exact slawChunk_2275 else
  if e2276 : k = 2276 then subst e2276; exact slawChunk_2276 else
  if e2277 : k = 2277 then subst e2277; exact slawChunk_2277 else
  if e2278 : k = 2278 then subst e2278; exact slawChunk_2278 else
  if e2279 : k = 2279 then subst e2279; exact slawChunk_2279 else
  omega
end D2
