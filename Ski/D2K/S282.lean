import Ski.D2Base
import Ski.D2K.S281
/-! Generated.  S-law of D: chunks 2256..2263 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_2256 : slawChunk 2256 = true := by decide +kernel
theorem slawChunk_2257 : slawChunk 2257 = true := by decide +kernel
theorem slawChunk_2258 : slawChunk 2258 = true := by decide +kernel
theorem slawChunk_2259 : slawChunk 2259 = true := by decide +kernel
theorem slawChunk_2260 : slawChunk 2260 = true := by decide +kernel
theorem slawChunk_2261 : slawChunk 2261 = true := by decide +kernel
theorem slawChunk_2262 : slawChunk 2262 = true := by decide +kernel
theorem slawChunk_2263 : slawChunk 2263 = true := by decide +kernel
theorem slawC_282 (k : Nat) (h1 : 2256 ≤ k) (h2 : k < 2264) : slawChunk k = true := by
  if e2256 : k = 2256 then subst e2256; exact slawChunk_2256 else
  if e2257 : k = 2257 then subst e2257; exact slawChunk_2257 else
  if e2258 : k = 2258 then subst e2258; exact slawChunk_2258 else
  if e2259 : k = 2259 then subst e2259; exact slawChunk_2259 else
  if e2260 : k = 2260 then subst e2260; exact slawChunk_2260 else
  if e2261 : k = 2261 then subst e2261; exact slawChunk_2261 else
  if e2262 : k = 2262 then subst e2262; exact slawChunk_2262 else
  if e2263 : k = 2263 then subst e2263; exact slawChunk_2263 else
  omega
end D2
