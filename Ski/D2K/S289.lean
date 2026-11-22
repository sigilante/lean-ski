import Ski.D2Base
import Ski.D2K.S288
/-! Generated.  S-law of D: chunks 2312..2319 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_2312 : slawChunk 2312 = true := by decide +kernel
theorem slawChunk_2313 : slawChunk 2313 = true := by decide +kernel
theorem slawChunk_2314 : slawChunk 2314 = true := by decide +kernel
theorem slawChunk_2315 : slawChunk 2315 = true := by decide +kernel
theorem slawChunk_2316 : slawChunk 2316 = true := by decide +kernel
theorem slawChunk_2317 : slawChunk 2317 = true := by decide +kernel
theorem slawChunk_2318 : slawChunk 2318 = true := by decide +kernel
theorem slawChunk_2319 : slawChunk 2319 = true := by decide +kernel
theorem slawC_289 (k : Nat) (h1 : 2312 ≤ k) (h2 : k < 2320) : slawChunk k = true := by
  if e2312 : k = 2312 then subst e2312; exact slawChunk_2312 else
  if e2313 : k = 2313 then subst e2313; exact slawChunk_2313 else
  if e2314 : k = 2314 then subst e2314; exact slawChunk_2314 else
  if e2315 : k = 2315 then subst e2315; exact slawChunk_2315 else
  if e2316 : k = 2316 then subst e2316; exact slawChunk_2316 else
  if e2317 : k = 2317 then subst e2317; exact slawChunk_2317 else
  if e2318 : k = 2318 then subst e2318; exact slawChunk_2318 else
  if e2319 : k = 2319 then subst e2319; exact slawChunk_2319 else
  omega
end D2
