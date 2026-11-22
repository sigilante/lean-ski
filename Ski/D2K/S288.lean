import Ski.D2Base
import Ski.D2K.S287
/-! Generated.  S-law of D: chunks 2304..2311 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_2304 : slawChunk 2304 = true := by decide +kernel
theorem slawChunk_2305 : slawChunk 2305 = true := by decide +kernel
theorem slawChunk_2306 : slawChunk 2306 = true := by decide +kernel
theorem slawChunk_2307 : slawChunk 2307 = true := by decide +kernel
theorem slawChunk_2308 : slawChunk 2308 = true := by decide +kernel
theorem slawChunk_2309 : slawChunk 2309 = true := by decide +kernel
theorem slawChunk_2310 : slawChunk 2310 = true := by decide +kernel
theorem slawChunk_2311 : slawChunk 2311 = true := by decide +kernel
theorem slawC_288 (k : Nat) (h1 : 2304 ≤ k) (h2 : k < 2312) : slawChunk k = true := by
  if e2304 : k = 2304 then subst e2304; exact slawChunk_2304 else
  if e2305 : k = 2305 then subst e2305; exact slawChunk_2305 else
  if e2306 : k = 2306 then subst e2306; exact slawChunk_2306 else
  if e2307 : k = 2307 then subst e2307; exact slawChunk_2307 else
  if e2308 : k = 2308 then subst e2308; exact slawChunk_2308 else
  if e2309 : k = 2309 then subst e2309; exact slawChunk_2309 else
  if e2310 : k = 2310 then subst e2310; exact slawChunk_2310 else
  if e2311 : k = 2311 then subst e2311; exact slawChunk_2311 else
  omega
end D2
