import Ski.D2Base
import Ski.D2K.S278
/-! Generated.  S-law of D: chunks 2232..2239 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_2232 : slawChunk 2232 = true := by decide +kernel
theorem slawChunk_2233 : slawChunk 2233 = true := by decide +kernel
theorem slawChunk_2234 : slawChunk 2234 = true := by decide +kernel
theorem slawChunk_2235 : slawChunk 2235 = true := by decide +kernel
theorem slawChunk_2236 : slawChunk 2236 = true := by decide +kernel
theorem slawChunk_2237 : slawChunk 2237 = true := by decide +kernel
theorem slawChunk_2238 : slawChunk 2238 = true := by decide +kernel
theorem slawChunk_2239 : slawChunk 2239 = true := by decide +kernel
theorem slawC_279 (k : Nat) (h1 : 2232 ≤ k) (h2 : k < 2240) : slawChunk k = true := by
  if e2232 : k = 2232 then subst e2232; exact slawChunk_2232 else
  if e2233 : k = 2233 then subst e2233; exact slawChunk_2233 else
  if e2234 : k = 2234 then subst e2234; exact slawChunk_2234 else
  if e2235 : k = 2235 then subst e2235; exact slawChunk_2235 else
  if e2236 : k = 2236 then subst e2236; exact slawChunk_2236 else
  if e2237 : k = 2237 then subst e2237; exact slawChunk_2237 else
  if e2238 : k = 2238 then subst e2238; exact slawChunk_2238 else
  if e2239 : k = 2239 then subst e2239; exact slawChunk_2239 else
  omega
end D2
