import Ski.D2Base
import Ski.D2K.S279
/-! Generated.  S-law of D: chunks 2240..2247 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_2240 : slawChunk 2240 = true := by decide +kernel
theorem slawChunk_2241 : slawChunk 2241 = true := by decide +kernel
theorem slawChunk_2242 : slawChunk 2242 = true := by decide +kernel
theorem slawChunk_2243 : slawChunk 2243 = true := by decide +kernel
theorem slawChunk_2244 : slawChunk 2244 = true := by decide +kernel
theorem slawChunk_2245 : slawChunk 2245 = true := by decide +kernel
theorem slawChunk_2246 : slawChunk 2246 = true := by decide +kernel
theorem slawChunk_2247 : slawChunk 2247 = true := by decide +kernel
theorem slawC_280 (k : Nat) (h1 : 2240 ≤ k) (h2 : k < 2248) : slawChunk k = true := by
  if e2240 : k = 2240 then subst e2240; exact slawChunk_2240 else
  if e2241 : k = 2241 then subst e2241; exact slawChunk_2241 else
  if e2242 : k = 2242 then subst e2242; exact slawChunk_2242 else
  if e2243 : k = 2243 then subst e2243; exact slawChunk_2243 else
  if e2244 : k = 2244 then subst e2244; exact slawChunk_2244 else
  if e2245 : k = 2245 then subst e2245; exact slawChunk_2245 else
  if e2246 : k = 2246 then subst e2246; exact slawChunk_2246 else
  if e2247 : k = 2247 then subst e2247; exact slawChunk_2247 else
  omega
end D2
