import Ski.D2Base
import Ski.D2K.S266
/-! Generated.  S-law of D: chunks 2136..2143 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_2136 : slawChunk 2136 = true := by decide +kernel
theorem slawChunk_2137 : slawChunk 2137 = true := by decide +kernel
theorem slawChunk_2138 : slawChunk 2138 = true := by decide +kernel
theorem slawChunk_2139 : slawChunk 2139 = true := by decide +kernel
theorem slawChunk_2140 : slawChunk 2140 = true := by decide +kernel
theorem slawChunk_2141 : slawChunk 2141 = true := by decide +kernel
theorem slawChunk_2142 : slawChunk 2142 = true := by decide +kernel
theorem slawChunk_2143 : slawChunk 2143 = true := by decide +kernel
theorem slawC_267 (k : Nat) (h1 : 2136 ≤ k) (h2 : k < 2144) : slawChunk k = true := by
  if e2136 : k = 2136 then subst e2136; exact slawChunk_2136 else
  if e2137 : k = 2137 then subst e2137; exact slawChunk_2137 else
  if e2138 : k = 2138 then subst e2138; exact slawChunk_2138 else
  if e2139 : k = 2139 then subst e2139; exact slawChunk_2139 else
  if e2140 : k = 2140 then subst e2140; exact slawChunk_2140 else
  if e2141 : k = 2141 then subst e2141; exact slawChunk_2141 else
  if e2142 : k = 2142 then subst e2142; exact slawChunk_2142 else
  if e2143 : k = 2143 then subst e2143; exact slawChunk_2143 else
  omega
end D2
