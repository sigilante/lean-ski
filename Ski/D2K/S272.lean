import Ski.D2Base
import Ski.D2K.S271
/-! Generated.  S-law of D: chunks 2176..2183 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_2176 : slawChunk 2176 = true := by decide +kernel
theorem slawChunk_2177 : slawChunk 2177 = true := by decide +kernel
theorem slawChunk_2178 : slawChunk 2178 = true := by decide +kernel
theorem slawChunk_2179 : slawChunk 2179 = true := by decide +kernel
theorem slawChunk_2180 : slawChunk 2180 = true := by decide +kernel
theorem slawChunk_2181 : slawChunk 2181 = true := by decide +kernel
theorem slawChunk_2182 : slawChunk 2182 = true := by decide +kernel
theorem slawChunk_2183 : slawChunk 2183 = true := by decide +kernel
theorem slawC_272 (k : Nat) (h1 : 2176 ≤ k) (h2 : k < 2184) : slawChunk k = true := by
  if e2176 : k = 2176 then subst e2176; exact slawChunk_2176 else
  if e2177 : k = 2177 then subst e2177; exact slawChunk_2177 else
  if e2178 : k = 2178 then subst e2178; exact slawChunk_2178 else
  if e2179 : k = 2179 then subst e2179; exact slawChunk_2179 else
  if e2180 : k = 2180 then subst e2180; exact slawChunk_2180 else
  if e2181 : k = 2181 then subst e2181; exact slawChunk_2181 else
  if e2182 : k = 2182 then subst e2182; exact slawChunk_2182 else
  if e2183 : k = 2183 then subst e2183; exact slawChunk_2183 else
  omega
end D2
