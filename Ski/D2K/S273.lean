import Ski.D2Base
import Ski.D2K.S272
/-! Generated.  S-law of D: chunks 2184..2191 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_2184 : slawChunk 2184 = true := by decide +kernel
theorem slawChunk_2185 : slawChunk 2185 = true := by decide +kernel
theorem slawChunk_2186 : slawChunk 2186 = true := by decide +kernel
theorem slawChunk_2187 : slawChunk 2187 = true := by decide +kernel
theorem slawChunk_2188 : slawChunk 2188 = true := by decide +kernel
theorem slawChunk_2189 : slawChunk 2189 = true := by decide +kernel
theorem slawChunk_2190 : slawChunk 2190 = true := by decide +kernel
theorem slawChunk_2191 : slawChunk 2191 = true := by decide +kernel
theorem slawC_273 (k : Nat) (h1 : 2184 ≤ k) (h2 : k < 2192) : slawChunk k = true := by
  if e2184 : k = 2184 then subst e2184; exact slawChunk_2184 else
  if e2185 : k = 2185 then subst e2185; exact slawChunk_2185 else
  if e2186 : k = 2186 then subst e2186; exact slawChunk_2186 else
  if e2187 : k = 2187 then subst e2187; exact slawChunk_2187 else
  if e2188 : k = 2188 then subst e2188; exact slawChunk_2188 else
  if e2189 : k = 2189 then subst e2189; exact slawChunk_2189 else
  if e2190 : k = 2190 then subst e2190; exact slawChunk_2190 else
  if e2191 : k = 2191 then subst e2191; exact slawChunk_2191 else
  omega
end D2
