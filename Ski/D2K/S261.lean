import Ski.D2Base
import Ski.D2K.S260
/-! Generated.  S-law of D: chunks 2088..2095 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_2088 : slawChunk 2088 = true := by decide +kernel
theorem slawChunk_2089 : slawChunk 2089 = true := by decide +kernel
theorem slawChunk_2090 : slawChunk 2090 = true := by decide +kernel
theorem slawChunk_2091 : slawChunk 2091 = true := by decide +kernel
theorem slawChunk_2092 : slawChunk 2092 = true := by decide +kernel
theorem slawChunk_2093 : slawChunk 2093 = true := by decide +kernel
theorem slawChunk_2094 : slawChunk 2094 = true := by decide +kernel
theorem slawChunk_2095 : slawChunk 2095 = true := by decide +kernel
theorem slawC_261 (k : Nat) (h1 : 2088 ≤ k) (h2 : k < 2096) : slawChunk k = true := by
  if e2088 : k = 2088 then subst e2088; exact slawChunk_2088 else
  if e2089 : k = 2089 then subst e2089; exact slawChunk_2089 else
  if e2090 : k = 2090 then subst e2090; exact slawChunk_2090 else
  if e2091 : k = 2091 then subst e2091; exact slawChunk_2091 else
  if e2092 : k = 2092 then subst e2092; exact slawChunk_2092 else
  if e2093 : k = 2093 then subst e2093; exact slawChunk_2093 else
  if e2094 : k = 2094 then subst e2094; exact slawChunk_2094 else
  if e2095 : k = 2095 then subst e2095; exact slawChunk_2095 else
  omega
end D2
