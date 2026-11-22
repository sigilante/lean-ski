import Ski.D2Base
import Ski.D2K.S263
/-! Generated.  S-law of D: chunks 2112..2119 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_2112 : slawChunk 2112 = true := by decide +kernel
theorem slawChunk_2113 : slawChunk 2113 = true := by decide +kernel
theorem slawChunk_2114 : slawChunk 2114 = true := by decide +kernel
theorem slawChunk_2115 : slawChunk 2115 = true := by decide +kernel
theorem slawChunk_2116 : slawChunk 2116 = true := by decide +kernel
theorem slawChunk_2117 : slawChunk 2117 = true := by decide +kernel
theorem slawChunk_2118 : slawChunk 2118 = true := by decide +kernel
theorem slawChunk_2119 : slawChunk 2119 = true := by decide +kernel
theorem slawC_264 (k : Nat) (h1 : 2112 ≤ k) (h2 : k < 2120) : slawChunk k = true := by
  if e2112 : k = 2112 then subst e2112; exact slawChunk_2112 else
  if e2113 : k = 2113 then subst e2113; exact slawChunk_2113 else
  if e2114 : k = 2114 then subst e2114; exact slawChunk_2114 else
  if e2115 : k = 2115 then subst e2115; exact slawChunk_2115 else
  if e2116 : k = 2116 then subst e2116; exact slawChunk_2116 else
  if e2117 : k = 2117 then subst e2117; exact slawChunk_2117 else
  if e2118 : k = 2118 then subst e2118; exact slawChunk_2118 else
  if e2119 : k = 2119 then subst e2119; exact slawChunk_2119 else
  omega
end D2
