import Ski.D2Base
import Ski.D2K.S257
/-! Generated.  S-law of D: chunks 2064..2071 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_2064 : slawChunk 2064 = true := by decide +kernel
theorem slawChunk_2065 : slawChunk 2065 = true := by decide +kernel
theorem slawChunk_2066 : slawChunk 2066 = true := by decide +kernel
theorem slawChunk_2067 : slawChunk 2067 = true := by decide +kernel
theorem slawChunk_2068 : slawChunk 2068 = true := by decide +kernel
theorem slawChunk_2069 : slawChunk 2069 = true := by decide +kernel
theorem slawChunk_2070 : slawChunk 2070 = true := by decide +kernel
theorem slawChunk_2071 : slawChunk 2071 = true := by decide +kernel
theorem slawC_258 (k : Nat) (h1 : 2064 ≤ k) (h2 : k < 2072) : slawChunk k = true := by
  if e2064 : k = 2064 then subst e2064; exact slawChunk_2064 else
  if e2065 : k = 2065 then subst e2065; exact slawChunk_2065 else
  if e2066 : k = 2066 then subst e2066; exact slawChunk_2066 else
  if e2067 : k = 2067 then subst e2067; exact slawChunk_2067 else
  if e2068 : k = 2068 then subst e2068; exact slawChunk_2068 else
  if e2069 : k = 2069 then subst e2069; exact slawChunk_2069 else
  if e2070 : k = 2070 then subst e2070; exact slawChunk_2070 else
  if e2071 : k = 2071 then subst e2071; exact slawChunk_2071 else
  omega
end D2
