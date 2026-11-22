import Ski.D2Base
import Ski.D2K.S262
/-! Generated.  S-law of D: chunks 2104..2111 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_2104 : slawChunk 2104 = true := by decide +kernel
theorem slawChunk_2105 : slawChunk 2105 = true := by decide +kernel
theorem slawChunk_2106 : slawChunk 2106 = true := by decide +kernel
theorem slawChunk_2107 : slawChunk 2107 = true := by decide +kernel
theorem slawChunk_2108 : slawChunk 2108 = true := by decide +kernel
theorem slawChunk_2109 : slawChunk 2109 = true := by decide +kernel
theorem slawChunk_2110 : slawChunk 2110 = true := by decide +kernel
theorem slawChunk_2111 : slawChunk 2111 = true := by decide +kernel
theorem slawC_263 (k : Nat) (h1 : 2104 ≤ k) (h2 : k < 2112) : slawChunk k = true := by
  if e2104 : k = 2104 then subst e2104; exact slawChunk_2104 else
  if e2105 : k = 2105 then subst e2105; exact slawChunk_2105 else
  if e2106 : k = 2106 then subst e2106; exact slawChunk_2106 else
  if e2107 : k = 2107 then subst e2107; exact slawChunk_2107 else
  if e2108 : k = 2108 then subst e2108; exact slawChunk_2108 else
  if e2109 : k = 2109 then subst e2109; exact slawChunk_2109 else
  if e2110 : k = 2110 then subst e2110; exact slawChunk_2110 else
  if e2111 : k = 2111 then subst e2111; exact slawChunk_2111 else
  omega
end D2
