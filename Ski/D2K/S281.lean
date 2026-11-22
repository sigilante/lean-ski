import Ski.D2Base
import Ski.D2K.S280
/-! Generated.  S-law of D: chunks 2248..2255 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_2248 : slawChunk 2248 = true := by decide +kernel
theorem slawChunk_2249 : slawChunk 2249 = true := by decide +kernel
theorem slawChunk_2250 : slawChunk 2250 = true := by decide +kernel
theorem slawChunk_2251 : slawChunk 2251 = true := by decide +kernel
theorem slawChunk_2252 : slawChunk 2252 = true := by decide +kernel
theorem slawChunk_2253 : slawChunk 2253 = true := by decide +kernel
theorem slawChunk_2254 : slawChunk 2254 = true := by decide +kernel
theorem slawChunk_2255 : slawChunk 2255 = true := by decide +kernel
theorem slawC_281 (k : Nat) (h1 : 2248 ≤ k) (h2 : k < 2256) : slawChunk k = true := by
  if e2248 : k = 2248 then subst e2248; exact slawChunk_2248 else
  if e2249 : k = 2249 then subst e2249; exact slawChunk_2249 else
  if e2250 : k = 2250 then subst e2250; exact slawChunk_2250 else
  if e2251 : k = 2251 then subst e2251; exact slawChunk_2251 else
  if e2252 : k = 2252 then subst e2252; exact slawChunk_2252 else
  if e2253 : k = 2253 then subst e2253; exact slawChunk_2253 else
  if e2254 : k = 2254 then subst e2254; exact slawChunk_2254 else
  if e2255 : k = 2255 then subst e2255; exact slawChunk_2255 else
  omega
end D2
