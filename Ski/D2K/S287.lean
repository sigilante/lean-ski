import Ski.D2Base
import Ski.D2K.S286
/-! Generated.  S-law of D: chunks 2296..2303 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_2296 : slawChunk 2296 = true := by decide +kernel
theorem slawChunk_2297 : slawChunk 2297 = true := by decide +kernel
theorem slawChunk_2298 : slawChunk 2298 = true := by decide +kernel
theorem slawChunk_2299 : slawChunk 2299 = true := by decide +kernel
theorem slawChunk_2300 : slawChunk 2300 = true := by decide +kernel
theorem slawChunk_2301 : slawChunk 2301 = true := by decide +kernel
theorem slawChunk_2302 : slawChunk 2302 = true := by decide +kernel
theorem slawChunk_2303 : slawChunk 2303 = true := by decide +kernel
theorem slawC_287 (k : Nat) (h1 : 2296 ≤ k) (h2 : k < 2304) : slawChunk k = true := by
  if e2296 : k = 2296 then subst e2296; exact slawChunk_2296 else
  if e2297 : k = 2297 then subst e2297; exact slawChunk_2297 else
  if e2298 : k = 2298 then subst e2298; exact slawChunk_2298 else
  if e2299 : k = 2299 then subst e2299; exact slawChunk_2299 else
  if e2300 : k = 2300 then subst e2300; exact slawChunk_2300 else
  if e2301 : k = 2301 then subst e2301; exact slawChunk_2301 else
  if e2302 : k = 2302 then subst e2302; exact slawChunk_2302 else
  if e2303 : k = 2303 then subst e2303; exact slawChunk_2303 else
  omega
end D2
