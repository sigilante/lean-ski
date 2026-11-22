import Ski.D2Base
import Ski.D2K.S304
/-! Generated.  S-law of D: chunks 2440..2447 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_2440 : slawChunk 2440 = true := by decide +kernel
theorem slawChunk_2441 : slawChunk 2441 = true := by decide +kernel
theorem slawChunk_2442 : slawChunk 2442 = true := by decide +kernel
theorem slawChunk_2443 : slawChunk 2443 = true := by decide +kernel
theorem slawChunk_2444 : slawChunk 2444 = true := by decide +kernel
theorem slawChunk_2445 : slawChunk 2445 = true := by decide +kernel
theorem slawChunk_2446 : slawChunk 2446 = true := by decide +kernel
theorem slawChunk_2447 : slawChunk 2447 = true := by decide +kernel
theorem slawC_305 (k : Nat) (h1 : 2440 ≤ k) (h2 : k < 2448) : slawChunk k = true := by
  if e2440 : k = 2440 then subst e2440; exact slawChunk_2440 else
  if e2441 : k = 2441 then subst e2441; exact slawChunk_2441 else
  if e2442 : k = 2442 then subst e2442; exact slawChunk_2442 else
  if e2443 : k = 2443 then subst e2443; exact slawChunk_2443 else
  if e2444 : k = 2444 then subst e2444; exact slawChunk_2444 else
  if e2445 : k = 2445 then subst e2445; exact slawChunk_2445 else
  if e2446 : k = 2446 then subst e2446; exact slawChunk_2446 else
  if e2447 : k = 2447 then subst e2447; exact slawChunk_2447 else
  omega
end D2
