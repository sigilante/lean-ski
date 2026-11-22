import Ski.D2Base
import Ski.D2K.S302
/-! Generated.  S-law of D: chunks 2424..2431 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_2424 : slawChunk 2424 = true := by decide +kernel
theorem slawChunk_2425 : slawChunk 2425 = true := by decide +kernel
theorem slawChunk_2426 : slawChunk 2426 = true := by decide +kernel
theorem slawChunk_2427 : slawChunk 2427 = true := by decide +kernel
theorem slawChunk_2428 : slawChunk 2428 = true := by decide +kernel
theorem slawChunk_2429 : slawChunk 2429 = true := by decide +kernel
theorem slawChunk_2430 : slawChunk 2430 = true := by decide +kernel
theorem slawChunk_2431 : slawChunk 2431 = true := by decide +kernel
theorem slawC_303 (k : Nat) (h1 : 2424 ≤ k) (h2 : k < 2432) : slawChunk k = true := by
  if e2424 : k = 2424 then subst e2424; exact slawChunk_2424 else
  if e2425 : k = 2425 then subst e2425; exact slawChunk_2425 else
  if e2426 : k = 2426 then subst e2426; exact slawChunk_2426 else
  if e2427 : k = 2427 then subst e2427; exact slawChunk_2427 else
  if e2428 : k = 2428 then subst e2428; exact slawChunk_2428 else
  if e2429 : k = 2429 then subst e2429; exact slawChunk_2429 else
  if e2430 : k = 2430 then subst e2430; exact slawChunk_2430 else
  if e2431 : k = 2431 then subst e2431; exact slawChunk_2431 else
  omega
end D2
