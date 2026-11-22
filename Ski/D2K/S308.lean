import Ski.D2Base
import Ski.D2K.S307
/-! Generated.  S-law of D: chunks 2464..2471 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_2464 : slawChunk 2464 = true := by decide +kernel
theorem slawChunk_2465 : slawChunk 2465 = true := by decide +kernel
theorem slawChunk_2466 : slawChunk 2466 = true := by decide +kernel
theorem slawChunk_2467 : slawChunk 2467 = true := by decide +kernel
theorem slawChunk_2468 : slawChunk 2468 = true := by decide +kernel
theorem slawChunk_2469 : slawChunk 2469 = true := by decide +kernel
theorem slawChunk_2470 : slawChunk 2470 = true := by decide +kernel
theorem slawChunk_2471 : slawChunk 2471 = true := by decide +kernel
theorem slawC_308 (k : Nat) (h1 : 2464 ≤ k) (h2 : k < 2472) : slawChunk k = true := by
  if e2464 : k = 2464 then subst e2464; exact slawChunk_2464 else
  if e2465 : k = 2465 then subst e2465; exact slawChunk_2465 else
  if e2466 : k = 2466 then subst e2466; exact slawChunk_2466 else
  if e2467 : k = 2467 then subst e2467; exact slawChunk_2467 else
  if e2468 : k = 2468 then subst e2468; exact slawChunk_2468 else
  if e2469 : k = 2469 then subst e2469; exact slawChunk_2469 else
  if e2470 : k = 2470 then subst e2470; exact slawChunk_2470 else
  if e2471 : k = 2471 then subst e2471; exact slawChunk_2471 else
  omega
end D2
