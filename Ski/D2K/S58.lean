import Ski.D2Base
import Ski.D2K.S57
/-! Generated.  S-law of D: chunks 464..471 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_464 : slawChunk 464 = true := by decide +kernel
theorem slawChunk_465 : slawChunk 465 = true := by decide +kernel
theorem slawChunk_466 : slawChunk 466 = true := by decide +kernel
theorem slawChunk_467 : slawChunk 467 = true := by decide +kernel
theorem slawChunk_468 : slawChunk 468 = true := by decide +kernel
theorem slawChunk_469 : slawChunk 469 = true := by decide +kernel
theorem slawChunk_470 : slawChunk 470 = true := by decide +kernel
theorem slawChunk_471 : slawChunk 471 = true := by decide +kernel
theorem slawC_58 (k : Nat) (h1 : 464 ≤ k) (h2 : k < 472) : slawChunk k = true := by
  if e464 : k = 464 then subst e464; exact slawChunk_464 else
  if e465 : k = 465 then subst e465; exact slawChunk_465 else
  if e466 : k = 466 then subst e466; exact slawChunk_466 else
  if e467 : k = 467 then subst e467; exact slawChunk_467 else
  if e468 : k = 468 then subst e468; exact slawChunk_468 else
  if e469 : k = 469 then subst e469; exact slawChunk_469 else
  if e470 : k = 470 then subst e470; exact slawChunk_470 else
  if e471 : k = 471 then subst e471; exact slawChunk_471 else
  omega
end D2
