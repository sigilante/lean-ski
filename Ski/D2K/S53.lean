import Ski.D2Base
import Ski.D2K.S52
/-! Generated.  S-law of D: chunks 424..431 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_424 : slawChunk 424 = true := by decide +kernel
theorem slawChunk_425 : slawChunk 425 = true := by decide +kernel
theorem slawChunk_426 : slawChunk 426 = true := by decide +kernel
theorem slawChunk_427 : slawChunk 427 = true := by decide +kernel
theorem slawChunk_428 : slawChunk 428 = true := by decide +kernel
theorem slawChunk_429 : slawChunk 429 = true := by decide +kernel
theorem slawChunk_430 : slawChunk 430 = true := by decide +kernel
theorem slawChunk_431 : slawChunk 431 = true := by decide +kernel
theorem slawC_53 (k : Nat) (h1 : 424 ≤ k) (h2 : k < 432) : slawChunk k = true := by
  if e424 : k = 424 then subst e424; exact slawChunk_424 else
  if e425 : k = 425 then subst e425; exact slawChunk_425 else
  if e426 : k = 426 then subst e426; exact slawChunk_426 else
  if e427 : k = 427 then subst e427; exact slawChunk_427 else
  if e428 : k = 428 then subst e428; exact slawChunk_428 else
  if e429 : k = 429 then subst e429; exact slawChunk_429 else
  if e430 : k = 430 then subst e430; exact slawChunk_430 else
  if e431 : k = 431 then subst e431; exact slawChunk_431 else
  omega
end D2
