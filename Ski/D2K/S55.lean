import Ski.D2Base
import Ski.D2K.S54
/-! Generated.  S-law of D: chunks 440..447 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_440 : slawChunk 440 = true := by decide +kernel
theorem slawChunk_441 : slawChunk 441 = true := by decide +kernel
theorem slawChunk_442 : slawChunk 442 = true := by decide +kernel
theorem slawChunk_443 : slawChunk 443 = true := by decide +kernel
theorem slawChunk_444 : slawChunk 444 = true := by decide +kernel
theorem slawChunk_445 : slawChunk 445 = true := by decide +kernel
theorem slawChunk_446 : slawChunk 446 = true := by decide +kernel
theorem slawChunk_447 : slawChunk 447 = true := by decide +kernel
theorem slawC_55 (k : Nat) (h1 : 440 ≤ k) (h2 : k < 448) : slawChunk k = true := by
  if e440 : k = 440 then subst e440; exact slawChunk_440 else
  if e441 : k = 441 then subst e441; exact slawChunk_441 else
  if e442 : k = 442 then subst e442; exact slawChunk_442 else
  if e443 : k = 443 then subst e443; exact slawChunk_443 else
  if e444 : k = 444 then subst e444; exact slawChunk_444 else
  if e445 : k = 445 then subst e445; exact slawChunk_445 else
  if e446 : k = 446 then subst e446; exact slawChunk_446 else
  if e447 : k = 447 then subst e447; exact slawChunk_447 else
  omega
end D2
