import Ski.D2Base
import Ski.D2K.S45
/-! Generated.  S-law of D: chunks 368..375 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_368 : slawChunk 368 = true := by decide +kernel
theorem slawChunk_369 : slawChunk 369 = true := by decide +kernel
theorem slawChunk_370 : slawChunk 370 = true := by decide +kernel
theorem slawChunk_371 : slawChunk 371 = true := by decide +kernel
theorem slawChunk_372 : slawChunk 372 = true := by decide +kernel
theorem slawChunk_373 : slawChunk 373 = true := by decide +kernel
theorem slawChunk_374 : slawChunk 374 = true := by decide +kernel
theorem slawChunk_375 : slawChunk 375 = true := by decide +kernel
theorem slawC_46 (k : Nat) (h1 : 368 ≤ k) (h2 : k < 376) : slawChunk k = true := by
  if e368 : k = 368 then subst e368; exact slawChunk_368 else
  if e369 : k = 369 then subst e369; exact slawChunk_369 else
  if e370 : k = 370 then subst e370; exact slawChunk_370 else
  if e371 : k = 371 then subst e371; exact slawChunk_371 else
  if e372 : k = 372 then subst e372; exact slawChunk_372 else
  if e373 : k = 373 then subst e373; exact slawChunk_373 else
  if e374 : k = 374 then subst e374; exact slawChunk_374 else
  if e375 : k = 375 then subst e375; exact slawChunk_375 else
  omega
end D2
