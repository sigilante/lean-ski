import Ski.D2Base
import Ski.D2K.S63
/-! Generated.  S-law of D: chunks 512..519 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_512 : slawChunk 512 = true := by decide +kernel
theorem slawChunk_513 : slawChunk 513 = true := by decide +kernel
theorem slawChunk_514 : slawChunk 514 = true := by decide +kernel
theorem slawChunk_515 : slawChunk 515 = true := by decide +kernel
theorem slawChunk_516 : slawChunk 516 = true := by decide +kernel
theorem slawChunk_517 : slawChunk 517 = true := by decide +kernel
theorem slawChunk_518 : slawChunk 518 = true := by decide +kernel
theorem slawChunk_519 : slawChunk 519 = true := by decide +kernel
theorem slawC_64 (k : Nat) (h1 : 512 ≤ k) (h2 : k < 520) : slawChunk k = true := by
  if e512 : k = 512 then subst e512; exact slawChunk_512 else
  if e513 : k = 513 then subst e513; exact slawChunk_513 else
  if e514 : k = 514 then subst e514; exact slawChunk_514 else
  if e515 : k = 515 then subst e515; exact slawChunk_515 else
  if e516 : k = 516 then subst e516; exact slawChunk_516 else
  if e517 : k = 517 then subst e517; exact slawChunk_517 else
  if e518 : k = 518 then subst e518; exact slawChunk_518 else
  if e519 : k = 519 then subst e519; exact slawChunk_519 else
  omega
end D2
