import Ski.D2Base
import Ski.D2K.S47
/-! Generated.  S-law of D: chunks 384..391 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_384 : slawChunk 384 = true := by decide +kernel
theorem slawChunk_385 : slawChunk 385 = true := by decide +kernel
theorem slawChunk_386 : slawChunk 386 = true := by decide +kernel
theorem slawChunk_387 : slawChunk 387 = true := by decide +kernel
theorem slawChunk_388 : slawChunk 388 = true := by decide +kernel
theorem slawChunk_389 : slawChunk 389 = true := by decide +kernel
theorem slawChunk_390 : slawChunk 390 = true := by decide +kernel
theorem slawChunk_391 : slawChunk 391 = true := by decide +kernel
theorem slawC_48 (k : Nat) (h1 : 384 ≤ k) (h2 : k < 392) : slawChunk k = true := by
  if e384 : k = 384 then subst e384; exact slawChunk_384 else
  if e385 : k = 385 then subst e385; exact slawChunk_385 else
  if e386 : k = 386 then subst e386; exact slawChunk_386 else
  if e387 : k = 387 then subst e387; exact slawChunk_387 else
  if e388 : k = 388 then subst e388; exact slawChunk_388 else
  if e389 : k = 389 then subst e389; exact slawChunk_389 else
  if e390 : k = 390 then subst e390; exact slawChunk_390 else
  if e391 : k = 391 then subst e391; exact slawChunk_391 else
  omega
end D2
