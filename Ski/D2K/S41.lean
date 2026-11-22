import Ski.D2Base
import Ski.D2K.S40
/-! Generated.  S-law of D: chunks 328..335 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_328 : slawChunk 328 = true := by decide +kernel
theorem slawChunk_329 : slawChunk 329 = true := by decide +kernel
theorem slawChunk_330 : slawChunk 330 = true := by decide +kernel
theorem slawChunk_331 : slawChunk 331 = true := by decide +kernel
theorem slawChunk_332 : slawChunk 332 = true := by decide +kernel
theorem slawChunk_333 : slawChunk 333 = true := by decide +kernel
theorem slawChunk_334 : slawChunk 334 = true := by decide +kernel
theorem slawChunk_335 : slawChunk 335 = true := by decide +kernel
theorem slawC_41 (k : Nat) (h1 : 328 ≤ k) (h2 : k < 336) : slawChunk k = true := by
  if e328 : k = 328 then subst e328; exact slawChunk_328 else
  if e329 : k = 329 then subst e329; exact slawChunk_329 else
  if e330 : k = 330 then subst e330; exact slawChunk_330 else
  if e331 : k = 331 then subst e331; exact slawChunk_331 else
  if e332 : k = 332 then subst e332; exact slawChunk_332 else
  if e333 : k = 333 then subst e333; exact slawChunk_333 else
  if e334 : k = 334 then subst e334; exact slawChunk_334 else
  if e335 : k = 335 then subst e335; exact slawChunk_335 else
  omega
end D2
