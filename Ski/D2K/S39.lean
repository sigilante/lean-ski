import Ski.D2Base
import Ski.D2K.S38
/-! Generated.  S-law of D: chunks 312..319 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_312 : slawChunk 312 = true := by decide +kernel
theorem slawChunk_313 : slawChunk 313 = true := by decide +kernel
theorem slawChunk_314 : slawChunk 314 = true := by decide +kernel
theorem slawChunk_315 : slawChunk 315 = true := by decide +kernel
theorem slawChunk_316 : slawChunk 316 = true := by decide +kernel
theorem slawChunk_317 : slawChunk 317 = true := by decide +kernel
theorem slawChunk_318 : slawChunk 318 = true := by decide +kernel
theorem slawChunk_319 : slawChunk 319 = true := by decide +kernel
theorem slawC_39 (k : Nat) (h1 : 312 ≤ k) (h2 : k < 320) : slawChunk k = true := by
  if e312 : k = 312 then subst e312; exact slawChunk_312 else
  if e313 : k = 313 then subst e313; exact slawChunk_313 else
  if e314 : k = 314 then subst e314; exact slawChunk_314 else
  if e315 : k = 315 then subst e315; exact slawChunk_315 else
  if e316 : k = 316 then subst e316; exact slawChunk_316 else
  if e317 : k = 317 then subst e317; exact slawChunk_317 else
  if e318 : k = 318 then subst e318; exact slawChunk_318 else
  if e319 : k = 319 then subst e319; exact slawChunk_319 else
  omega
end D2
