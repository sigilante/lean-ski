import Ski.D2Base
import Ski.D2K.S33
/-! Generated.  S-law of D: chunks 272..279 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_272 : slawChunk 272 = true := by decide +kernel
theorem slawChunk_273 : slawChunk 273 = true := by decide +kernel
theorem slawChunk_274 : slawChunk 274 = true := by decide +kernel
theorem slawChunk_275 : slawChunk 275 = true := by decide +kernel
theorem slawChunk_276 : slawChunk 276 = true := by decide +kernel
theorem slawChunk_277 : slawChunk 277 = true := by decide +kernel
theorem slawChunk_278 : slawChunk 278 = true := by decide +kernel
theorem slawChunk_279 : slawChunk 279 = true := by decide +kernel
theorem slawC_34 (k : Nat) (h1 : 272 ≤ k) (h2 : k < 280) : slawChunk k = true := by
  if e272 : k = 272 then subst e272; exact slawChunk_272 else
  if e273 : k = 273 then subst e273; exact slawChunk_273 else
  if e274 : k = 274 then subst e274; exact slawChunk_274 else
  if e275 : k = 275 then subst e275; exact slawChunk_275 else
  if e276 : k = 276 then subst e276; exact slawChunk_276 else
  if e277 : k = 277 then subst e277; exact slawChunk_277 else
  if e278 : k = 278 then subst e278; exact slawChunk_278 else
  if e279 : k = 279 then subst e279; exact slawChunk_279 else
  omega
end D2
