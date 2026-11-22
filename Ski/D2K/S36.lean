import Ski.D2Base
import Ski.D2K.S35
/-! Generated.  S-law of D: chunks 288..295 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_288 : slawChunk 288 = true := by decide +kernel
theorem slawChunk_289 : slawChunk 289 = true := by decide +kernel
theorem slawChunk_290 : slawChunk 290 = true := by decide +kernel
theorem slawChunk_291 : slawChunk 291 = true := by decide +kernel
theorem slawChunk_292 : slawChunk 292 = true := by decide +kernel
theorem slawChunk_293 : slawChunk 293 = true := by decide +kernel
theorem slawChunk_294 : slawChunk 294 = true := by decide +kernel
theorem slawChunk_295 : slawChunk 295 = true := by decide +kernel
theorem slawC_36 (k : Nat) (h1 : 288 ≤ k) (h2 : k < 296) : slawChunk k = true := by
  if e288 : k = 288 then subst e288; exact slawChunk_288 else
  if e289 : k = 289 then subst e289; exact slawChunk_289 else
  if e290 : k = 290 then subst e290; exact slawChunk_290 else
  if e291 : k = 291 then subst e291; exact slawChunk_291 else
  if e292 : k = 292 then subst e292; exact slawChunk_292 else
  if e293 : k = 293 then subst e293; exact slawChunk_293 else
  if e294 : k = 294 then subst e294; exact slawChunk_294 else
  if e295 : k = 295 then subst e295; exact slawChunk_295 else
  omega
end D2
