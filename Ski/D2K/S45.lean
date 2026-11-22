import Ski.D2Base
import Ski.D2K.S44
/-! Generated.  S-law of D: chunks 360..367 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_360 : slawChunk 360 = true := by decide +kernel
theorem slawChunk_361 : slawChunk 361 = true := by decide +kernel
theorem slawChunk_362 : slawChunk 362 = true := by decide +kernel
theorem slawChunk_363 : slawChunk 363 = true := by decide +kernel
theorem slawChunk_364 : slawChunk 364 = true := by decide +kernel
theorem slawChunk_365 : slawChunk 365 = true := by decide +kernel
theorem slawChunk_366 : slawChunk 366 = true := by decide +kernel
theorem slawChunk_367 : slawChunk 367 = true := by decide +kernel
theorem slawC_45 (k : Nat) (h1 : 360 ≤ k) (h2 : k < 368) : slawChunk k = true := by
  if e360 : k = 360 then subst e360; exact slawChunk_360 else
  if e361 : k = 361 then subst e361; exact slawChunk_361 else
  if e362 : k = 362 then subst e362; exact slawChunk_362 else
  if e363 : k = 363 then subst e363; exact slawChunk_363 else
  if e364 : k = 364 then subst e364; exact slawChunk_364 else
  if e365 : k = 365 then subst e365; exact slawChunk_365 else
  if e366 : k = 366 then subst e366; exact slawChunk_366 else
  if e367 : k = 367 then subst e367; exact slawChunk_367 else
  omega
end D2
