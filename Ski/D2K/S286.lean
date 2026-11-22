import Ski.D2Base
import Ski.D2K.S285
/-! Generated.  S-law of D: chunks 2288..2295 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_2288 : slawChunk 2288 = true := by decide +kernel
theorem slawChunk_2289 : slawChunk 2289 = true := by decide +kernel
theorem slawChunk_2290 : slawChunk 2290 = true := by decide +kernel
theorem slawChunk_2291 : slawChunk 2291 = true := by decide +kernel
theorem slawChunk_2292 : slawChunk 2292 = true := by decide +kernel
theorem slawChunk_2293 : slawChunk 2293 = true := by decide +kernel
theorem slawChunk_2294 : slawChunk 2294 = true := by decide +kernel
theorem slawChunk_2295 : slawChunk 2295 = true := by decide +kernel
theorem slawC_286 (k : Nat) (h1 : 2288 ≤ k) (h2 : k < 2296) : slawChunk k = true := by
  if e2288 : k = 2288 then subst e2288; exact slawChunk_2288 else
  if e2289 : k = 2289 then subst e2289; exact slawChunk_2289 else
  if e2290 : k = 2290 then subst e2290; exact slawChunk_2290 else
  if e2291 : k = 2291 then subst e2291; exact slawChunk_2291 else
  if e2292 : k = 2292 then subst e2292; exact slawChunk_2292 else
  if e2293 : k = 2293 then subst e2293; exact slawChunk_2293 else
  if e2294 : k = 2294 then subst e2294; exact slawChunk_2294 else
  if e2295 : k = 2295 then subst e2295; exact slawChunk_2295 else
  omega
end D2
