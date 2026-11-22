import Ski.D2Base
import Ski.D2K.S292
/-! Generated.  S-law of D: chunks 2344..2351 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_2344 : slawChunk 2344 = true := by decide +kernel
theorem slawChunk_2345 : slawChunk 2345 = true := by decide +kernel
theorem slawChunk_2346 : slawChunk 2346 = true := by decide +kernel
theorem slawChunk_2347 : slawChunk 2347 = true := by decide +kernel
theorem slawChunk_2348 : slawChunk 2348 = true := by decide +kernel
theorem slawChunk_2349 : slawChunk 2349 = true := by decide +kernel
theorem slawChunk_2350 : slawChunk 2350 = true := by decide +kernel
theorem slawChunk_2351 : slawChunk 2351 = true := by decide +kernel
theorem slawC_293 (k : Nat) (h1 : 2344 ≤ k) (h2 : k < 2352) : slawChunk k = true := by
  if e2344 : k = 2344 then subst e2344; exact slawChunk_2344 else
  if e2345 : k = 2345 then subst e2345; exact slawChunk_2345 else
  if e2346 : k = 2346 then subst e2346; exact slawChunk_2346 else
  if e2347 : k = 2347 then subst e2347; exact slawChunk_2347 else
  if e2348 : k = 2348 then subst e2348; exact slawChunk_2348 else
  if e2349 : k = 2349 then subst e2349; exact slawChunk_2349 else
  if e2350 : k = 2350 then subst e2350; exact slawChunk_2350 else
  if e2351 : k = 2351 then subst e2351; exact slawChunk_2351 else
  omega
end D2
