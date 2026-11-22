import Ski.D2Base
import Ski.D2K.S290
/-! Generated.  S-law of D: chunks 2328..2335 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_2328 : slawChunk 2328 = true := by decide +kernel
theorem slawChunk_2329 : slawChunk 2329 = true := by decide +kernel
theorem slawChunk_2330 : slawChunk 2330 = true := by decide +kernel
theorem slawChunk_2331 : slawChunk 2331 = true := by decide +kernel
theorem slawChunk_2332 : slawChunk 2332 = true := by decide +kernel
theorem slawChunk_2333 : slawChunk 2333 = true := by decide +kernel
theorem slawChunk_2334 : slawChunk 2334 = true := by decide +kernel
theorem slawChunk_2335 : slawChunk 2335 = true := by decide +kernel
theorem slawC_291 (k : Nat) (h1 : 2328 ≤ k) (h2 : k < 2336) : slawChunk k = true := by
  if e2328 : k = 2328 then subst e2328; exact slawChunk_2328 else
  if e2329 : k = 2329 then subst e2329; exact slawChunk_2329 else
  if e2330 : k = 2330 then subst e2330; exact slawChunk_2330 else
  if e2331 : k = 2331 then subst e2331; exact slawChunk_2331 else
  if e2332 : k = 2332 then subst e2332; exact slawChunk_2332 else
  if e2333 : k = 2333 then subst e2333; exact slawChunk_2333 else
  if e2334 : k = 2334 then subst e2334; exact slawChunk_2334 else
  if e2335 : k = 2335 then subst e2335; exact slawChunk_2335 else
  omega
end D2
