import Ski.D2Base
import Ski.D2K.S289
/-! Generated.  S-law of D: chunks 2320..2327 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_2320 : slawChunk 2320 = true := by decide +kernel
theorem slawChunk_2321 : slawChunk 2321 = true := by decide +kernel
theorem slawChunk_2322 : slawChunk 2322 = true := by decide +kernel
theorem slawChunk_2323 : slawChunk 2323 = true := by decide +kernel
theorem slawChunk_2324 : slawChunk 2324 = true := by decide +kernel
theorem slawChunk_2325 : slawChunk 2325 = true := by decide +kernel
theorem slawChunk_2326 : slawChunk 2326 = true := by decide +kernel
theorem slawChunk_2327 : slawChunk 2327 = true := by decide +kernel
theorem slawC_290 (k : Nat) (h1 : 2320 ≤ k) (h2 : k < 2328) : slawChunk k = true := by
  if e2320 : k = 2320 then subst e2320; exact slawChunk_2320 else
  if e2321 : k = 2321 then subst e2321; exact slawChunk_2321 else
  if e2322 : k = 2322 then subst e2322; exact slawChunk_2322 else
  if e2323 : k = 2323 then subst e2323; exact slawChunk_2323 else
  if e2324 : k = 2324 then subst e2324; exact slawChunk_2324 else
  if e2325 : k = 2325 then subst e2325; exact slawChunk_2325 else
  if e2326 : k = 2326 then subst e2326; exact slawChunk_2326 else
  if e2327 : k = 2327 then subst e2327; exact slawChunk_2327 else
  omega
end D2
