import Ski.D2Base
import Ski.D2K.S300
/-! Generated.  S-law of D: chunks 2408..2415 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_2408 : slawChunk 2408 = true := by decide +kernel
theorem slawChunk_2409 : slawChunk 2409 = true := by decide +kernel
theorem slawChunk_2410 : slawChunk 2410 = true := by decide +kernel
theorem slawChunk_2411 : slawChunk 2411 = true := by decide +kernel
theorem slawChunk_2412 : slawChunk 2412 = true := by decide +kernel
theorem slawChunk_2413 : slawChunk 2413 = true := by decide +kernel
theorem slawChunk_2414 : slawChunk 2414 = true := by decide +kernel
theorem slawChunk_2415 : slawChunk 2415 = true := by decide +kernel
theorem slawC_301 (k : Nat) (h1 : 2408 ≤ k) (h2 : k < 2416) : slawChunk k = true := by
  if e2408 : k = 2408 then subst e2408; exact slawChunk_2408 else
  if e2409 : k = 2409 then subst e2409; exact slawChunk_2409 else
  if e2410 : k = 2410 then subst e2410; exact slawChunk_2410 else
  if e2411 : k = 2411 then subst e2411; exact slawChunk_2411 else
  if e2412 : k = 2412 then subst e2412; exact slawChunk_2412 else
  if e2413 : k = 2413 then subst e2413; exact slawChunk_2413 else
  if e2414 : k = 2414 then subst e2414; exact slawChunk_2414 else
  if e2415 : k = 2415 then subst e2415; exact slawChunk_2415 else
  omega
end D2
