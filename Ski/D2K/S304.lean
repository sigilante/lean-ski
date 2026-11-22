import Ski.D2Base
import Ski.D2K.S303
/-! Generated.  S-law of D: chunks 2432..2439 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_2432 : slawChunk 2432 = true := by decide +kernel
theorem slawChunk_2433 : slawChunk 2433 = true := by decide +kernel
theorem slawChunk_2434 : slawChunk 2434 = true := by decide +kernel
theorem slawChunk_2435 : slawChunk 2435 = true := by decide +kernel
theorem slawChunk_2436 : slawChunk 2436 = true := by decide +kernel
theorem slawChunk_2437 : slawChunk 2437 = true := by decide +kernel
theorem slawChunk_2438 : slawChunk 2438 = true := by decide +kernel
theorem slawChunk_2439 : slawChunk 2439 = true := by decide +kernel
theorem slawC_304 (k : Nat) (h1 : 2432 ≤ k) (h2 : k < 2440) : slawChunk k = true := by
  if e2432 : k = 2432 then subst e2432; exact slawChunk_2432 else
  if e2433 : k = 2433 then subst e2433; exact slawChunk_2433 else
  if e2434 : k = 2434 then subst e2434; exact slawChunk_2434 else
  if e2435 : k = 2435 then subst e2435; exact slawChunk_2435 else
  if e2436 : k = 2436 then subst e2436; exact slawChunk_2436 else
  if e2437 : k = 2437 then subst e2437; exact slawChunk_2437 else
  if e2438 : k = 2438 then subst e2438; exact slawChunk_2438 else
  if e2439 : k = 2439 then subst e2439; exact slawChunk_2439 else
  omega
end D2
