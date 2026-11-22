import Ski.D2Base
import Ski.D2K.S299
/-! Generated.  S-law of D: chunks 2400..2407 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_2400 : slawChunk 2400 = true := by decide +kernel
theorem slawChunk_2401 : slawChunk 2401 = true := by decide +kernel
theorem slawChunk_2402 : slawChunk 2402 = true := by decide +kernel
theorem slawChunk_2403 : slawChunk 2403 = true := by decide +kernel
theorem slawChunk_2404 : slawChunk 2404 = true := by decide +kernel
theorem slawChunk_2405 : slawChunk 2405 = true := by decide +kernel
theorem slawChunk_2406 : slawChunk 2406 = true := by decide +kernel
theorem slawChunk_2407 : slawChunk 2407 = true := by decide +kernel
theorem slawC_300 (k : Nat) (h1 : 2400 ≤ k) (h2 : k < 2408) : slawChunk k = true := by
  if e2400 : k = 2400 then subst e2400; exact slawChunk_2400 else
  if e2401 : k = 2401 then subst e2401; exact slawChunk_2401 else
  if e2402 : k = 2402 then subst e2402; exact slawChunk_2402 else
  if e2403 : k = 2403 then subst e2403; exact slawChunk_2403 else
  if e2404 : k = 2404 then subst e2404; exact slawChunk_2404 else
  if e2405 : k = 2405 then subst e2405; exact slawChunk_2405 else
  if e2406 : k = 2406 then subst e2406; exact slawChunk_2406 else
  if e2407 : k = 2407 then subst e2407; exact slawChunk_2407 else
  omega
end D2
