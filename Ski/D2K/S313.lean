import Ski.D2Base
import Ski.D2K.S312
/-! Generated.  S-law of D: chunks 2504..2511 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_2504 : slawChunk 2504 = true := by decide +kernel
theorem slawChunk_2505 : slawChunk 2505 = true := by decide +kernel
theorem slawChunk_2506 : slawChunk 2506 = true := by decide +kernel
theorem slawChunk_2507 : slawChunk 2507 = true := by decide +kernel
theorem slawChunk_2508 : slawChunk 2508 = true := by decide +kernel
theorem slawChunk_2509 : slawChunk 2509 = true := by decide +kernel
theorem slawChunk_2510 : slawChunk 2510 = true := by decide +kernel
theorem slawChunk_2511 : slawChunk 2511 = true := by decide +kernel
theorem slawC_313 (k : Nat) (h1 : 2504 ≤ k) (h2 : k < 2512) : slawChunk k = true := by
  if e2504 : k = 2504 then subst e2504; exact slawChunk_2504 else
  if e2505 : k = 2505 then subst e2505; exact slawChunk_2505 else
  if e2506 : k = 2506 then subst e2506; exact slawChunk_2506 else
  if e2507 : k = 2507 then subst e2507; exact slawChunk_2507 else
  if e2508 : k = 2508 then subst e2508; exact slawChunk_2508 else
  if e2509 : k = 2509 then subst e2509; exact slawChunk_2509 else
  if e2510 : k = 2510 then subst e2510; exact slawChunk_2510 else
  if e2511 : k = 2511 then subst e2511; exact slawChunk_2511 else
  omega
end D2
