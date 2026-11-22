import Ski.D2Base
import Ski.D2K.S62
/-! Generated.  S-law of D: chunks 504..511 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_504 : slawChunk 504 = true := by decide +kernel
theorem slawChunk_505 : slawChunk 505 = true := by decide +kernel
theorem slawChunk_506 : slawChunk 506 = true := by decide +kernel
theorem slawChunk_507 : slawChunk 507 = true := by decide +kernel
theorem slawChunk_508 : slawChunk 508 = true := by decide +kernel
theorem slawChunk_509 : slawChunk 509 = true := by decide +kernel
theorem slawChunk_510 : slawChunk 510 = true := by decide +kernel
theorem slawChunk_511 : slawChunk 511 = true := by decide +kernel
theorem slawC_63 (k : Nat) (h1 : 504 ≤ k) (h2 : k < 512) : slawChunk k = true := by
  if e504 : k = 504 then subst e504; exact slawChunk_504 else
  if e505 : k = 505 then subst e505; exact slawChunk_505 else
  if e506 : k = 506 then subst e506; exact slawChunk_506 else
  if e507 : k = 507 then subst e507; exact slawChunk_507 else
  if e508 : k = 508 then subst e508; exact slawChunk_508 else
  if e509 : k = 509 then subst e509; exact slawChunk_509 else
  if e510 : k = 510 then subst e510; exact slawChunk_510 else
  if e511 : k = 511 then subst e511; exact slawChunk_511 else
  omega
end D2
