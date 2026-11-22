import Ski.D2Base
import Ski.D2K.S301
/-! Generated.  S-law of D: chunks 2416..2423 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_2416 : slawChunk 2416 = true := by decide +kernel
theorem slawChunk_2417 : slawChunk 2417 = true := by decide +kernel
theorem slawChunk_2418 : slawChunk 2418 = true := by decide +kernel
theorem slawChunk_2419 : slawChunk 2419 = true := by decide +kernel
theorem slawChunk_2420 : slawChunk 2420 = true := by decide +kernel
theorem slawChunk_2421 : slawChunk 2421 = true := by decide +kernel
theorem slawChunk_2422 : slawChunk 2422 = true := by decide +kernel
theorem slawChunk_2423 : slawChunk 2423 = true := by decide +kernel
theorem slawC_302 (k : Nat) (h1 : 2416 ≤ k) (h2 : k < 2424) : slawChunk k = true := by
  if e2416 : k = 2416 then subst e2416; exact slawChunk_2416 else
  if e2417 : k = 2417 then subst e2417; exact slawChunk_2417 else
  if e2418 : k = 2418 then subst e2418; exact slawChunk_2418 else
  if e2419 : k = 2419 then subst e2419; exact slawChunk_2419 else
  if e2420 : k = 2420 then subst e2420; exact slawChunk_2420 else
  if e2421 : k = 2421 then subst e2421; exact slawChunk_2421 else
  if e2422 : k = 2422 then subst e2422; exact slawChunk_2422 else
  if e2423 : k = 2423 then subst e2423; exact slawChunk_2423 else
  omega
end D2
