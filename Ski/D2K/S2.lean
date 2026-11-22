import Ski.D2Base
import Ski.D2K.S1
/-! Generated.  S-law of D: chunks 16..23 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_16 : slawChunk 16 = true := by decide +kernel
theorem slawChunk_17 : slawChunk 17 = true := by decide +kernel
theorem slawChunk_18 : slawChunk 18 = true := by decide +kernel
theorem slawChunk_19 : slawChunk 19 = true := by decide +kernel
theorem slawChunk_20 : slawChunk 20 = true := by decide +kernel
theorem slawChunk_21 : slawChunk 21 = true := by decide +kernel
theorem slawChunk_22 : slawChunk 22 = true := by decide +kernel
theorem slawChunk_23 : slawChunk 23 = true := by decide +kernel
theorem slawC_2 (k : Nat) (h1 : 16 ≤ k) (h2 : k < 24) : slawChunk k = true := by
  if e16 : k = 16 then subst e16; exact slawChunk_16 else
  if e17 : k = 17 then subst e17; exact slawChunk_17 else
  if e18 : k = 18 then subst e18; exact slawChunk_18 else
  if e19 : k = 19 then subst e19; exact slawChunk_19 else
  if e20 : k = 20 then subst e20; exact slawChunk_20 else
  if e21 : k = 21 then subst e21; exact slawChunk_21 else
  if e22 : k = 22 then subst e22; exact slawChunk_22 else
  if e23 : k = 23 then subst e23; exact slawChunk_23 else
  omega
end D2
