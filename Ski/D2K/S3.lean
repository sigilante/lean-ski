import Ski.D2Base
import Ski.D2K.S2
/-! Generated.  S-law of D: chunks 24..31 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_24 : slawChunk 24 = true := by decide +kernel
theorem slawChunk_25 : slawChunk 25 = true := by decide +kernel
theorem slawChunk_26 : slawChunk 26 = true := by decide +kernel
theorem slawChunk_27 : slawChunk 27 = true := by decide +kernel
theorem slawChunk_28 : slawChunk 28 = true := by decide +kernel
theorem slawChunk_29 : slawChunk 29 = true := by decide +kernel
theorem slawChunk_30 : slawChunk 30 = true := by decide +kernel
theorem slawChunk_31 : slawChunk 31 = true := by decide +kernel
theorem slawC_3 (k : Nat) (h1 : 24 ≤ k) (h2 : k < 32) : slawChunk k = true := by
  if e24 : k = 24 then subst e24; exact slawChunk_24 else
  if e25 : k = 25 then subst e25; exact slawChunk_25 else
  if e26 : k = 26 then subst e26; exact slawChunk_26 else
  if e27 : k = 27 then subst e27; exact slawChunk_27 else
  if e28 : k = 28 then subst e28; exact slawChunk_28 else
  if e29 : k = 29 then subst e29; exact slawChunk_29 else
  if e30 : k = 30 then subst e30; exact slawChunk_30 else
  if e31 : k = 31 then subst e31; exact slawChunk_31 else
  omega
end D2
