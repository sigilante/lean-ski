import Ski.D2Base
import Ski.D2K.S3
/-! Generated.  S-law of D: chunks 32..39 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_32 : slawChunk 32 = true := by decide +kernel
theorem slawChunk_33 : slawChunk 33 = true := by decide +kernel
theorem slawChunk_34 : slawChunk 34 = true := by decide +kernel
theorem slawChunk_35 : slawChunk 35 = true := by decide +kernel
theorem slawChunk_36 : slawChunk 36 = true := by decide +kernel
theorem slawChunk_37 : slawChunk 37 = true := by decide +kernel
theorem slawChunk_38 : slawChunk 38 = true := by decide +kernel
theorem slawChunk_39 : slawChunk 39 = true := by decide +kernel
theorem slawC_4 (k : Nat) (h1 : 32 ≤ k) (h2 : k < 40) : slawChunk k = true := by
  if e32 : k = 32 then subst e32; exact slawChunk_32 else
  if e33 : k = 33 then subst e33; exact slawChunk_33 else
  if e34 : k = 34 then subst e34; exact slawChunk_34 else
  if e35 : k = 35 then subst e35; exact slawChunk_35 else
  if e36 : k = 36 then subst e36; exact slawChunk_36 else
  if e37 : k = 37 then subst e37; exact slawChunk_37 else
  if e38 : k = 38 then subst e38; exact slawChunk_38 else
  if e39 : k = 39 then subst e39; exact slawChunk_39 else
  omega
end D2
