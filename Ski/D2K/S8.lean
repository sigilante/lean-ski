import Ski.D2Base
import Ski.D2K.S7
/-! Generated.  S-law of D: chunks 64..71 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_64 : slawChunk 64 = true := by decide +kernel
theorem slawChunk_65 : slawChunk 65 = true := by decide +kernel
theorem slawChunk_66 : slawChunk 66 = true := by decide +kernel
theorem slawChunk_67 : slawChunk 67 = true := by decide +kernel
theorem slawChunk_68 : slawChunk 68 = true := by decide +kernel
theorem slawChunk_69 : slawChunk 69 = true := by decide +kernel
theorem slawChunk_70 : slawChunk 70 = true := by decide +kernel
theorem slawChunk_71 : slawChunk 71 = true := by decide +kernel
theorem slawC_8 (k : Nat) (h1 : 64 ≤ k) (h2 : k < 72) : slawChunk k = true := by
  if e64 : k = 64 then subst e64; exact slawChunk_64 else
  if e65 : k = 65 then subst e65; exact slawChunk_65 else
  if e66 : k = 66 then subst e66; exact slawChunk_66 else
  if e67 : k = 67 then subst e67; exact slawChunk_67 else
  if e68 : k = 68 then subst e68; exact slawChunk_68 else
  if e69 : k = 69 then subst e69; exact slawChunk_69 else
  if e70 : k = 70 then subst e70; exact slawChunk_70 else
  if e71 : k = 71 then subst e71; exact slawChunk_71 else
  omega
end D2
