import Ski.D2Base
import Ski.D2K.S8
/-! Generated.  S-law of D: chunks 72..79 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_72 : slawChunk 72 = true := by decide +kernel
theorem slawChunk_73 : slawChunk 73 = true := by decide +kernel
theorem slawChunk_74 : slawChunk 74 = true := by decide +kernel
theorem slawChunk_75 : slawChunk 75 = true := by decide +kernel
theorem slawChunk_76 : slawChunk 76 = true := by decide +kernel
theorem slawChunk_77 : slawChunk 77 = true := by decide +kernel
theorem slawChunk_78 : slawChunk 78 = true := by decide +kernel
theorem slawChunk_79 : slawChunk 79 = true := by decide +kernel
theorem slawC_9 (k : Nat) (h1 : 72 ≤ k) (h2 : k < 80) : slawChunk k = true := by
  if e72 : k = 72 then subst e72; exact slawChunk_72 else
  if e73 : k = 73 then subst e73; exact slawChunk_73 else
  if e74 : k = 74 then subst e74; exact slawChunk_74 else
  if e75 : k = 75 then subst e75; exact slawChunk_75 else
  if e76 : k = 76 then subst e76; exact slawChunk_76 else
  if e77 : k = 77 then subst e77; exact slawChunk_77 else
  if e78 : k = 78 then subst e78; exact slawChunk_78 else
  if e79 : k = 79 then subst e79; exact slawChunk_79 else
  omega
end D2
