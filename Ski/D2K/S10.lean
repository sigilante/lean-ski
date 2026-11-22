import Ski.D2Base
import Ski.D2K.S9
/-! Generated.  S-law of D: chunks 80..87 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_80 : slawChunk 80 = true := by decide +kernel
theorem slawChunk_81 : slawChunk 81 = true := by decide +kernel
theorem slawChunk_82 : slawChunk 82 = true := by decide +kernel
theorem slawChunk_83 : slawChunk 83 = true := by decide +kernel
theorem slawChunk_84 : slawChunk 84 = true := by decide +kernel
theorem slawChunk_85 : slawChunk 85 = true := by decide +kernel
theorem slawChunk_86 : slawChunk 86 = true := by decide +kernel
theorem slawChunk_87 : slawChunk 87 = true := by decide +kernel
theorem slawC_10 (k : Nat) (h1 : 80 ≤ k) (h2 : k < 88) : slawChunk k = true := by
  if e80 : k = 80 then subst e80; exact slawChunk_80 else
  if e81 : k = 81 then subst e81; exact slawChunk_81 else
  if e82 : k = 82 then subst e82; exact slawChunk_82 else
  if e83 : k = 83 then subst e83; exact slawChunk_83 else
  if e84 : k = 84 then subst e84; exact slawChunk_84 else
  if e85 : k = 85 then subst e85; exact slawChunk_85 else
  if e86 : k = 86 then subst e86; exact slawChunk_86 else
  if e87 : k = 87 then subst e87; exact slawChunk_87 else
  omega
end D2
