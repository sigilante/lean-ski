import Ski.D2Base
import Ski.D2K.S14
/-! Generated.  S-law of D: chunks 120..127 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_120 : slawChunk 120 = true := by decide +kernel
theorem slawChunk_121 : slawChunk 121 = true := by decide +kernel
theorem slawChunk_122 : slawChunk 122 = true := by decide +kernel
theorem slawChunk_123 : slawChunk 123 = true := by decide +kernel
theorem slawChunk_124 : slawChunk 124 = true := by decide +kernel
theorem slawChunk_125 : slawChunk 125 = true := by decide +kernel
theorem slawChunk_126 : slawChunk 126 = true := by decide +kernel
theorem slawChunk_127 : slawChunk 127 = true := by decide +kernel
theorem slawC_15 (k : Nat) (h1 : 120 ≤ k) (h2 : k < 128) : slawChunk k = true := by
  if e120 : k = 120 then subst e120; exact slawChunk_120 else
  if e121 : k = 121 then subst e121; exact slawChunk_121 else
  if e122 : k = 122 then subst e122; exact slawChunk_122 else
  if e123 : k = 123 then subst e123; exact slawChunk_123 else
  if e124 : k = 124 then subst e124; exact slawChunk_124 else
  if e125 : k = 125 then subst e125; exact slawChunk_125 else
  if e126 : k = 126 then subst e126; exact slawChunk_126 else
  if e127 : k = 127 then subst e127; exact slawChunk_127 else
  omega
end D2
