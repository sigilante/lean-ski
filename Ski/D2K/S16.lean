import Ski.D2Base
import Ski.D2K.S15
/-! Generated.  S-law of D: chunks 128..135 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_128 : slawChunk 128 = true := by decide +kernel
theorem slawChunk_129 : slawChunk 129 = true := by decide +kernel
theorem slawChunk_130 : slawChunk 130 = true := by decide +kernel
theorem slawChunk_131 : slawChunk 131 = true := by decide +kernel
theorem slawChunk_132 : slawChunk 132 = true := by decide +kernel
theorem slawChunk_133 : slawChunk 133 = true := by decide +kernel
theorem slawChunk_134 : slawChunk 134 = true := by decide +kernel
theorem slawChunk_135 : slawChunk 135 = true := by decide +kernel
theorem slawC_16 (k : Nat) (h1 : 128 ≤ k) (h2 : k < 136) : slawChunk k = true := by
  if e128 : k = 128 then subst e128; exact slawChunk_128 else
  if e129 : k = 129 then subst e129; exact slawChunk_129 else
  if e130 : k = 130 then subst e130; exact slawChunk_130 else
  if e131 : k = 131 then subst e131; exact slawChunk_131 else
  if e132 : k = 132 then subst e132; exact slawChunk_132 else
  if e133 : k = 133 then subst e133; exact slawChunk_133 else
  if e134 : k = 134 then subst e134; exact slawChunk_134 else
  if e135 : k = 135 then subst e135; exact slawChunk_135 else
  omega
end D2
