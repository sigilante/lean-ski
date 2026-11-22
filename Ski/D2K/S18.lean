import Ski.D2Base
import Ski.D2K.S17
/-! Generated.  S-law of D: chunks 144..151 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_144 : slawChunk 144 = true := by decide +kernel
theorem slawChunk_145 : slawChunk 145 = true := by decide +kernel
theorem slawChunk_146 : slawChunk 146 = true := by decide +kernel
theorem slawChunk_147 : slawChunk 147 = true := by decide +kernel
theorem slawChunk_148 : slawChunk 148 = true := by decide +kernel
theorem slawChunk_149 : slawChunk 149 = true := by decide +kernel
theorem slawChunk_150 : slawChunk 150 = true := by decide +kernel
theorem slawChunk_151 : slawChunk 151 = true := by decide +kernel
theorem slawC_18 (k : Nat) (h1 : 144 ≤ k) (h2 : k < 152) : slawChunk k = true := by
  if e144 : k = 144 then subst e144; exact slawChunk_144 else
  if e145 : k = 145 then subst e145; exact slawChunk_145 else
  if e146 : k = 146 then subst e146; exact slawChunk_146 else
  if e147 : k = 147 then subst e147; exact slawChunk_147 else
  if e148 : k = 148 then subst e148; exact slawChunk_148 else
  if e149 : k = 149 then subst e149; exact slawChunk_149 else
  if e150 : k = 150 then subst e150; exact slawChunk_150 else
  if e151 : k = 151 then subst e151; exact slawChunk_151 else
  omega
end D2
