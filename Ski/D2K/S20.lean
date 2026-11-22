import Ski.D2Base
import Ski.D2K.S19
/-! Generated.  S-law of D: chunks 160..167 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_160 : slawChunk 160 = true := by decide +kernel
theorem slawChunk_161 : slawChunk 161 = true := by decide +kernel
theorem slawChunk_162 : slawChunk 162 = true := by decide +kernel
theorem slawChunk_163 : slawChunk 163 = true := by decide +kernel
theorem slawChunk_164 : slawChunk 164 = true := by decide +kernel
theorem slawChunk_165 : slawChunk 165 = true := by decide +kernel
theorem slawChunk_166 : slawChunk 166 = true := by decide +kernel
theorem slawChunk_167 : slawChunk 167 = true := by decide +kernel
theorem slawC_20 (k : Nat) (h1 : 160 ≤ k) (h2 : k < 168) : slawChunk k = true := by
  if e160 : k = 160 then subst e160; exact slawChunk_160 else
  if e161 : k = 161 then subst e161; exact slawChunk_161 else
  if e162 : k = 162 then subst e162; exact slawChunk_162 else
  if e163 : k = 163 then subst e163; exact slawChunk_163 else
  if e164 : k = 164 then subst e164; exact slawChunk_164 else
  if e165 : k = 165 then subst e165; exact slawChunk_165 else
  if e166 : k = 166 then subst e166; exact slawChunk_166 else
  if e167 : k = 167 then subst e167; exact slawChunk_167 else
  omega
end D2
