import Ski.D2Base
import Ski.D2K.S21
/-! Generated.  S-law of D: chunks 176..183 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_176 : slawChunk 176 = true := by decide +kernel
theorem slawChunk_177 : slawChunk 177 = true := by decide +kernel
theorem slawChunk_178 : slawChunk 178 = true := by decide +kernel
theorem slawChunk_179 : slawChunk 179 = true := by decide +kernel
theorem slawChunk_180 : slawChunk 180 = true := by decide +kernel
theorem slawChunk_181 : slawChunk 181 = true := by decide +kernel
theorem slawChunk_182 : slawChunk 182 = true := by decide +kernel
theorem slawChunk_183 : slawChunk 183 = true := by decide +kernel
theorem slawC_22 (k : Nat) (h1 : 176 ≤ k) (h2 : k < 184) : slawChunk k = true := by
  if e176 : k = 176 then subst e176; exact slawChunk_176 else
  if e177 : k = 177 then subst e177; exact slawChunk_177 else
  if e178 : k = 178 then subst e178; exact slawChunk_178 else
  if e179 : k = 179 then subst e179; exact slawChunk_179 else
  if e180 : k = 180 then subst e180; exact slawChunk_180 else
  if e181 : k = 181 then subst e181; exact slawChunk_181 else
  if e182 : k = 182 then subst e182; exact slawChunk_182 else
  if e183 : k = 183 then subst e183; exact slawChunk_183 else
  omega
end D2
