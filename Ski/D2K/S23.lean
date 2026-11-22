import Ski.D2Base
import Ski.D2K.S22
/-! Generated.  S-law of D: chunks 184..191 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_184 : slawChunk 184 = true := by decide +kernel
theorem slawChunk_185 : slawChunk 185 = true := by decide +kernel
theorem slawChunk_186 : slawChunk 186 = true := by decide +kernel
theorem slawChunk_187 : slawChunk 187 = true := by decide +kernel
theorem slawChunk_188 : slawChunk 188 = true := by decide +kernel
theorem slawChunk_189 : slawChunk 189 = true := by decide +kernel
theorem slawChunk_190 : slawChunk 190 = true := by decide +kernel
theorem slawChunk_191 : slawChunk 191 = true := by decide +kernel
theorem slawC_23 (k : Nat) (h1 : 184 ≤ k) (h2 : k < 192) : slawChunk k = true := by
  if e184 : k = 184 then subst e184; exact slawChunk_184 else
  if e185 : k = 185 then subst e185; exact slawChunk_185 else
  if e186 : k = 186 then subst e186; exact slawChunk_186 else
  if e187 : k = 187 then subst e187; exact slawChunk_187 else
  if e188 : k = 188 then subst e188; exact slawChunk_188 else
  if e189 : k = 189 then subst e189; exact slawChunk_189 else
  if e190 : k = 190 then subst e190; exact slawChunk_190 else
  if e191 : k = 191 then subst e191; exact slawChunk_191 else
  omega
end D2
