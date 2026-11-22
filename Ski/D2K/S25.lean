import Ski.D2Base
import Ski.D2K.S24
/-! Generated.  S-law of D: chunks 200..207 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_200 : slawChunk 200 = true := by decide +kernel
theorem slawChunk_201 : slawChunk 201 = true := by decide +kernel
theorem slawChunk_202 : slawChunk 202 = true := by decide +kernel
theorem slawChunk_203 : slawChunk 203 = true := by decide +kernel
theorem slawChunk_204 : slawChunk 204 = true := by decide +kernel
theorem slawChunk_205 : slawChunk 205 = true := by decide +kernel
theorem slawChunk_206 : slawChunk 206 = true := by decide +kernel
theorem slawChunk_207 : slawChunk 207 = true := by decide +kernel
theorem slawC_25 (k : Nat) (h1 : 200 ≤ k) (h2 : k < 208) : slawChunk k = true := by
  if e200 : k = 200 then subst e200; exact slawChunk_200 else
  if e201 : k = 201 then subst e201; exact slawChunk_201 else
  if e202 : k = 202 then subst e202; exact slawChunk_202 else
  if e203 : k = 203 then subst e203; exact slawChunk_203 else
  if e204 : k = 204 then subst e204; exact slawChunk_204 else
  if e205 : k = 205 then subst e205; exact slawChunk_205 else
  if e206 : k = 206 then subst e206; exact slawChunk_206 else
  if e207 : k = 207 then subst e207; exact slawChunk_207 else
  omega
end D2
