import Ski.D2Base
import Ski.D2K.S23
/-! Generated.  S-law of D: chunks 192..199 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_192 : slawChunk 192 = true := by decide +kernel
theorem slawChunk_193 : slawChunk 193 = true := by decide +kernel
theorem slawChunk_194 : slawChunk 194 = true := by decide +kernel
theorem slawChunk_195 : slawChunk 195 = true := by decide +kernel
theorem slawChunk_196 : slawChunk 196 = true := by decide +kernel
theorem slawChunk_197 : slawChunk 197 = true := by decide +kernel
theorem slawChunk_198 : slawChunk 198 = true := by decide +kernel
theorem slawChunk_199 : slawChunk 199 = true := by decide +kernel
theorem slawC_24 (k : Nat) (h1 : 192 ≤ k) (h2 : k < 200) : slawChunk k = true := by
  if e192 : k = 192 then subst e192; exact slawChunk_192 else
  if e193 : k = 193 then subst e193; exact slawChunk_193 else
  if e194 : k = 194 then subst e194; exact slawChunk_194 else
  if e195 : k = 195 then subst e195; exact slawChunk_195 else
  if e196 : k = 196 then subst e196; exact slawChunk_196 else
  if e197 : k = 197 then subst e197; exact slawChunk_197 else
  if e198 : k = 198 then subst e198; exact slawChunk_198 else
  if e199 : k = 199 then subst e199; exact slawChunk_199 else
  omega
end D2
