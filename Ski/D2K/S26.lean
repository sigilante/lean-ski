import Ski.D2Base
import Ski.D2K.S25
/-! Generated.  S-law of D: chunks 208..215 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_208 : slawChunk 208 = true := by decide +kernel
theorem slawChunk_209 : slawChunk 209 = true := by decide +kernel
theorem slawChunk_210 : slawChunk 210 = true := by decide +kernel
theorem slawChunk_211 : slawChunk 211 = true := by decide +kernel
theorem slawChunk_212 : slawChunk 212 = true := by decide +kernel
theorem slawChunk_213 : slawChunk 213 = true := by decide +kernel
theorem slawChunk_214 : slawChunk 214 = true := by decide +kernel
theorem slawChunk_215 : slawChunk 215 = true := by decide +kernel
theorem slawC_26 (k : Nat) (h1 : 208 ≤ k) (h2 : k < 216) : slawChunk k = true := by
  if e208 : k = 208 then subst e208; exact slawChunk_208 else
  if e209 : k = 209 then subst e209; exact slawChunk_209 else
  if e210 : k = 210 then subst e210; exact slawChunk_210 else
  if e211 : k = 211 then subst e211; exact slawChunk_211 else
  if e212 : k = 212 then subst e212; exact slawChunk_212 else
  if e213 : k = 213 then subst e213; exact slawChunk_213 else
  if e214 : k = 214 then subst e214; exact slawChunk_214 else
  if e215 : k = 215 then subst e215; exact slawChunk_215 else
  omega
end D2
