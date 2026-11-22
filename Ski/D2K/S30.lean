import Ski.D2Base
import Ski.D2K.S29
/-! Generated.  S-law of D: chunks 240..247 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_240 : slawChunk 240 = true := by decide +kernel
theorem slawChunk_241 : slawChunk 241 = true := by decide +kernel
theorem slawChunk_242 : slawChunk 242 = true := by decide +kernel
theorem slawChunk_243 : slawChunk 243 = true := by decide +kernel
theorem slawChunk_244 : slawChunk 244 = true := by decide +kernel
theorem slawChunk_245 : slawChunk 245 = true := by decide +kernel
theorem slawChunk_246 : slawChunk 246 = true := by decide +kernel
theorem slawChunk_247 : slawChunk 247 = true := by decide +kernel
theorem slawC_30 (k : Nat) (h1 : 240 ≤ k) (h2 : k < 248) : slawChunk k = true := by
  if e240 : k = 240 then subst e240; exact slawChunk_240 else
  if e241 : k = 241 then subst e241; exact slawChunk_241 else
  if e242 : k = 242 then subst e242; exact slawChunk_242 else
  if e243 : k = 243 then subst e243; exact slawChunk_243 else
  if e244 : k = 244 then subst e244; exact slawChunk_244 else
  if e245 : k = 245 then subst e245; exact slawChunk_245 else
  if e246 : k = 246 then subst e246; exact slawChunk_246 else
  if e247 : k = 247 then subst e247; exact slawChunk_247 else
  omega
end D2
