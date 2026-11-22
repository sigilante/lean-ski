import Ski.D2Base
import Ski.D2K.S27
/-! Generated.  S-law of D: chunks 224..231 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_224 : slawChunk 224 = true := by decide +kernel
theorem slawChunk_225 : slawChunk 225 = true := by decide +kernel
theorem slawChunk_226 : slawChunk 226 = true := by decide +kernel
theorem slawChunk_227 : slawChunk 227 = true := by decide +kernel
theorem slawChunk_228 : slawChunk 228 = true := by decide +kernel
theorem slawChunk_229 : slawChunk 229 = true := by decide +kernel
theorem slawChunk_230 : slawChunk 230 = true := by decide +kernel
theorem slawChunk_231 : slawChunk 231 = true := by decide +kernel
theorem slawC_28 (k : Nat) (h1 : 224 ≤ k) (h2 : k < 232) : slawChunk k = true := by
  if e224 : k = 224 then subst e224; exact slawChunk_224 else
  if e225 : k = 225 then subst e225; exact slawChunk_225 else
  if e226 : k = 226 then subst e226; exact slawChunk_226 else
  if e227 : k = 227 then subst e227; exact slawChunk_227 else
  if e228 : k = 228 then subst e228; exact slawChunk_228 else
  if e229 : k = 229 then subst e229; exact slawChunk_229 else
  if e230 : k = 230 then subst e230; exact slawChunk_230 else
  if e231 : k = 231 then subst e231; exact slawChunk_231 else
  omega
end D2
