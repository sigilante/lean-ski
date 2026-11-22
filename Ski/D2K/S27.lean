import Ski.D2Base
import Ski.D2K.S26
/-! Generated.  S-law of D: chunks 216..223 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_216 : slawChunk 216 = true := by decide +kernel
theorem slawChunk_217 : slawChunk 217 = true := by decide +kernel
theorem slawChunk_218 : slawChunk 218 = true := by decide +kernel
theorem slawChunk_219 : slawChunk 219 = true := by decide +kernel
theorem slawChunk_220 : slawChunk 220 = true := by decide +kernel
theorem slawChunk_221 : slawChunk 221 = true := by decide +kernel
theorem slawChunk_222 : slawChunk 222 = true := by decide +kernel
theorem slawChunk_223 : slawChunk 223 = true := by decide +kernel
theorem slawC_27 (k : Nat) (h1 : 216 ≤ k) (h2 : k < 224) : slawChunk k = true := by
  if e216 : k = 216 then subst e216; exact slawChunk_216 else
  if e217 : k = 217 then subst e217; exact slawChunk_217 else
  if e218 : k = 218 then subst e218; exact slawChunk_218 else
  if e219 : k = 219 then subst e219; exact slawChunk_219 else
  if e220 : k = 220 then subst e220; exact slawChunk_220 else
  if e221 : k = 221 then subst e221; exact slawChunk_221 else
  if e222 : k = 222 then subst e222; exact slawChunk_222 else
  if e223 : k = 223 then subst e223; exact slawChunk_223 else
  omega
end D2
