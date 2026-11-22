import Ski.D2Base
import Ski.D2K.S49
/-! Generated.  S-law of D: chunks 400..407 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_400 : slawChunk 400 = true := by decide +kernel
theorem slawChunk_401 : slawChunk 401 = true := by decide +kernel
theorem slawChunk_402 : slawChunk 402 = true := by decide +kernel
theorem slawChunk_403 : slawChunk 403 = true := by decide +kernel
theorem slawChunk_404 : slawChunk 404 = true := by decide +kernel
theorem slawChunk_405 : slawChunk 405 = true := by decide +kernel
theorem slawChunk_406 : slawChunk 406 = true := by decide +kernel
theorem slawChunk_407 : slawChunk 407 = true := by decide +kernel
theorem slawC_50 (k : Nat) (h1 : 400 ≤ k) (h2 : k < 408) : slawChunk k = true := by
  if e400 : k = 400 then subst e400; exact slawChunk_400 else
  if e401 : k = 401 then subst e401; exact slawChunk_401 else
  if e402 : k = 402 then subst e402; exact slawChunk_402 else
  if e403 : k = 403 then subst e403; exact slawChunk_403 else
  if e404 : k = 404 then subst e404; exact slawChunk_404 else
  if e405 : k = 405 then subst e405; exact slawChunk_405 else
  if e406 : k = 406 then subst e406; exact slawChunk_406 else
  if e407 : k = 407 then subst e407; exact slawChunk_407 else
  omega
end D2
