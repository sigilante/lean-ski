import Ski.D2Base
import Ski.D2K.S6
/-! Generated.  S-law of D: chunks 56..63 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_56 : slawChunk 56 = true := by decide +kernel
theorem slawChunk_57 : slawChunk 57 = true := by decide +kernel
theorem slawChunk_58 : slawChunk 58 = true := by decide +kernel
theorem slawChunk_59 : slawChunk 59 = true := by decide +kernel
theorem slawChunk_60 : slawChunk 60 = true := by decide +kernel
theorem slawChunk_61 : slawChunk 61 = true := by decide +kernel
theorem slawChunk_62 : slawChunk 62 = true := by decide +kernel
theorem slawChunk_63 : slawChunk 63 = true := by decide +kernel
theorem slawC_7 (k : Nat) (h1 : 56 ≤ k) (h2 : k < 64) : slawChunk k = true := by
  if e56 : k = 56 then subst e56; exact slawChunk_56 else
  if e57 : k = 57 then subst e57; exact slawChunk_57 else
  if e58 : k = 58 then subst e58; exact slawChunk_58 else
  if e59 : k = 59 then subst e59; exact slawChunk_59 else
  if e60 : k = 60 then subst e60; exact slawChunk_60 else
  if e61 : k = 61 then subst e61; exact slawChunk_61 else
  if e62 : k = 62 then subst e62; exact slawChunk_62 else
  if e63 : k = 63 then subst e63; exact slawChunk_63 else
  omega
end D2
