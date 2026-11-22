import Ski.D2Base
import Ski.D2K.S130
/-! Generated.  S-law of D: chunks 1048..1055 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_1048 : slawChunk 1048 = true := by decide +kernel
theorem slawChunk_1049 : slawChunk 1049 = true := by decide +kernel
theorem slawChunk_1050 : slawChunk 1050 = true := by decide +kernel
theorem slawChunk_1051 : slawChunk 1051 = true := by decide +kernel
theorem slawChunk_1052 : slawChunk 1052 = true := by decide +kernel
theorem slawChunk_1053 : slawChunk 1053 = true := by decide +kernel
theorem slawChunk_1054 : slawChunk 1054 = true := by decide +kernel
theorem slawChunk_1055 : slawChunk 1055 = true := by decide +kernel
theorem slawC_131 (k : Nat) (h1 : 1048 ≤ k) (h2 : k < 1056) : slawChunk k = true := by
  if e1048 : k = 1048 then subst e1048; exact slawChunk_1048 else
  if e1049 : k = 1049 then subst e1049; exact slawChunk_1049 else
  if e1050 : k = 1050 then subst e1050; exact slawChunk_1050 else
  if e1051 : k = 1051 then subst e1051; exact slawChunk_1051 else
  if e1052 : k = 1052 then subst e1052; exact slawChunk_1052 else
  if e1053 : k = 1053 then subst e1053; exact slawChunk_1053 else
  if e1054 : k = 1054 then subst e1054; exact slawChunk_1054 else
  if e1055 : k = 1055 then subst e1055; exact slawChunk_1055 else
  omega
end D2
