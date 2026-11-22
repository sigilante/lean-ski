import Ski.D2Base
import Ski.D2K.S139
/-! Generated.  S-law of D: chunks 1120..1127 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_1120 : slawChunk 1120 = true := by decide +kernel
theorem slawChunk_1121 : slawChunk 1121 = true := by decide +kernel
theorem slawChunk_1122 : slawChunk 1122 = true := by decide +kernel
theorem slawChunk_1123 : slawChunk 1123 = true := by decide +kernel
theorem slawChunk_1124 : slawChunk 1124 = true := by decide +kernel
theorem slawChunk_1125 : slawChunk 1125 = true := by decide +kernel
theorem slawChunk_1126 : slawChunk 1126 = true := by decide +kernel
theorem slawChunk_1127 : slawChunk 1127 = true := by decide +kernel
theorem slawC_140 (k : Nat) (h1 : 1120 ≤ k) (h2 : k < 1128) : slawChunk k = true := by
  if e1120 : k = 1120 then subst e1120; exact slawChunk_1120 else
  if e1121 : k = 1121 then subst e1121; exact slawChunk_1121 else
  if e1122 : k = 1122 then subst e1122; exact slawChunk_1122 else
  if e1123 : k = 1123 then subst e1123; exact slawChunk_1123 else
  if e1124 : k = 1124 then subst e1124; exact slawChunk_1124 else
  if e1125 : k = 1125 then subst e1125; exact slawChunk_1125 else
  if e1126 : k = 1126 then subst e1126; exact slawChunk_1126 else
  if e1127 : k = 1127 then subst e1127; exact slawChunk_1127 else
  omega
end D2
