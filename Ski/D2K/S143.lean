import Ski.D2Base
import Ski.D2K.S142
/-! Generated.  S-law of D: chunks 1144..1151 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_1144 : slawChunk 1144 = true := by decide +kernel
theorem slawChunk_1145 : slawChunk 1145 = true := by decide +kernel
theorem slawChunk_1146 : slawChunk 1146 = true := by decide +kernel
theorem slawChunk_1147 : slawChunk 1147 = true := by decide +kernel
theorem slawChunk_1148 : slawChunk 1148 = true := by decide +kernel
theorem slawChunk_1149 : slawChunk 1149 = true := by decide +kernel
theorem slawChunk_1150 : slawChunk 1150 = true := by decide +kernel
theorem slawChunk_1151 : slawChunk 1151 = true := by decide +kernel
theorem slawC_143 (k : Nat) (h1 : 1144 ≤ k) (h2 : k < 1152) : slawChunk k = true := by
  if e1144 : k = 1144 then subst e1144; exact slawChunk_1144 else
  if e1145 : k = 1145 then subst e1145; exact slawChunk_1145 else
  if e1146 : k = 1146 then subst e1146; exact slawChunk_1146 else
  if e1147 : k = 1147 then subst e1147; exact slawChunk_1147 else
  if e1148 : k = 1148 then subst e1148; exact slawChunk_1148 else
  if e1149 : k = 1149 then subst e1149; exact slawChunk_1149 else
  if e1150 : k = 1150 then subst e1150; exact slawChunk_1150 else
  if e1151 : k = 1151 then subst e1151; exact slawChunk_1151 else
  omega
end D2
