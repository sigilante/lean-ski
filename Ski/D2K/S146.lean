import Ski.D2Base
import Ski.D2K.S145
/-! Generated.  S-law of D: chunks 1168..1175 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_1168 : slawChunk 1168 = true := by decide +kernel
theorem slawChunk_1169 : slawChunk 1169 = true := by decide +kernel
theorem slawChunk_1170 : slawChunk 1170 = true := by decide +kernel
theorem slawChunk_1171 : slawChunk 1171 = true := by decide +kernel
theorem slawChunk_1172 : slawChunk 1172 = true := by decide +kernel
theorem slawChunk_1173 : slawChunk 1173 = true := by decide +kernel
theorem slawChunk_1174 : slawChunk 1174 = true := by decide +kernel
theorem slawChunk_1175 : slawChunk 1175 = true := by decide +kernel
theorem slawC_146 (k : Nat) (h1 : 1168 ≤ k) (h2 : k < 1176) : slawChunk k = true := by
  if e1168 : k = 1168 then subst e1168; exact slawChunk_1168 else
  if e1169 : k = 1169 then subst e1169; exact slawChunk_1169 else
  if e1170 : k = 1170 then subst e1170; exact slawChunk_1170 else
  if e1171 : k = 1171 then subst e1171; exact slawChunk_1171 else
  if e1172 : k = 1172 then subst e1172; exact slawChunk_1172 else
  if e1173 : k = 1173 then subst e1173; exact slawChunk_1173 else
  if e1174 : k = 1174 then subst e1174; exact slawChunk_1174 else
  if e1175 : k = 1175 then subst e1175; exact slawChunk_1175 else
  omega
end D2
