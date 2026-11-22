import Ski.D2Base
import Ski.D2K.S148
/-! Generated.  S-law of D: chunks 1192..1199 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_1192 : slawChunk 1192 = true := by decide +kernel
theorem slawChunk_1193 : slawChunk 1193 = true := by decide +kernel
theorem slawChunk_1194 : slawChunk 1194 = true := by decide +kernel
theorem slawChunk_1195 : slawChunk 1195 = true := by decide +kernel
theorem slawChunk_1196 : slawChunk 1196 = true := by decide +kernel
theorem slawChunk_1197 : slawChunk 1197 = true := by decide +kernel
theorem slawChunk_1198 : slawChunk 1198 = true := by decide +kernel
theorem slawChunk_1199 : slawChunk 1199 = true := by decide +kernel
theorem slawC_149 (k : Nat) (h1 : 1192 ≤ k) (h2 : k < 1200) : slawChunk k = true := by
  if e1192 : k = 1192 then subst e1192; exact slawChunk_1192 else
  if e1193 : k = 1193 then subst e1193; exact slawChunk_1193 else
  if e1194 : k = 1194 then subst e1194; exact slawChunk_1194 else
  if e1195 : k = 1195 then subst e1195; exact slawChunk_1195 else
  if e1196 : k = 1196 then subst e1196; exact slawChunk_1196 else
  if e1197 : k = 1197 then subst e1197; exact slawChunk_1197 else
  if e1198 : k = 1198 then subst e1198; exact slawChunk_1198 else
  if e1199 : k = 1199 then subst e1199; exact slawChunk_1199 else
  omega
end D2
