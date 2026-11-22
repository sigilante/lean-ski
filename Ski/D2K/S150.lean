import Ski.D2Base
import Ski.D2K.S149
/-! Generated.  S-law of D: chunks 1200..1207 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_1200 : slawChunk 1200 = true := by decide +kernel
theorem slawChunk_1201 : slawChunk 1201 = true := by decide +kernel
theorem slawChunk_1202 : slawChunk 1202 = true := by decide +kernel
theorem slawChunk_1203 : slawChunk 1203 = true := by decide +kernel
theorem slawChunk_1204 : slawChunk 1204 = true := by decide +kernel
theorem slawChunk_1205 : slawChunk 1205 = true := by decide +kernel
theorem slawChunk_1206 : slawChunk 1206 = true := by decide +kernel
theorem slawChunk_1207 : slawChunk 1207 = true := by decide +kernel
theorem slawC_150 (k : Nat) (h1 : 1200 ≤ k) (h2 : k < 1208) : slawChunk k = true := by
  if e1200 : k = 1200 then subst e1200; exact slawChunk_1200 else
  if e1201 : k = 1201 then subst e1201; exact slawChunk_1201 else
  if e1202 : k = 1202 then subst e1202; exact slawChunk_1202 else
  if e1203 : k = 1203 then subst e1203; exact slawChunk_1203 else
  if e1204 : k = 1204 then subst e1204; exact slawChunk_1204 else
  if e1205 : k = 1205 then subst e1205; exact slawChunk_1205 else
  if e1206 : k = 1206 then subst e1206; exact slawChunk_1206 else
  if e1207 : k = 1207 then subst e1207; exact slawChunk_1207 else
  omega
end D2
