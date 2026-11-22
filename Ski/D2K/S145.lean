import Ski.D2Base
import Ski.D2K.S144
/-! Generated.  S-law of D: chunks 1160..1167 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_1160 : slawChunk 1160 = true := by decide +kernel
theorem slawChunk_1161 : slawChunk 1161 = true := by decide +kernel
theorem slawChunk_1162 : slawChunk 1162 = true := by decide +kernel
theorem slawChunk_1163 : slawChunk 1163 = true := by decide +kernel
theorem slawChunk_1164 : slawChunk 1164 = true := by decide +kernel
theorem slawChunk_1165 : slawChunk 1165 = true := by decide +kernel
theorem slawChunk_1166 : slawChunk 1166 = true := by decide +kernel
theorem slawChunk_1167 : slawChunk 1167 = true := by decide +kernel
theorem slawC_145 (k : Nat) (h1 : 1160 ≤ k) (h2 : k < 1168) : slawChunk k = true := by
  if e1160 : k = 1160 then subst e1160; exact slawChunk_1160 else
  if e1161 : k = 1161 then subst e1161; exact slawChunk_1161 else
  if e1162 : k = 1162 then subst e1162; exact slawChunk_1162 else
  if e1163 : k = 1163 then subst e1163; exact slawChunk_1163 else
  if e1164 : k = 1164 then subst e1164; exact slawChunk_1164 else
  if e1165 : k = 1165 then subst e1165; exact slawChunk_1165 else
  if e1166 : k = 1166 then subst e1166; exact slawChunk_1166 else
  if e1167 : k = 1167 then subst e1167; exact slawChunk_1167 else
  omega
end D2
