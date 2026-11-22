import Ski.D2Base
import Ski.D2K.S138
/-! Generated.  S-law of D: chunks 1112..1119 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_1112 : slawChunk 1112 = true := by decide +kernel
theorem slawChunk_1113 : slawChunk 1113 = true := by decide +kernel
theorem slawChunk_1114 : slawChunk 1114 = true := by decide +kernel
theorem slawChunk_1115 : slawChunk 1115 = true := by decide +kernel
theorem slawChunk_1116 : slawChunk 1116 = true := by decide +kernel
theorem slawChunk_1117 : slawChunk 1117 = true := by decide +kernel
theorem slawChunk_1118 : slawChunk 1118 = true := by decide +kernel
theorem slawChunk_1119 : slawChunk 1119 = true := by decide +kernel
theorem slawC_139 (k : Nat) (h1 : 1112 ≤ k) (h2 : k < 1120) : slawChunk k = true := by
  if e1112 : k = 1112 then subst e1112; exact slawChunk_1112 else
  if e1113 : k = 1113 then subst e1113; exact slawChunk_1113 else
  if e1114 : k = 1114 then subst e1114; exact slawChunk_1114 else
  if e1115 : k = 1115 then subst e1115; exact slawChunk_1115 else
  if e1116 : k = 1116 then subst e1116; exact slawChunk_1116 else
  if e1117 : k = 1117 then subst e1117; exact slawChunk_1117 else
  if e1118 : k = 1118 then subst e1118; exact slawChunk_1118 else
  if e1119 : k = 1119 then subst e1119; exact slawChunk_1119 else
  omega
end D2
