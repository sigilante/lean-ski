import Ski.D2Base
import Ski.D2K.S135
/-! Generated.  S-law of D: chunks 1088..1095 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_1088 : slawChunk 1088 = true := by decide +kernel
theorem slawChunk_1089 : slawChunk 1089 = true := by decide +kernel
theorem slawChunk_1090 : slawChunk 1090 = true := by decide +kernel
theorem slawChunk_1091 : slawChunk 1091 = true := by decide +kernel
theorem slawChunk_1092 : slawChunk 1092 = true := by decide +kernel
theorem slawChunk_1093 : slawChunk 1093 = true := by decide +kernel
theorem slawChunk_1094 : slawChunk 1094 = true := by decide +kernel
theorem slawChunk_1095 : slawChunk 1095 = true := by decide +kernel
theorem slawC_136 (k : Nat) (h1 : 1088 ≤ k) (h2 : k < 1096) : slawChunk k = true := by
  if e1088 : k = 1088 then subst e1088; exact slawChunk_1088 else
  if e1089 : k = 1089 then subst e1089; exact slawChunk_1089 else
  if e1090 : k = 1090 then subst e1090; exact slawChunk_1090 else
  if e1091 : k = 1091 then subst e1091; exact slawChunk_1091 else
  if e1092 : k = 1092 then subst e1092; exact slawChunk_1092 else
  if e1093 : k = 1093 then subst e1093; exact slawChunk_1093 else
  if e1094 : k = 1094 then subst e1094; exact slawChunk_1094 else
  if e1095 : k = 1095 then subst e1095; exact slawChunk_1095 else
  omega
end D2
