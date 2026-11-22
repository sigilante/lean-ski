import Ski.D2Base
import Ski.D2K.S134
/-! Generated.  S-law of D: chunks 1080..1087 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_1080 : slawChunk 1080 = true := by decide +kernel
theorem slawChunk_1081 : slawChunk 1081 = true := by decide +kernel
theorem slawChunk_1082 : slawChunk 1082 = true := by decide +kernel
theorem slawChunk_1083 : slawChunk 1083 = true := by decide +kernel
theorem slawChunk_1084 : slawChunk 1084 = true := by decide +kernel
theorem slawChunk_1085 : slawChunk 1085 = true := by decide +kernel
theorem slawChunk_1086 : slawChunk 1086 = true := by decide +kernel
theorem slawChunk_1087 : slawChunk 1087 = true := by decide +kernel
theorem slawC_135 (k : Nat) (h1 : 1080 ≤ k) (h2 : k < 1088) : slawChunk k = true := by
  if e1080 : k = 1080 then subst e1080; exact slawChunk_1080 else
  if e1081 : k = 1081 then subst e1081; exact slawChunk_1081 else
  if e1082 : k = 1082 then subst e1082; exact slawChunk_1082 else
  if e1083 : k = 1083 then subst e1083; exact slawChunk_1083 else
  if e1084 : k = 1084 then subst e1084; exact slawChunk_1084 else
  if e1085 : k = 1085 then subst e1085; exact slawChunk_1085 else
  if e1086 : k = 1086 then subst e1086; exact slawChunk_1086 else
  if e1087 : k = 1087 then subst e1087; exact slawChunk_1087 else
  omega
end D2
