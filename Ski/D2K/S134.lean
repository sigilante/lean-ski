import Ski.D2Base
import Ski.D2K.S133
/-! Generated.  S-law of D: chunks 1072..1079 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_1072 : slawChunk 1072 = true := by decide +kernel
theorem slawChunk_1073 : slawChunk 1073 = true := by decide +kernel
theorem slawChunk_1074 : slawChunk 1074 = true := by decide +kernel
theorem slawChunk_1075 : slawChunk 1075 = true := by decide +kernel
theorem slawChunk_1076 : slawChunk 1076 = true := by decide +kernel
theorem slawChunk_1077 : slawChunk 1077 = true := by decide +kernel
theorem slawChunk_1078 : slawChunk 1078 = true := by decide +kernel
theorem slawChunk_1079 : slawChunk 1079 = true := by decide +kernel
theorem slawC_134 (k : Nat) (h1 : 1072 ≤ k) (h2 : k < 1080) : slawChunk k = true := by
  if e1072 : k = 1072 then subst e1072; exact slawChunk_1072 else
  if e1073 : k = 1073 then subst e1073; exact slawChunk_1073 else
  if e1074 : k = 1074 then subst e1074; exact slawChunk_1074 else
  if e1075 : k = 1075 then subst e1075; exact slawChunk_1075 else
  if e1076 : k = 1076 then subst e1076; exact slawChunk_1076 else
  if e1077 : k = 1077 then subst e1077; exact slawChunk_1077 else
  if e1078 : k = 1078 then subst e1078; exact slawChunk_1078 else
  if e1079 : k = 1079 then subst e1079; exact slawChunk_1079 else
  omega
end D2
