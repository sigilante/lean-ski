import Ski.D2Base
import Ski.D2K.S126
/-! Generated.  S-law of D: chunks 1016..1023 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_1016 : slawChunk 1016 = true := by decide +kernel
theorem slawChunk_1017 : slawChunk 1017 = true := by decide +kernel
theorem slawChunk_1018 : slawChunk 1018 = true := by decide +kernel
theorem slawChunk_1019 : slawChunk 1019 = true := by decide +kernel
theorem slawChunk_1020 : slawChunk 1020 = true := by decide +kernel
theorem slawChunk_1021 : slawChunk 1021 = true := by decide +kernel
theorem slawChunk_1022 : slawChunk 1022 = true := by decide +kernel
theorem slawChunk_1023 : slawChunk 1023 = true := by decide +kernel
theorem slawC_127 (k : Nat) (h1 : 1016 ≤ k) (h2 : k < 1024) : slawChunk k = true := by
  if e1016 : k = 1016 then subst e1016; exact slawChunk_1016 else
  if e1017 : k = 1017 then subst e1017; exact slawChunk_1017 else
  if e1018 : k = 1018 then subst e1018; exact slawChunk_1018 else
  if e1019 : k = 1019 then subst e1019; exact slawChunk_1019 else
  if e1020 : k = 1020 then subst e1020; exact slawChunk_1020 else
  if e1021 : k = 1021 then subst e1021; exact slawChunk_1021 else
  if e1022 : k = 1022 then subst e1022; exact slawChunk_1022 else
  if e1023 : k = 1023 then subst e1023; exact slawChunk_1023 else
  omega
end D2
