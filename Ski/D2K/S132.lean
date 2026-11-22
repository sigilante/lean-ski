import Ski.D2Base
import Ski.D2K.S131
/-! Generated.  S-law of D: chunks 1056..1063 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_1056 : slawChunk 1056 = true := by decide +kernel
theorem slawChunk_1057 : slawChunk 1057 = true := by decide +kernel
theorem slawChunk_1058 : slawChunk 1058 = true := by decide +kernel
theorem slawChunk_1059 : slawChunk 1059 = true := by decide +kernel
theorem slawChunk_1060 : slawChunk 1060 = true := by decide +kernel
theorem slawChunk_1061 : slawChunk 1061 = true := by decide +kernel
theorem slawChunk_1062 : slawChunk 1062 = true := by decide +kernel
theorem slawChunk_1063 : slawChunk 1063 = true := by decide +kernel
theorem slawC_132 (k : Nat) (h1 : 1056 ≤ k) (h2 : k < 1064) : slawChunk k = true := by
  if e1056 : k = 1056 then subst e1056; exact slawChunk_1056 else
  if e1057 : k = 1057 then subst e1057; exact slawChunk_1057 else
  if e1058 : k = 1058 then subst e1058; exact slawChunk_1058 else
  if e1059 : k = 1059 then subst e1059; exact slawChunk_1059 else
  if e1060 : k = 1060 then subst e1060; exact slawChunk_1060 else
  if e1061 : k = 1061 then subst e1061; exact slawChunk_1061 else
  if e1062 : k = 1062 then subst e1062; exact slawChunk_1062 else
  if e1063 : k = 1063 then subst e1063; exact slawChunk_1063 else
  omega
end D2
