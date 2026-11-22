import Ski.D2Base
import Ski.D2K.S127
/-! Generated.  S-law of D: chunks 1024..1031 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_1024 : slawChunk 1024 = true := by decide +kernel
theorem slawChunk_1025 : slawChunk 1025 = true := by decide +kernel
theorem slawChunk_1026 : slawChunk 1026 = true := by decide +kernel
theorem slawChunk_1027 : slawChunk 1027 = true := by decide +kernel
theorem slawChunk_1028 : slawChunk 1028 = true := by decide +kernel
theorem slawChunk_1029 : slawChunk 1029 = true := by decide +kernel
theorem slawChunk_1030 : slawChunk 1030 = true := by decide +kernel
theorem slawChunk_1031 : slawChunk 1031 = true := by decide +kernel
theorem slawC_128 (k : Nat) (h1 : 1024 ≤ k) (h2 : k < 1032) : slawChunk k = true := by
  if e1024 : k = 1024 then subst e1024; exact slawChunk_1024 else
  if e1025 : k = 1025 then subst e1025; exact slawChunk_1025 else
  if e1026 : k = 1026 then subst e1026; exact slawChunk_1026 else
  if e1027 : k = 1027 then subst e1027; exact slawChunk_1027 else
  if e1028 : k = 1028 then subst e1028; exact slawChunk_1028 else
  if e1029 : k = 1029 then subst e1029; exact slawChunk_1029 else
  if e1030 : k = 1030 then subst e1030; exact slawChunk_1030 else
  if e1031 : k = 1031 then subst e1031; exact slawChunk_1031 else
  omega
end D2
