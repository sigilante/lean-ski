import Ski.D2Base
import Ski.D2K.S124
/-! Generated.  S-law of D: chunks 1000..1007 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_1000 : slawChunk 1000 = true := by decide +kernel
theorem slawChunk_1001 : slawChunk 1001 = true := by decide +kernel
theorem slawChunk_1002 : slawChunk 1002 = true := by decide +kernel
theorem slawChunk_1003 : slawChunk 1003 = true := by decide +kernel
theorem slawChunk_1004 : slawChunk 1004 = true := by decide +kernel
theorem slawChunk_1005 : slawChunk 1005 = true := by decide +kernel
theorem slawChunk_1006 : slawChunk 1006 = true := by decide +kernel
theorem slawChunk_1007 : slawChunk 1007 = true := by decide +kernel
theorem slawC_125 (k : Nat) (h1 : 1000 ≤ k) (h2 : k < 1008) : slawChunk k = true := by
  if e1000 : k = 1000 then subst e1000; exact slawChunk_1000 else
  if e1001 : k = 1001 then subst e1001; exact slawChunk_1001 else
  if e1002 : k = 1002 then subst e1002; exact slawChunk_1002 else
  if e1003 : k = 1003 then subst e1003; exact slawChunk_1003 else
  if e1004 : k = 1004 then subst e1004; exact slawChunk_1004 else
  if e1005 : k = 1005 then subst e1005; exact slawChunk_1005 else
  if e1006 : k = 1006 then subst e1006; exact slawChunk_1006 else
  if e1007 : k = 1007 then subst e1007; exact slawChunk_1007 else
  omega
end D2
