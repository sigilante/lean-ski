import Ski.D2Base
import Ski.D2K.S123
/-! Generated.  S-law of D: chunks 992..999 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_992 : slawChunk 992 = true := by decide +kernel
theorem slawChunk_993 : slawChunk 993 = true := by decide +kernel
theorem slawChunk_994 : slawChunk 994 = true := by decide +kernel
theorem slawChunk_995 : slawChunk 995 = true := by decide +kernel
theorem slawChunk_996 : slawChunk 996 = true := by decide +kernel
theorem slawChunk_997 : slawChunk 997 = true := by decide +kernel
theorem slawChunk_998 : slawChunk 998 = true := by decide +kernel
theorem slawChunk_999 : slawChunk 999 = true := by decide +kernel
theorem slawC_124 (k : Nat) (h1 : 992 ≤ k) (h2 : k < 1000) : slawChunk k = true := by
  if e992 : k = 992 then subst e992; exact slawChunk_992 else
  if e993 : k = 993 then subst e993; exact slawChunk_993 else
  if e994 : k = 994 then subst e994; exact slawChunk_994 else
  if e995 : k = 995 then subst e995; exact slawChunk_995 else
  if e996 : k = 996 then subst e996; exact slawChunk_996 else
  if e997 : k = 997 then subst e997; exact slawChunk_997 else
  if e998 : k = 998 then subst e998; exact slawChunk_998 else
  if e999 : k = 999 then subst e999; exact slawChunk_999 else
  omega
end D2
