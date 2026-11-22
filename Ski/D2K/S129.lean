import Ski.D2Base
import Ski.D2K.S128
/-! Generated.  S-law of D: chunks 1032..1039 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_1032 : slawChunk 1032 = true := by decide +kernel
theorem slawChunk_1033 : slawChunk 1033 = true := by decide +kernel
theorem slawChunk_1034 : slawChunk 1034 = true := by decide +kernel
theorem slawChunk_1035 : slawChunk 1035 = true := by decide +kernel
theorem slawChunk_1036 : slawChunk 1036 = true := by decide +kernel
theorem slawChunk_1037 : slawChunk 1037 = true := by decide +kernel
theorem slawChunk_1038 : slawChunk 1038 = true := by decide +kernel
theorem slawChunk_1039 : slawChunk 1039 = true := by decide +kernel
theorem slawC_129 (k : Nat) (h1 : 1032 ≤ k) (h2 : k < 1040) : slawChunk k = true := by
  if e1032 : k = 1032 then subst e1032; exact slawChunk_1032 else
  if e1033 : k = 1033 then subst e1033; exact slawChunk_1033 else
  if e1034 : k = 1034 then subst e1034; exact slawChunk_1034 else
  if e1035 : k = 1035 then subst e1035; exact slawChunk_1035 else
  if e1036 : k = 1036 then subst e1036; exact slawChunk_1036 else
  if e1037 : k = 1037 then subst e1037; exact slawChunk_1037 else
  if e1038 : k = 1038 then subst e1038; exact slawChunk_1038 else
  if e1039 : k = 1039 then subst e1039; exact slawChunk_1039 else
  omega
end D2
