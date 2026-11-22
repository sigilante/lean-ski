import Ski.D2Base
import Ski.D2K.S13
/-! Generated.  S-law of D: chunks 112..119 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_112 : slawChunk 112 = true := by decide +kernel
theorem slawChunk_113 : slawChunk 113 = true := by decide +kernel
theorem slawChunk_114 : slawChunk 114 = true := by decide +kernel
theorem slawChunk_115 : slawChunk 115 = true := by decide +kernel
theorem slawChunk_116 : slawChunk 116 = true := by decide +kernel
theorem slawChunk_117 : slawChunk 117 = true := by decide +kernel
theorem slawChunk_118 : slawChunk 118 = true := by decide +kernel
theorem slawChunk_119 : slawChunk 119 = true := by decide +kernel
theorem slawC_14 (k : Nat) (h1 : 112 ≤ k) (h2 : k < 120) : slawChunk k = true := by
  if e112 : k = 112 then subst e112; exact slawChunk_112 else
  if e113 : k = 113 then subst e113; exact slawChunk_113 else
  if e114 : k = 114 then subst e114; exact slawChunk_114 else
  if e115 : k = 115 then subst e115; exact slawChunk_115 else
  if e116 : k = 116 then subst e116; exact slawChunk_116 else
  if e117 : k = 117 then subst e117; exact slawChunk_117 else
  if e118 : k = 118 then subst e118; exact slawChunk_118 else
  if e119 : k = 119 then subst e119; exact slawChunk_119 else
  omega
end D2
