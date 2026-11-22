import Ski.D2Base
import Ski.D2K.S18
/-! Generated.  S-law of D: chunks 152..159 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_152 : slawChunk 152 = true := by decide +kernel
theorem slawChunk_153 : slawChunk 153 = true := by decide +kernel
theorem slawChunk_154 : slawChunk 154 = true := by decide +kernel
theorem slawChunk_155 : slawChunk 155 = true := by decide +kernel
theorem slawChunk_156 : slawChunk 156 = true := by decide +kernel
theorem slawChunk_157 : slawChunk 157 = true := by decide +kernel
theorem slawChunk_158 : slawChunk 158 = true := by decide +kernel
theorem slawChunk_159 : slawChunk 159 = true := by decide +kernel
theorem slawC_19 (k : Nat) (h1 : 152 ≤ k) (h2 : k < 160) : slawChunk k = true := by
  if e152 : k = 152 then subst e152; exact slawChunk_152 else
  if e153 : k = 153 then subst e153; exact slawChunk_153 else
  if e154 : k = 154 then subst e154; exact slawChunk_154 else
  if e155 : k = 155 then subst e155; exact slawChunk_155 else
  if e156 : k = 156 then subst e156; exact slawChunk_156 else
  if e157 : k = 157 then subst e157; exact slawChunk_157 else
  if e158 : k = 158 then subst e158; exact slawChunk_158 else
  if e159 : k = 159 then subst e159; exact slawChunk_159 else
  omega
end D2
