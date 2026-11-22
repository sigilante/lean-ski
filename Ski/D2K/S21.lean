import Ski.D2Base
import Ski.D2K.S20
/-! Generated.  S-law of D: chunks 168..175 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_168 : slawChunk 168 = true := by decide +kernel
theorem slawChunk_169 : slawChunk 169 = true := by decide +kernel
theorem slawChunk_170 : slawChunk 170 = true := by decide +kernel
theorem slawChunk_171 : slawChunk 171 = true := by decide +kernel
theorem slawChunk_172 : slawChunk 172 = true := by decide +kernel
theorem slawChunk_173 : slawChunk 173 = true := by decide +kernel
theorem slawChunk_174 : slawChunk 174 = true := by decide +kernel
theorem slawChunk_175 : slawChunk 175 = true := by decide +kernel
theorem slawC_21 (k : Nat) (h1 : 168 ≤ k) (h2 : k < 176) : slawChunk k = true := by
  if e168 : k = 168 then subst e168; exact slawChunk_168 else
  if e169 : k = 169 then subst e169; exact slawChunk_169 else
  if e170 : k = 170 then subst e170; exact slawChunk_170 else
  if e171 : k = 171 then subst e171; exact slawChunk_171 else
  if e172 : k = 172 then subst e172; exact slawChunk_172 else
  if e173 : k = 173 then subst e173; exact slawChunk_173 else
  if e174 : k = 174 then subst e174; exact slawChunk_174 else
  if e175 : k = 175 then subst e175; exact slawChunk_175 else
  omega
end D2
