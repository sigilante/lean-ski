import Ski.D2Base
import Ski.D2K.S16
/-! Generated.  S-law of D: chunks 136..143 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_136 : slawChunk 136 = true := by decide +kernel
theorem slawChunk_137 : slawChunk 137 = true := by decide +kernel
theorem slawChunk_138 : slawChunk 138 = true := by decide +kernel
theorem slawChunk_139 : slawChunk 139 = true := by decide +kernel
theorem slawChunk_140 : slawChunk 140 = true := by decide +kernel
theorem slawChunk_141 : slawChunk 141 = true := by decide +kernel
theorem slawChunk_142 : slawChunk 142 = true := by decide +kernel
theorem slawChunk_143 : slawChunk 143 = true := by decide +kernel
theorem slawC_17 (k : Nat) (h1 : 136 ≤ k) (h2 : k < 144) : slawChunk k = true := by
  if e136 : k = 136 then subst e136; exact slawChunk_136 else
  if e137 : k = 137 then subst e137; exact slawChunk_137 else
  if e138 : k = 138 then subst e138; exact slawChunk_138 else
  if e139 : k = 139 then subst e139; exact slawChunk_139 else
  if e140 : k = 140 then subst e140; exact slawChunk_140 else
  if e141 : k = 141 then subst e141; exact slawChunk_141 else
  if e142 : k = 142 then subst e142; exact slawChunk_142 else
  if e143 : k = 143 then subst e143; exact slawChunk_143 else
  omega
end D2
