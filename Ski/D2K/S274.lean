import Ski.D2Base
import Ski.D2K.S273
/-! Generated.  S-law of D: chunks 2192..2199 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_2192 : slawChunk 2192 = true := by decide +kernel
theorem slawChunk_2193 : slawChunk 2193 = true := by decide +kernel
theorem slawChunk_2194 : slawChunk 2194 = true := by decide +kernel
theorem slawChunk_2195 : slawChunk 2195 = true := by decide +kernel
theorem slawChunk_2196 : slawChunk 2196 = true := by decide +kernel
theorem slawChunk_2197 : slawChunk 2197 = true := by decide +kernel
theorem slawChunk_2198 : slawChunk 2198 = true := by decide +kernel
theorem slawChunk_2199 : slawChunk 2199 = true := by decide +kernel
theorem slawC_274 (k : Nat) (h1 : 2192 ≤ k) (h2 : k < 2200) : slawChunk k = true := by
  if e2192 : k = 2192 then subst e2192; exact slawChunk_2192 else
  if e2193 : k = 2193 then subst e2193; exact slawChunk_2193 else
  if e2194 : k = 2194 then subst e2194; exact slawChunk_2194 else
  if e2195 : k = 2195 then subst e2195; exact slawChunk_2195 else
  if e2196 : k = 2196 then subst e2196; exact slawChunk_2196 else
  if e2197 : k = 2197 then subst e2197; exact slawChunk_2197 else
  if e2198 : k = 2198 then subst e2198; exact slawChunk_2198 else
  if e2199 : k = 2199 then subst e2199; exact slawChunk_2199 else
  omega
end D2
