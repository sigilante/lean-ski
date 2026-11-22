import Ski.D2Base
import Ski.D2K.S268
/-! Generated.  S-law of D: chunks 2152..2159 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_2152 : slawChunk 2152 = true := by decide +kernel
theorem slawChunk_2153 : slawChunk 2153 = true := by decide +kernel
theorem slawChunk_2154 : slawChunk 2154 = true := by decide +kernel
theorem slawChunk_2155 : slawChunk 2155 = true := by decide +kernel
theorem slawChunk_2156 : slawChunk 2156 = true := by decide +kernel
theorem slawChunk_2157 : slawChunk 2157 = true := by decide +kernel
theorem slawChunk_2158 : slawChunk 2158 = true := by decide +kernel
theorem slawChunk_2159 : slawChunk 2159 = true := by decide +kernel
theorem slawC_269 (k : Nat) (h1 : 2152 ≤ k) (h2 : k < 2160) : slawChunk k = true := by
  if e2152 : k = 2152 then subst e2152; exact slawChunk_2152 else
  if e2153 : k = 2153 then subst e2153; exact slawChunk_2153 else
  if e2154 : k = 2154 then subst e2154; exact slawChunk_2154 else
  if e2155 : k = 2155 then subst e2155; exact slawChunk_2155 else
  if e2156 : k = 2156 then subst e2156; exact slawChunk_2156 else
  if e2157 : k = 2157 then subst e2157; exact slawChunk_2157 else
  if e2158 : k = 2158 then subst e2158; exact slawChunk_2158 else
  if e2159 : k = 2159 then subst e2159; exact slawChunk_2159 else
  omega
end D2
