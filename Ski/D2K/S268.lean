import Ski.D2Base
import Ski.D2K.S267
/-! Generated.  S-law of D: chunks 2144..2151 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_2144 : slawChunk 2144 = true := by decide +kernel
theorem slawChunk_2145 : slawChunk 2145 = true := by decide +kernel
theorem slawChunk_2146 : slawChunk 2146 = true := by decide +kernel
theorem slawChunk_2147 : slawChunk 2147 = true := by decide +kernel
theorem slawChunk_2148 : slawChunk 2148 = true := by decide +kernel
theorem slawChunk_2149 : slawChunk 2149 = true := by decide +kernel
theorem slawChunk_2150 : slawChunk 2150 = true := by decide +kernel
theorem slawChunk_2151 : slawChunk 2151 = true := by decide +kernel
theorem slawC_268 (k : Nat) (h1 : 2144 ≤ k) (h2 : k < 2152) : slawChunk k = true := by
  if e2144 : k = 2144 then subst e2144; exact slawChunk_2144 else
  if e2145 : k = 2145 then subst e2145; exact slawChunk_2145 else
  if e2146 : k = 2146 then subst e2146; exact slawChunk_2146 else
  if e2147 : k = 2147 then subst e2147; exact slawChunk_2147 else
  if e2148 : k = 2148 then subst e2148; exact slawChunk_2148 else
  if e2149 : k = 2149 then subst e2149; exact slawChunk_2149 else
  if e2150 : k = 2150 then subst e2150; exact slawChunk_2150 else
  if e2151 : k = 2151 then subst e2151; exact slawChunk_2151 else
  omega
end D2
