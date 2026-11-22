import Ski.D2Base
import Ski.D2K.S270
/-! Generated.  S-law of D: chunks 2168..2175 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_2168 : slawChunk 2168 = true := by decide +kernel
theorem slawChunk_2169 : slawChunk 2169 = true := by decide +kernel
theorem slawChunk_2170 : slawChunk 2170 = true := by decide +kernel
theorem slawChunk_2171 : slawChunk 2171 = true := by decide +kernel
theorem slawChunk_2172 : slawChunk 2172 = true := by decide +kernel
theorem slawChunk_2173 : slawChunk 2173 = true := by decide +kernel
theorem slawChunk_2174 : slawChunk 2174 = true := by decide +kernel
theorem slawChunk_2175 : slawChunk 2175 = true := by decide +kernel
theorem slawC_271 (k : Nat) (h1 : 2168 ≤ k) (h2 : k < 2176) : slawChunk k = true := by
  if e2168 : k = 2168 then subst e2168; exact slawChunk_2168 else
  if e2169 : k = 2169 then subst e2169; exact slawChunk_2169 else
  if e2170 : k = 2170 then subst e2170; exact slawChunk_2170 else
  if e2171 : k = 2171 then subst e2171; exact slawChunk_2171 else
  if e2172 : k = 2172 then subst e2172; exact slawChunk_2172 else
  if e2173 : k = 2173 then subst e2173; exact slawChunk_2173 else
  if e2174 : k = 2174 then subst e2174; exact slawChunk_2174 else
  if e2175 : k = 2175 then subst e2175; exact slawChunk_2175 else
  omega
end D2
