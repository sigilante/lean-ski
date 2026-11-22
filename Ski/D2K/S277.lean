import Ski.D2Base
import Ski.D2K.S276
/-! Generated.  S-law of D: chunks 2216..2223 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_2216 : slawChunk 2216 = true := by decide +kernel
theorem slawChunk_2217 : slawChunk 2217 = true := by decide +kernel
theorem slawChunk_2218 : slawChunk 2218 = true := by decide +kernel
theorem slawChunk_2219 : slawChunk 2219 = true := by decide +kernel
theorem slawChunk_2220 : slawChunk 2220 = true := by decide +kernel
theorem slawChunk_2221 : slawChunk 2221 = true := by decide +kernel
theorem slawChunk_2222 : slawChunk 2222 = true := by decide +kernel
theorem slawChunk_2223 : slawChunk 2223 = true := by decide +kernel
theorem slawC_277 (k : Nat) (h1 : 2216 ≤ k) (h2 : k < 2224) : slawChunk k = true := by
  if e2216 : k = 2216 then subst e2216; exact slawChunk_2216 else
  if e2217 : k = 2217 then subst e2217; exact slawChunk_2217 else
  if e2218 : k = 2218 then subst e2218; exact slawChunk_2218 else
  if e2219 : k = 2219 then subst e2219; exact slawChunk_2219 else
  if e2220 : k = 2220 then subst e2220; exact slawChunk_2220 else
  if e2221 : k = 2221 then subst e2221; exact slawChunk_2221 else
  if e2222 : k = 2222 then subst e2222; exact slawChunk_2222 else
  if e2223 : k = 2223 then subst e2223; exact slawChunk_2223 else
  omega
end D2
