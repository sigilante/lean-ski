import Ski.D2Base
import Ski.D2K.S274
/-! Generated.  S-law of D: chunks 2200..2207 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_2200 : slawChunk 2200 = true := by decide +kernel
theorem slawChunk_2201 : slawChunk 2201 = true := by decide +kernel
theorem slawChunk_2202 : slawChunk 2202 = true := by decide +kernel
theorem slawChunk_2203 : slawChunk 2203 = true := by decide +kernel
theorem slawChunk_2204 : slawChunk 2204 = true := by decide +kernel
theorem slawChunk_2205 : slawChunk 2205 = true := by decide +kernel
theorem slawChunk_2206 : slawChunk 2206 = true := by decide +kernel
theorem slawChunk_2207 : slawChunk 2207 = true := by decide +kernel
theorem slawC_275 (k : Nat) (h1 : 2200 ≤ k) (h2 : k < 2208) : slawChunk k = true := by
  if e2200 : k = 2200 then subst e2200; exact slawChunk_2200 else
  if e2201 : k = 2201 then subst e2201; exact slawChunk_2201 else
  if e2202 : k = 2202 then subst e2202; exact slawChunk_2202 else
  if e2203 : k = 2203 then subst e2203; exact slawChunk_2203 else
  if e2204 : k = 2204 then subst e2204; exact slawChunk_2204 else
  if e2205 : k = 2205 then subst e2205; exact slawChunk_2205 else
  if e2206 : k = 2206 then subst e2206; exact slawChunk_2206 else
  if e2207 : k = 2207 then subst e2207; exact slawChunk_2207 else
  omega
end D2
