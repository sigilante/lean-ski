import Ski.D2Base
import Ski.D2K.S275
/-! Generated.  S-law of D: chunks 2208..2215 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_2208 : slawChunk 2208 = true := by decide +kernel
theorem slawChunk_2209 : slawChunk 2209 = true := by decide +kernel
theorem slawChunk_2210 : slawChunk 2210 = true := by decide +kernel
theorem slawChunk_2211 : slawChunk 2211 = true := by decide +kernel
theorem slawChunk_2212 : slawChunk 2212 = true := by decide +kernel
theorem slawChunk_2213 : slawChunk 2213 = true := by decide +kernel
theorem slawChunk_2214 : slawChunk 2214 = true := by decide +kernel
theorem slawChunk_2215 : slawChunk 2215 = true := by decide +kernel
theorem slawC_276 (k : Nat) (h1 : 2208 ≤ k) (h2 : k < 2216) : slawChunk k = true := by
  if e2208 : k = 2208 then subst e2208; exact slawChunk_2208 else
  if e2209 : k = 2209 then subst e2209; exact slawChunk_2209 else
  if e2210 : k = 2210 then subst e2210; exact slawChunk_2210 else
  if e2211 : k = 2211 then subst e2211; exact slawChunk_2211 else
  if e2212 : k = 2212 then subst e2212; exact slawChunk_2212 else
  if e2213 : k = 2213 then subst e2213; exact slawChunk_2213 else
  if e2214 : k = 2214 then subst e2214; exact slawChunk_2214 else
  if e2215 : k = 2215 then subst e2215; exact slawChunk_2215 else
  omega
end D2
