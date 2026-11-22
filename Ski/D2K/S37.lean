import Ski.D2Base
import Ski.D2K.S36
/-! Generated.  S-law of D: chunks 296..303 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_296 : slawChunk 296 = true := by decide +kernel
theorem slawChunk_297 : slawChunk 297 = true := by decide +kernel
theorem slawChunk_298 : slawChunk 298 = true := by decide +kernel
theorem slawChunk_299 : slawChunk 299 = true := by decide +kernel
theorem slawChunk_300 : slawChunk 300 = true := by decide +kernel
theorem slawChunk_301 : slawChunk 301 = true := by decide +kernel
theorem slawChunk_302 : slawChunk 302 = true := by decide +kernel
theorem slawChunk_303 : slawChunk 303 = true := by decide +kernel
theorem slawC_37 (k : Nat) (h1 : 296 ≤ k) (h2 : k < 304) : slawChunk k = true := by
  if e296 : k = 296 then subst e296; exact slawChunk_296 else
  if e297 : k = 297 then subst e297; exact slawChunk_297 else
  if e298 : k = 298 then subst e298; exact slawChunk_298 else
  if e299 : k = 299 then subst e299; exact slawChunk_299 else
  if e300 : k = 300 then subst e300; exact slawChunk_300 else
  if e301 : k = 301 then subst e301; exact slawChunk_301 else
  if e302 : k = 302 then subst e302; exact slawChunk_302 else
  if e303 : k = 303 then subst e303; exact slawChunk_303 else
  omega
end D2
