import Ski.D2Base
import Ski.D2K.S264
/-! Generated.  S-law of D: chunks 2120..2127 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_2120 : slawChunk 2120 = true := by decide +kernel
theorem slawChunk_2121 : slawChunk 2121 = true := by decide +kernel
theorem slawChunk_2122 : slawChunk 2122 = true := by decide +kernel
theorem slawChunk_2123 : slawChunk 2123 = true := by decide +kernel
theorem slawChunk_2124 : slawChunk 2124 = true := by decide +kernel
theorem slawChunk_2125 : slawChunk 2125 = true := by decide +kernel
theorem slawChunk_2126 : slawChunk 2126 = true := by decide +kernel
theorem slawChunk_2127 : slawChunk 2127 = true := by decide +kernel
theorem slawC_265 (k : Nat) (h1 : 2120 ≤ k) (h2 : k < 2128) : slawChunk k = true := by
  if e2120 : k = 2120 then subst e2120; exact slawChunk_2120 else
  if e2121 : k = 2121 then subst e2121; exact slawChunk_2121 else
  if e2122 : k = 2122 then subst e2122; exact slawChunk_2122 else
  if e2123 : k = 2123 then subst e2123; exact slawChunk_2123 else
  if e2124 : k = 2124 then subst e2124; exact slawChunk_2124 else
  if e2125 : k = 2125 then subst e2125; exact slawChunk_2125 else
  if e2126 : k = 2126 then subst e2126; exact slawChunk_2126 else
  if e2127 : k = 2127 then subst e2127; exact slawChunk_2127 else
  omega
end D2
