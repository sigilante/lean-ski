import Ski.D2Base
import Ski.D2K.S265
/-! Generated.  S-law of D: chunks 2128..2135 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_2128 : slawChunk 2128 = true := by decide +kernel
theorem slawChunk_2129 : slawChunk 2129 = true := by decide +kernel
theorem slawChunk_2130 : slawChunk 2130 = true := by decide +kernel
theorem slawChunk_2131 : slawChunk 2131 = true := by decide +kernel
theorem slawChunk_2132 : slawChunk 2132 = true := by decide +kernel
theorem slawChunk_2133 : slawChunk 2133 = true := by decide +kernel
theorem slawChunk_2134 : slawChunk 2134 = true := by decide +kernel
theorem slawChunk_2135 : slawChunk 2135 = true := by decide +kernel
theorem slawC_266 (k : Nat) (h1 : 2128 ≤ k) (h2 : k < 2136) : slawChunk k = true := by
  if e2128 : k = 2128 then subst e2128; exact slawChunk_2128 else
  if e2129 : k = 2129 then subst e2129; exact slawChunk_2129 else
  if e2130 : k = 2130 then subst e2130; exact slawChunk_2130 else
  if e2131 : k = 2131 then subst e2131; exact slawChunk_2131 else
  if e2132 : k = 2132 then subst e2132; exact slawChunk_2132 else
  if e2133 : k = 2133 then subst e2133; exact slawChunk_2133 else
  if e2134 : k = 2134 then subst e2134; exact slawChunk_2134 else
  if e2135 : k = 2135 then subst e2135; exact slawChunk_2135 else
  omega
end D2
