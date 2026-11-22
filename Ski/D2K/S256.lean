import Ski.D2Base
import Ski.D2K.S255
/-! Generated.  S-law of D: chunks 2048..2055 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_2048 : slawChunk 2048 = true := by decide +kernel
theorem slawChunk_2049 : slawChunk 2049 = true := by decide +kernel
theorem slawChunk_2050 : slawChunk 2050 = true := by decide +kernel
theorem slawChunk_2051 : slawChunk 2051 = true := by decide +kernel
theorem slawChunk_2052 : slawChunk 2052 = true := by decide +kernel
theorem slawChunk_2053 : slawChunk 2053 = true := by decide +kernel
theorem slawChunk_2054 : slawChunk 2054 = true := by decide +kernel
theorem slawChunk_2055 : slawChunk 2055 = true := by decide +kernel
theorem slawC_256 (k : Nat) (h1 : 2048 ≤ k) (h2 : k < 2056) : slawChunk k = true := by
  if e2048 : k = 2048 then subst e2048; exact slawChunk_2048 else
  if e2049 : k = 2049 then subst e2049; exact slawChunk_2049 else
  if e2050 : k = 2050 then subst e2050; exact slawChunk_2050 else
  if e2051 : k = 2051 then subst e2051; exact slawChunk_2051 else
  if e2052 : k = 2052 then subst e2052; exact slawChunk_2052 else
  if e2053 : k = 2053 then subst e2053; exact slawChunk_2053 else
  if e2054 : k = 2054 then subst e2054; exact slawChunk_2054 else
  if e2055 : k = 2055 then subst e2055; exact slawChunk_2055 else
  omega
end D2
