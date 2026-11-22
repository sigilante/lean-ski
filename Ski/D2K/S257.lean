import Ski.D2Base
import Ski.D2K.S256
/-! Generated.  S-law of D: chunks 2056..2063 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_2056 : slawChunk 2056 = true := by decide +kernel
theorem slawChunk_2057 : slawChunk 2057 = true := by decide +kernel
theorem slawChunk_2058 : slawChunk 2058 = true := by decide +kernel
theorem slawChunk_2059 : slawChunk 2059 = true := by decide +kernel
theorem slawChunk_2060 : slawChunk 2060 = true := by decide +kernel
theorem slawChunk_2061 : slawChunk 2061 = true := by decide +kernel
theorem slawChunk_2062 : slawChunk 2062 = true := by decide +kernel
theorem slawChunk_2063 : slawChunk 2063 = true := by decide +kernel
theorem slawC_257 (k : Nat) (h1 : 2056 ≤ k) (h2 : k < 2064) : slawChunk k = true := by
  if e2056 : k = 2056 then subst e2056; exact slawChunk_2056 else
  if e2057 : k = 2057 then subst e2057; exact slawChunk_2057 else
  if e2058 : k = 2058 then subst e2058; exact slawChunk_2058 else
  if e2059 : k = 2059 then subst e2059; exact slawChunk_2059 else
  if e2060 : k = 2060 then subst e2060; exact slawChunk_2060 else
  if e2061 : k = 2061 then subst e2061; exact slawChunk_2061 else
  if e2062 : k = 2062 then subst e2062; exact slawChunk_2062 else
  if e2063 : k = 2063 then subst e2063; exact slawChunk_2063 else
  omega
end D2
