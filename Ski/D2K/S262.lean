import Ski.D2Base
import Ski.D2K.S261
/-! Generated.  S-law of D: chunks 2096..2103 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_2096 : slawChunk 2096 = true := by decide +kernel
theorem slawChunk_2097 : slawChunk 2097 = true := by decide +kernel
theorem slawChunk_2098 : slawChunk 2098 = true := by decide +kernel
theorem slawChunk_2099 : slawChunk 2099 = true := by decide +kernel
theorem slawChunk_2100 : slawChunk 2100 = true := by decide +kernel
theorem slawChunk_2101 : slawChunk 2101 = true := by decide +kernel
theorem slawChunk_2102 : slawChunk 2102 = true := by decide +kernel
theorem slawChunk_2103 : slawChunk 2103 = true := by decide +kernel
theorem slawC_262 (k : Nat) (h1 : 2096 ≤ k) (h2 : k < 2104) : slawChunk k = true := by
  if e2096 : k = 2096 then subst e2096; exact slawChunk_2096 else
  if e2097 : k = 2097 then subst e2097; exact slawChunk_2097 else
  if e2098 : k = 2098 then subst e2098; exact slawChunk_2098 else
  if e2099 : k = 2099 then subst e2099; exact slawChunk_2099 else
  if e2100 : k = 2100 then subst e2100; exact slawChunk_2100 else
  if e2101 : k = 2101 then subst e2101; exact slawChunk_2101 else
  if e2102 : k = 2102 then subst e2102; exact slawChunk_2102 else
  if e2103 : k = 2103 then subst e2103; exact slawChunk_2103 else
  omega
end D2
