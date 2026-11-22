import Ski.D2Base
import Ski.D2K.S120
/-! Generated.  S-law of D: chunks 968..975 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_968 : slawChunk 968 = true := by decide +kernel
theorem slawChunk_969 : slawChunk 969 = true := by decide +kernel
theorem slawChunk_970 : slawChunk 970 = true := by decide +kernel
theorem slawChunk_971 : slawChunk 971 = true := by decide +kernel
theorem slawChunk_972 : slawChunk 972 = true := by decide +kernel
theorem slawChunk_973 : slawChunk 973 = true := by decide +kernel
theorem slawChunk_974 : slawChunk 974 = true := by decide +kernel
theorem slawChunk_975 : slawChunk 975 = true := by decide +kernel
theorem slawC_121 (k : Nat) (h1 : 968 ≤ k) (h2 : k < 976) : slawChunk k = true := by
  if e968 : k = 968 then subst e968; exact slawChunk_968 else
  if e969 : k = 969 then subst e969; exact slawChunk_969 else
  if e970 : k = 970 then subst e970; exact slawChunk_970 else
  if e971 : k = 971 then subst e971; exact slawChunk_971 else
  if e972 : k = 972 then subst e972; exact slawChunk_972 else
  if e973 : k = 973 then subst e973; exact slawChunk_973 else
  if e974 : k = 974 then subst e974; exact slawChunk_974 else
  if e975 : k = 975 then subst e975; exact slawChunk_975 else
  omega
end D2
