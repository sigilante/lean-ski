import Ski.D2Base
import Ski.D2K.S245
/-! Generated.  S-law of D: chunks 1968..1975 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_1968 : slawChunk 1968 = true := by decide +kernel
theorem slawChunk_1969 : slawChunk 1969 = true := by decide +kernel
theorem slawChunk_1970 : slawChunk 1970 = true := by decide +kernel
theorem slawChunk_1971 : slawChunk 1971 = true := by decide +kernel
theorem slawChunk_1972 : slawChunk 1972 = true := by decide +kernel
theorem slawChunk_1973 : slawChunk 1973 = true := by decide +kernel
theorem slawChunk_1974 : slawChunk 1974 = true := by decide +kernel
theorem slawChunk_1975 : slawChunk 1975 = true := by decide +kernel
theorem slawC_246 (k : Nat) (h1 : 1968 ≤ k) (h2 : k < 1976) : slawChunk k = true := by
  if e1968 : k = 1968 then subst e1968; exact slawChunk_1968 else
  if e1969 : k = 1969 then subst e1969; exact slawChunk_1969 else
  if e1970 : k = 1970 then subst e1970; exact slawChunk_1970 else
  if e1971 : k = 1971 then subst e1971; exact slawChunk_1971 else
  if e1972 : k = 1972 then subst e1972; exact slawChunk_1972 else
  if e1973 : k = 1973 then subst e1973; exact slawChunk_1973 else
  if e1974 : k = 1974 then subst e1974; exact slawChunk_1974 else
  if e1975 : k = 1975 then subst e1975; exact slawChunk_1975 else
  omega
end D2
