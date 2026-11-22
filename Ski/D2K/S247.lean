import Ski.D2Base
import Ski.D2K.S246
/-! Generated.  S-law of D: chunks 1976..1983 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_1976 : slawChunk 1976 = true := by decide +kernel
theorem slawChunk_1977 : slawChunk 1977 = true := by decide +kernel
theorem slawChunk_1978 : slawChunk 1978 = true := by decide +kernel
theorem slawChunk_1979 : slawChunk 1979 = true := by decide +kernel
theorem slawChunk_1980 : slawChunk 1980 = true := by decide +kernel
theorem slawChunk_1981 : slawChunk 1981 = true := by decide +kernel
theorem slawChunk_1982 : slawChunk 1982 = true := by decide +kernel
theorem slawChunk_1983 : slawChunk 1983 = true := by decide +kernel
theorem slawC_247 (k : Nat) (h1 : 1976 ≤ k) (h2 : k < 1984) : slawChunk k = true := by
  if e1976 : k = 1976 then subst e1976; exact slawChunk_1976 else
  if e1977 : k = 1977 then subst e1977; exact slawChunk_1977 else
  if e1978 : k = 1978 then subst e1978; exact slawChunk_1978 else
  if e1979 : k = 1979 then subst e1979; exact slawChunk_1979 else
  if e1980 : k = 1980 then subst e1980; exact slawChunk_1980 else
  if e1981 : k = 1981 then subst e1981; exact slawChunk_1981 else
  if e1982 : k = 1982 then subst e1982; exact slawChunk_1982 else
  if e1983 : k = 1983 then subst e1983; exact slawChunk_1983 else
  omega
end D2
