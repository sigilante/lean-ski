import Ski.D2Base
import Ski.D2K.S122
/-! Generated.  S-law of D: chunks 984..991 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_984 : slawChunk 984 = true := by decide +kernel
theorem slawChunk_985 : slawChunk 985 = true := by decide +kernel
theorem slawChunk_986 : slawChunk 986 = true := by decide +kernel
theorem slawChunk_987 : slawChunk 987 = true := by decide +kernel
theorem slawChunk_988 : slawChunk 988 = true := by decide +kernel
theorem slawChunk_989 : slawChunk 989 = true := by decide +kernel
theorem slawChunk_990 : slawChunk 990 = true := by decide +kernel
theorem slawChunk_991 : slawChunk 991 = true := by decide +kernel
theorem slawC_123 (k : Nat) (h1 : 984 ≤ k) (h2 : k < 992) : slawChunk k = true := by
  if e984 : k = 984 then subst e984; exact slawChunk_984 else
  if e985 : k = 985 then subst e985; exact slawChunk_985 else
  if e986 : k = 986 then subst e986; exact slawChunk_986 else
  if e987 : k = 987 then subst e987; exact slawChunk_987 else
  if e988 : k = 988 then subst e988; exact slawChunk_988 else
  if e989 : k = 989 then subst e989; exact slawChunk_989 else
  if e990 : k = 990 then subst e990; exact slawChunk_990 else
  if e991 : k = 991 then subst e991; exact slawChunk_991 else
  omega
end D2
