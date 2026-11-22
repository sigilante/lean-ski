import Ski.D2Base
import Ski.D2K.S247
/-! Generated.  S-law of D: chunks 1984..1991 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_1984 : slawChunk 1984 = true := by decide +kernel
theorem slawChunk_1985 : slawChunk 1985 = true := by decide +kernel
theorem slawChunk_1986 : slawChunk 1986 = true := by decide +kernel
theorem slawChunk_1987 : slawChunk 1987 = true := by decide +kernel
theorem slawChunk_1988 : slawChunk 1988 = true := by decide +kernel
theorem slawChunk_1989 : slawChunk 1989 = true := by decide +kernel
theorem slawChunk_1990 : slawChunk 1990 = true := by decide +kernel
theorem slawChunk_1991 : slawChunk 1991 = true := by decide +kernel
theorem slawC_248 (k : Nat) (h1 : 1984 ≤ k) (h2 : k < 1992) : slawChunk k = true := by
  if e1984 : k = 1984 then subst e1984; exact slawChunk_1984 else
  if e1985 : k = 1985 then subst e1985; exact slawChunk_1985 else
  if e1986 : k = 1986 then subst e1986; exact slawChunk_1986 else
  if e1987 : k = 1987 then subst e1987; exact slawChunk_1987 else
  if e1988 : k = 1988 then subst e1988; exact slawChunk_1988 else
  if e1989 : k = 1989 then subst e1989; exact slawChunk_1989 else
  if e1990 : k = 1990 then subst e1990; exact slawChunk_1990 else
  if e1991 : k = 1991 then subst e1991; exact slawChunk_1991 else
  omega
end D2
