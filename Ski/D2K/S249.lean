import Ski.D2Base
import Ski.D2K.S248
/-! Generated.  S-law of D: chunks 1992..1999 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_1992 : slawChunk 1992 = true := by decide +kernel
theorem slawChunk_1993 : slawChunk 1993 = true := by decide +kernel
theorem slawChunk_1994 : slawChunk 1994 = true := by decide +kernel
theorem slawChunk_1995 : slawChunk 1995 = true := by decide +kernel
theorem slawChunk_1996 : slawChunk 1996 = true := by decide +kernel
theorem slawChunk_1997 : slawChunk 1997 = true := by decide +kernel
theorem slawChunk_1998 : slawChunk 1998 = true := by decide +kernel
theorem slawChunk_1999 : slawChunk 1999 = true := by decide +kernel
theorem slawC_249 (k : Nat) (h1 : 1992 ≤ k) (h2 : k < 2000) : slawChunk k = true := by
  if e1992 : k = 1992 then subst e1992; exact slawChunk_1992 else
  if e1993 : k = 1993 then subst e1993; exact slawChunk_1993 else
  if e1994 : k = 1994 then subst e1994; exact slawChunk_1994 else
  if e1995 : k = 1995 then subst e1995; exact slawChunk_1995 else
  if e1996 : k = 1996 then subst e1996; exact slawChunk_1996 else
  if e1997 : k = 1997 then subst e1997; exact slawChunk_1997 else
  if e1998 : k = 1998 then subst e1998; exact slawChunk_1998 else
  if e1999 : k = 1999 then subst e1999; exact slawChunk_1999 else
  omega
end D2
