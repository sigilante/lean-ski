import Ski.D2Base
import Ski.D2K.S249
/-! Generated.  S-law of D: chunks 2000..2007 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_2000 : slawChunk 2000 = true := by decide +kernel
theorem slawChunk_2001 : slawChunk 2001 = true := by decide +kernel
theorem slawChunk_2002 : slawChunk 2002 = true := by decide +kernel
theorem slawChunk_2003 : slawChunk 2003 = true := by decide +kernel
theorem slawChunk_2004 : slawChunk 2004 = true := by decide +kernel
theorem slawChunk_2005 : slawChunk 2005 = true := by decide +kernel
theorem slawChunk_2006 : slawChunk 2006 = true := by decide +kernel
theorem slawChunk_2007 : slawChunk 2007 = true := by decide +kernel
theorem slawC_250 (k : Nat) (h1 : 2000 ≤ k) (h2 : k < 2008) : slawChunk k = true := by
  if e2000 : k = 2000 then subst e2000; exact slawChunk_2000 else
  if e2001 : k = 2001 then subst e2001; exact slawChunk_2001 else
  if e2002 : k = 2002 then subst e2002; exact slawChunk_2002 else
  if e2003 : k = 2003 then subst e2003; exact slawChunk_2003 else
  if e2004 : k = 2004 then subst e2004; exact slawChunk_2004 else
  if e2005 : k = 2005 then subst e2005; exact slawChunk_2005 else
  if e2006 : k = 2006 then subst e2006; exact slawChunk_2006 else
  if e2007 : k = 2007 then subst e2007; exact slawChunk_2007 else
  omega
end D2
