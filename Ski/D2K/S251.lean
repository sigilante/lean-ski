import Ski.D2Base
import Ski.D2K.S250
/-! Generated.  S-law of D: chunks 2008..2015 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_2008 : slawChunk 2008 = true := by decide +kernel
theorem slawChunk_2009 : slawChunk 2009 = true := by decide +kernel
theorem slawChunk_2010 : slawChunk 2010 = true := by decide +kernel
theorem slawChunk_2011 : slawChunk 2011 = true := by decide +kernel
theorem slawChunk_2012 : slawChunk 2012 = true := by decide +kernel
theorem slawChunk_2013 : slawChunk 2013 = true := by decide +kernel
theorem slawChunk_2014 : slawChunk 2014 = true := by decide +kernel
theorem slawChunk_2015 : slawChunk 2015 = true := by decide +kernel
theorem slawC_251 (k : Nat) (h1 : 2008 ≤ k) (h2 : k < 2016) : slawChunk k = true := by
  if e2008 : k = 2008 then subst e2008; exact slawChunk_2008 else
  if e2009 : k = 2009 then subst e2009; exact slawChunk_2009 else
  if e2010 : k = 2010 then subst e2010; exact slawChunk_2010 else
  if e2011 : k = 2011 then subst e2011; exact slawChunk_2011 else
  if e2012 : k = 2012 then subst e2012; exact slawChunk_2012 else
  if e2013 : k = 2013 then subst e2013; exact slawChunk_2013 else
  if e2014 : k = 2014 then subst e2014; exact slawChunk_2014 else
  if e2015 : k = 2015 then subst e2015; exact slawChunk_2015 else
  omega
end D2
