import Ski.D2Base
import Ski.D2K.S125
/-! Generated.  S-law of D: chunks 1008..1015 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_1008 : slawChunk 1008 = true := by decide +kernel
theorem slawChunk_1009 : slawChunk 1009 = true := by decide +kernel
theorem slawChunk_1010 : slawChunk 1010 = true := by decide +kernel
theorem slawChunk_1011 : slawChunk 1011 = true := by decide +kernel
theorem slawChunk_1012 : slawChunk 1012 = true := by decide +kernel
theorem slawChunk_1013 : slawChunk 1013 = true := by decide +kernel
theorem slawChunk_1014 : slawChunk 1014 = true := by decide +kernel
theorem slawChunk_1015 : slawChunk 1015 = true := by decide +kernel
theorem slawC_126 (k : Nat) (h1 : 1008 ≤ k) (h2 : k < 1016) : slawChunk k = true := by
  if e1008 : k = 1008 then subst e1008; exact slawChunk_1008 else
  if e1009 : k = 1009 then subst e1009; exact slawChunk_1009 else
  if e1010 : k = 1010 then subst e1010; exact slawChunk_1010 else
  if e1011 : k = 1011 then subst e1011; exact slawChunk_1011 else
  if e1012 : k = 1012 then subst e1012; exact slawChunk_1012 else
  if e1013 : k = 1013 then subst e1013; exact slawChunk_1013 else
  if e1014 : k = 1014 then subst e1014; exact slawChunk_1014 else
  if e1015 : k = 1015 then subst e1015; exact slawChunk_1015 else
  omega
end D2
