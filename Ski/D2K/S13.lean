import Ski.D2Base
import Ski.D2K.S12
/-! Generated.  S-law of D: chunks 104..111 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_104 : slawChunk 104 = true := by decide +kernel
theorem slawChunk_105 : slawChunk 105 = true := by decide +kernel
theorem slawChunk_106 : slawChunk 106 = true := by decide +kernel
theorem slawChunk_107 : slawChunk 107 = true := by decide +kernel
theorem slawChunk_108 : slawChunk 108 = true := by decide +kernel
theorem slawChunk_109 : slawChunk 109 = true := by decide +kernel
theorem slawChunk_110 : slawChunk 110 = true := by decide +kernel
theorem slawChunk_111 : slawChunk 111 = true := by decide +kernel
theorem slawC_13 (k : Nat) (h1 : 104 ≤ k) (h2 : k < 112) : slawChunk k = true := by
  if e104 : k = 104 then subst e104; exact slawChunk_104 else
  if e105 : k = 105 then subst e105; exact slawChunk_105 else
  if e106 : k = 106 then subst e106; exact slawChunk_106 else
  if e107 : k = 107 then subst e107; exact slawChunk_107 else
  if e108 : k = 108 then subst e108; exact slawChunk_108 else
  if e109 : k = 109 then subst e109; exact slawChunk_109 else
  if e110 : k = 110 then subst e110; exact slawChunk_110 else
  if e111 : k = 111 then subst e111; exact slawChunk_111 else
  omega
end D2
