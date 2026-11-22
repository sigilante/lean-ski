import Ski.D2Base
import Ski.D2K.S121
/-! Generated.  S-law of D: chunks 976..983 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_976 : slawChunk 976 = true := by decide +kernel
theorem slawChunk_977 : slawChunk 977 = true := by decide +kernel
theorem slawChunk_978 : slawChunk 978 = true := by decide +kernel
theorem slawChunk_979 : slawChunk 979 = true := by decide +kernel
theorem slawChunk_980 : slawChunk 980 = true := by decide +kernel
theorem slawChunk_981 : slawChunk 981 = true := by decide +kernel
theorem slawChunk_982 : slawChunk 982 = true := by decide +kernel
theorem slawChunk_983 : slawChunk 983 = true := by decide +kernel
theorem slawC_122 (k : Nat) (h1 : 976 ≤ k) (h2 : k < 984) : slawChunk k = true := by
  if e976 : k = 976 then subst e976; exact slawChunk_976 else
  if e977 : k = 977 then subst e977; exact slawChunk_977 else
  if e978 : k = 978 then subst e978; exact slawChunk_978 else
  if e979 : k = 979 then subst e979; exact slawChunk_979 else
  if e980 : k = 980 then subst e980; exact slawChunk_980 else
  if e981 : k = 981 then subst e981; exact slawChunk_981 else
  if e982 : k = 982 then subst e982; exact slawChunk_982 else
  if e983 : k = 983 then subst e983; exact slawChunk_983 else
  omega
end D2
