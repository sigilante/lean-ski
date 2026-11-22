import Ski.D2Base
import Ski.D2K.S152
/-! Generated.  S-law of D: chunks 1224..1231 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_1224 : slawChunk 1224 = true := by decide +kernel
theorem slawChunk_1225 : slawChunk 1225 = true := by decide +kernel
theorem slawChunk_1226 : slawChunk 1226 = true := by decide +kernel
theorem slawChunk_1227 : slawChunk 1227 = true := by decide +kernel
theorem slawChunk_1228 : slawChunk 1228 = true := by decide +kernel
theorem slawChunk_1229 : slawChunk 1229 = true := by decide +kernel
theorem slawChunk_1230 : slawChunk 1230 = true := by decide +kernel
theorem slawChunk_1231 : slawChunk 1231 = true := by decide +kernel
theorem slawC_153 (k : Nat) (h1 : 1224 ≤ k) (h2 : k < 1232) : slawChunk k = true := by
  if e1224 : k = 1224 then subst e1224; exact slawChunk_1224 else
  if e1225 : k = 1225 then subst e1225; exact slawChunk_1225 else
  if e1226 : k = 1226 then subst e1226; exact slawChunk_1226 else
  if e1227 : k = 1227 then subst e1227; exact slawChunk_1227 else
  if e1228 : k = 1228 then subst e1228; exact slawChunk_1228 else
  if e1229 : k = 1229 then subst e1229; exact slawChunk_1229 else
  if e1230 : k = 1230 then subst e1230; exact slawChunk_1230 else
  if e1231 : k = 1231 then subst e1231; exact slawChunk_1231 else
  omega
end D2
