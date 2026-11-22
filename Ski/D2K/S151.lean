import Ski.D2Base
import Ski.D2K.S150
/-! Generated.  S-law of D: chunks 1208..1215 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_1208 : slawChunk 1208 = true := by decide +kernel
theorem slawChunk_1209 : slawChunk 1209 = true := by decide +kernel
theorem slawChunk_1210 : slawChunk 1210 = true := by decide +kernel
theorem slawChunk_1211 : slawChunk 1211 = true := by decide +kernel
theorem slawChunk_1212 : slawChunk 1212 = true := by decide +kernel
theorem slawChunk_1213 : slawChunk 1213 = true := by decide +kernel
theorem slawChunk_1214 : slawChunk 1214 = true := by decide +kernel
theorem slawChunk_1215 : slawChunk 1215 = true := by decide +kernel
theorem slawC_151 (k : Nat) (h1 : 1208 ≤ k) (h2 : k < 1216) : slawChunk k = true := by
  if e1208 : k = 1208 then subst e1208; exact slawChunk_1208 else
  if e1209 : k = 1209 then subst e1209; exact slawChunk_1209 else
  if e1210 : k = 1210 then subst e1210; exact slawChunk_1210 else
  if e1211 : k = 1211 then subst e1211; exact slawChunk_1211 else
  if e1212 : k = 1212 then subst e1212; exact slawChunk_1212 else
  if e1213 : k = 1213 then subst e1213; exact slawChunk_1213 else
  if e1214 : k = 1214 then subst e1214; exact slawChunk_1214 else
  if e1215 : k = 1215 then subst e1215; exact slawChunk_1215 else
  omega
end D2
