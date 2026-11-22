import Ski.D2Base
import Ski.D2K.S153
/-! Generated.  S-law of D: chunks 1232..1239 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_1232 : slawChunk 1232 = true := by decide +kernel
theorem slawChunk_1233 : slawChunk 1233 = true := by decide +kernel
theorem slawChunk_1234 : slawChunk 1234 = true := by decide +kernel
theorem slawChunk_1235 : slawChunk 1235 = true := by decide +kernel
theorem slawChunk_1236 : slawChunk 1236 = true := by decide +kernel
theorem slawChunk_1237 : slawChunk 1237 = true := by decide +kernel
theorem slawChunk_1238 : slawChunk 1238 = true := by decide +kernel
theorem slawChunk_1239 : slawChunk 1239 = true := by decide +kernel
theorem slawC_154 (k : Nat) (h1 : 1232 ≤ k) (h2 : k < 1240) : slawChunk k = true := by
  if e1232 : k = 1232 then subst e1232; exact slawChunk_1232 else
  if e1233 : k = 1233 then subst e1233; exact slawChunk_1233 else
  if e1234 : k = 1234 then subst e1234; exact slawChunk_1234 else
  if e1235 : k = 1235 then subst e1235; exact slawChunk_1235 else
  if e1236 : k = 1236 then subst e1236; exact slawChunk_1236 else
  if e1237 : k = 1237 then subst e1237; exact slawChunk_1237 else
  if e1238 : k = 1238 then subst e1238; exact slawChunk_1238 else
  if e1239 : k = 1239 then subst e1239; exact slawChunk_1239 else
  omega
end D2
