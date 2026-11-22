import Ski.D2Base
import Ski.D2K.S172
/-! Generated.  S-law of D: chunks 1384..1391 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_1384 : slawChunk 1384 = true := by decide +kernel
theorem slawChunk_1385 : slawChunk 1385 = true := by decide +kernel
theorem slawChunk_1386 : slawChunk 1386 = true := by decide +kernel
theorem slawChunk_1387 : slawChunk 1387 = true := by decide +kernel
theorem slawChunk_1388 : slawChunk 1388 = true := by decide +kernel
theorem slawChunk_1389 : slawChunk 1389 = true := by decide +kernel
theorem slawChunk_1390 : slawChunk 1390 = true := by decide +kernel
theorem slawChunk_1391 : slawChunk 1391 = true := by decide +kernel
theorem slawC_173 (k : Nat) (h1 : 1384 ≤ k) (h2 : k < 1392) : slawChunk k = true := by
  if e1384 : k = 1384 then subst e1384; exact slawChunk_1384 else
  if e1385 : k = 1385 then subst e1385; exact slawChunk_1385 else
  if e1386 : k = 1386 then subst e1386; exact slawChunk_1386 else
  if e1387 : k = 1387 then subst e1387; exact slawChunk_1387 else
  if e1388 : k = 1388 then subst e1388; exact slawChunk_1388 else
  if e1389 : k = 1389 then subst e1389; exact slawChunk_1389 else
  if e1390 : k = 1390 then subst e1390; exact slawChunk_1390 else
  if e1391 : k = 1391 then subst e1391; exact slawChunk_1391 else
  omega
end D2
