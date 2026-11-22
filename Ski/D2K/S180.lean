import Ski.D2Base
import Ski.D2K.S179
/-! Generated.  S-law of D: chunks 1440..1447 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_1440 : slawChunk 1440 = true := by decide +kernel
theorem slawChunk_1441 : slawChunk 1441 = true := by decide +kernel
theorem slawChunk_1442 : slawChunk 1442 = true := by decide +kernel
theorem slawChunk_1443 : slawChunk 1443 = true := by decide +kernel
theorem slawChunk_1444 : slawChunk 1444 = true := by decide +kernel
theorem slawChunk_1445 : slawChunk 1445 = true := by decide +kernel
theorem slawChunk_1446 : slawChunk 1446 = true := by decide +kernel
theorem slawChunk_1447 : slawChunk 1447 = true := by decide +kernel
theorem slawC_180 (k : Nat) (h1 : 1440 ≤ k) (h2 : k < 1448) : slawChunk k = true := by
  if e1440 : k = 1440 then subst e1440; exact slawChunk_1440 else
  if e1441 : k = 1441 then subst e1441; exact slawChunk_1441 else
  if e1442 : k = 1442 then subst e1442; exact slawChunk_1442 else
  if e1443 : k = 1443 then subst e1443; exact slawChunk_1443 else
  if e1444 : k = 1444 then subst e1444; exact slawChunk_1444 else
  if e1445 : k = 1445 then subst e1445; exact slawChunk_1445 else
  if e1446 : k = 1446 then subst e1446; exact slawChunk_1446 else
  if e1447 : k = 1447 then subst e1447; exact slawChunk_1447 else
  omega
end D2
