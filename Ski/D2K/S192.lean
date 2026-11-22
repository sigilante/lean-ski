import Ski.D2Base
import Ski.D2K.S191
/-! Generated.  S-law of D: chunks 1536..1543 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_1536 : slawChunk 1536 = true := by decide +kernel
theorem slawChunk_1537 : slawChunk 1537 = true := by decide +kernel
theorem slawChunk_1538 : slawChunk 1538 = true := by decide +kernel
theorem slawChunk_1539 : slawChunk 1539 = true := by decide +kernel
theorem slawChunk_1540 : slawChunk 1540 = true := by decide +kernel
theorem slawChunk_1541 : slawChunk 1541 = true := by decide +kernel
theorem slawChunk_1542 : slawChunk 1542 = true := by decide +kernel
theorem slawChunk_1543 : slawChunk 1543 = true := by decide +kernel
theorem slawC_192 (k : Nat) (h1 : 1536 ≤ k) (h2 : k < 1544) : slawChunk k = true := by
  if e1536 : k = 1536 then subst e1536; exact slawChunk_1536 else
  if e1537 : k = 1537 then subst e1537; exact slawChunk_1537 else
  if e1538 : k = 1538 then subst e1538; exact slawChunk_1538 else
  if e1539 : k = 1539 then subst e1539; exact slawChunk_1539 else
  if e1540 : k = 1540 then subst e1540; exact slawChunk_1540 else
  if e1541 : k = 1541 then subst e1541; exact slawChunk_1541 else
  if e1542 : k = 1542 then subst e1542; exact slawChunk_1542 else
  if e1543 : k = 1543 then subst e1543; exact slawChunk_1543 else
  omega
end D2
