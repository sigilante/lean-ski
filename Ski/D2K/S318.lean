import Ski.D2Base
import Ski.D2K.S317
/-! Generated.  S-law of D: chunks 2544..2551 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_2544 : slawChunk 2544 = true := by decide +kernel
theorem slawChunk_2545 : slawChunk 2545 = true := by decide +kernel
theorem slawChunk_2546 : slawChunk 2546 = true := by decide +kernel
theorem slawChunk_2547 : slawChunk 2547 = true := by decide +kernel
theorem slawChunk_2548 : slawChunk 2548 = true := by decide +kernel
theorem slawChunk_2549 : slawChunk 2549 = true := by decide +kernel
theorem slawChunk_2550 : slawChunk 2550 = true := by decide +kernel
theorem slawChunk_2551 : slawChunk 2551 = true := by decide +kernel
theorem slawC_318 (k : Nat) (h1 : 2544 ≤ k) (h2 : k < 2552) : slawChunk k = true := by
  if e2544 : k = 2544 then subst e2544; exact slawChunk_2544 else
  if e2545 : k = 2545 then subst e2545; exact slawChunk_2545 else
  if e2546 : k = 2546 then subst e2546; exact slawChunk_2546 else
  if e2547 : k = 2547 then subst e2547; exact slawChunk_2547 else
  if e2548 : k = 2548 then subst e2548; exact slawChunk_2548 else
  if e2549 : k = 2549 then subst e2549; exact slawChunk_2549 else
  if e2550 : k = 2550 then subst e2550; exact slawChunk_2550 else
  if e2551 : k = 2551 then subst e2551; exact slawChunk_2551 else
  omega
end D2
