import Ski.D2Base
import Ski.D2K.S67
/-! Generated.  S-law of D: chunks 544..551 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_544 : slawChunk 544 = true := by decide +kernel
theorem slawChunk_545 : slawChunk 545 = true := by decide +kernel
theorem slawChunk_546 : slawChunk 546 = true := by decide +kernel
theorem slawChunk_547 : slawChunk 547 = true := by decide +kernel
theorem slawChunk_548 : slawChunk 548 = true := by decide +kernel
theorem slawChunk_549 : slawChunk 549 = true := by decide +kernel
theorem slawChunk_550 : slawChunk 550 = true := by decide +kernel
theorem slawChunk_551 : slawChunk 551 = true := by decide +kernel
theorem slawC_68 (k : Nat) (h1 : 544 ≤ k) (h2 : k < 552) : slawChunk k = true := by
  if e544 : k = 544 then subst e544; exact slawChunk_544 else
  if e545 : k = 545 then subst e545; exact slawChunk_545 else
  if e546 : k = 546 then subst e546; exact slawChunk_546 else
  if e547 : k = 547 then subst e547; exact slawChunk_547 else
  if e548 : k = 548 then subst e548; exact slawChunk_548 else
  if e549 : k = 549 then subst e549; exact slawChunk_549 else
  if e550 : k = 550 then subst e550; exact slawChunk_550 else
  if e551 : k = 551 then subst e551; exact slawChunk_551 else
  omega
end D2
