import Ski.D2Base
import Ski.D2K.S70
/-! Generated.  S-law of D: chunks 568..575 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_568 : slawChunk 568 = true := by decide +kernel
theorem slawChunk_569 : slawChunk 569 = true := by decide +kernel
theorem slawChunk_570 : slawChunk 570 = true := by decide +kernel
theorem slawChunk_571 : slawChunk 571 = true := by decide +kernel
theorem slawChunk_572 : slawChunk 572 = true := by decide +kernel
theorem slawChunk_573 : slawChunk 573 = true := by decide +kernel
theorem slawChunk_574 : slawChunk 574 = true := by decide +kernel
theorem slawChunk_575 : slawChunk 575 = true := by decide +kernel
theorem slawC_71 (k : Nat) (h1 : 568 ≤ k) (h2 : k < 576) : slawChunk k = true := by
  if e568 : k = 568 then subst e568; exact slawChunk_568 else
  if e569 : k = 569 then subst e569; exact slawChunk_569 else
  if e570 : k = 570 then subst e570; exact slawChunk_570 else
  if e571 : k = 571 then subst e571; exact slawChunk_571 else
  if e572 : k = 572 then subst e572; exact slawChunk_572 else
  if e573 : k = 573 then subst e573; exact slawChunk_573 else
  if e574 : k = 574 then subst e574; exact slawChunk_574 else
  if e575 : k = 575 then subst e575; exact slawChunk_575 else
  omega
end D2
