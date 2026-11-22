import Ski.D2Base
import Ski.D2K.S320
/-! Generated.  S-law of D: chunks 2568..2575 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_2568 : slawChunk 2568 = true := by decide +kernel
theorem slawChunk_2569 : slawChunk 2569 = true := by decide +kernel
theorem slawChunk_2570 : slawChunk 2570 = true := by decide +kernel
theorem slawChunk_2571 : slawChunk 2571 = true := by decide +kernel
theorem slawChunk_2572 : slawChunk 2572 = true := by decide +kernel
theorem slawChunk_2573 : slawChunk 2573 = true := by decide +kernel
theorem slawChunk_2574 : slawChunk 2574 = true := by decide +kernel
theorem slawChunk_2575 : slawChunk 2575 = true := by decide +kernel
theorem slawC_321 (k : Nat) (h1 : 2568 ≤ k) (h2 : k < 2576) : slawChunk k = true := by
  if e2568 : k = 2568 then subst e2568; exact slawChunk_2568 else
  if e2569 : k = 2569 then subst e2569; exact slawChunk_2569 else
  if e2570 : k = 2570 then subst e2570; exact slawChunk_2570 else
  if e2571 : k = 2571 then subst e2571; exact slawChunk_2571 else
  if e2572 : k = 2572 then subst e2572; exact slawChunk_2572 else
  if e2573 : k = 2573 then subst e2573; exact slawChunk_2573 else
  if e2574 : k = 2574 then subst e2574; exact slawChunk_2574 else
  if e2575 : k = 2575 then subst e2575; exact slawChunk_2575 else
  omega
end D2
