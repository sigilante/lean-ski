import Ski.D2Base
import Ski.D2K.S329
/-! Generated.  S-law of D: chunks 2640..2647 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_2640 : slawChunk 2640 = true := by decide +kernel
theorem slawChunk_2641 : slawChunk 2641 = true := by decide +kernel
theorem slawChunk_2642 : slawChunk 2642 = true := by decide +kernel
theorem slawChunk_2643 : slawChunk 2643 = true := by decide +kernel
theorem slawChunk_2644 : slawChunk 2644 = true := by decide +kernel
theorem slawChunk_2645 : slawChunk 2645 = true := by decide +kernel
theorem slawChunk_2646 : slawChunk 2646 = true := by decide +kernel
theorem slawChunk_2647 : slawChunk 2647 = true := by decide +kernel
theorem slawC_330 (k : Nat) (h1 : 2640 ≤ k) (h2 : k < 2648) : slawChunk k = true := by
  if e2640 : k = 2640 then subst e2640; exact slawChunk_2640 else
  if e2641 : k = 2641 then subst e2641; exact slawChunk_2641 else
  if e2642 : k = 2642 then subst e2642; exact slawChunk_2642 else
  if e2643 : k = 2643 then subst e2643; exact slawChunk_2643 else
  if e2644 : k = 2644 then subst e2644; exact slawChunk_2644 else
  if e2645 : k = 2645 then subst e2645; exact slawChunk_2645 else
  if e2646 : k = 2646 then subst e2646; exact slawChunk_2646 else
  if e2647 : k = 2647 then subst e2647; exact slawChunk_2647 else
  omega
end D2
