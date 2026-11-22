import Ski.D2Base
import Ski.D2K.S336
/-! Generated.  S-law of D: chunks 2696..2703 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_2696 : slawChunk 2696 = true := by decide +kernel
theorem slawChunk_2697 : slawChunk 2697 = true := by decide +kernel
theorem slawChunk_2698 : slawChunk 2698 = true := by decide +kernel
theorem slawChunk_2699 : slawChunk 2699 = true := by decide +kernel
theorem slawChunk_2700 : slawChunk 2700 = true := by decide +kernel
theorem slawChunk_2701 : slawChunk 2701 = true := by decide +kernel
theorem slawChunk_2702 : slawChunk 2702 = true := by decide +kernel
theorem slawChunk_2703 : slawChunk 2703 = true := by decide +kernel
theorem slawC_337 (k : Nat) (h1 : 2696 ≤ k) (h2 : k < 2704) : slawChunk k = true := by
  if e2696 : k = 2696 then subst e2696; exact slawChunk_2696 else
  if e2697 : k = 2697 then subst e2697; exact slawChunk_2697 else
  if e2698 : k = 2698 then subst e2698; exact slawChunk_2698 else
  if e2699 : k = 2699 then subst e2699; exact slawChunk_2699 else
  if e2700 : k = 2700 then subst e2700; exact slawChunk_2700 else
  if e2701 : k = 2701 then subst e2701; exact slawChunk_2701 else
  if e2702 : k = 2702 then subst e2702; exact slawChunk_2702 else
  if e2703 : k = 2703 then subst e2703; exact slawChunk_2703 else
  omega
end D2
