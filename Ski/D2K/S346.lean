import Ski.D2Base
import Ski.D2K.S345
/-! Generated.  S-law of D: chunks 2768..2775 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_2768 : slawChunk 2768 = true := by decide +kernel
theorem slawChunk_2769 : slawChunk 2769 = true := by decide +kernel
theorem slawChunk_2770 : slawChunk 2770 = true := by decide +kernel
theorem slawChunk_2771 : slawChunk 2771 = true := by decide +kernel
theorem slawChunk_2772 : slawChunk 2772 = true := by decide +kernel
theorem slawChunk_2773 : slawChunk 2773 = true := by decide +kernel
theorem slawChunk_2774 : slawChunk 2774 = true := by decide +kernel
theorem slawChunk_2775 : slawChunk 2775 = true := by decide +kernel
theorem slawC_346 (k : Nat) (h1 : 2768 ≤ k) (h2 : k < 2776) : slawChunk k = true := by
  if e2768 : k = 2768 then subst e2768; exact slawChunk_2768 else
  if e2769 : k = 2769 then subst e2769; exact slawChunk_2769 else
  if e2770 : k = 2770 then subst e2770; exact slawChunk_2770 else
  if e2771 : k = 2771 then subst e2771; exact slawChunk_2771 else
  if e2772 : k = 2772 then subst e2772; exact slawChunk_2772 else
  if e2773 : k = 2773 then subst e2773; exact slawChunk_2773 else
  if e2774 : k = 2774 then subst e2774; exact slawChunk_2774 else
  if e2775 : k = 2775 then subst e2775; exact slawChunk_2775 else
  omega
end D2
