import Ski.D2Base
import Ski.D2K.S339
/-! Generated.  S-law of D: chunks 2720..2727 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_2720 : slawChunk 2720 = true := by decide +kernel
theorem slawChunk_2721 : slawChunk 2721 = true := by decide +kernel
theorem slawChunk_2722 : slawChunk 2722 = true := by decide +kernel
theorem slawChunk_2723 : slawChunk 2723 = true := by decide +kernel
theorem slawChunk_2724 : slawChunk 2724 = true := by decide +kernel
theorem slawChunk_2725 : slawChunk 2725 = true := by decide +kernel
theorem slawChunk_2726 : slawChunk 2726 = true := by decide +kernel
theorem slawChunk_2727 : slawChunk 2727 = true := by decide +kernel
theorem slawC_340 (k : Nat) (h1 : 2720 ≤ k) (h2 : k < 2728) : slawChunk k = true := by
  if e2720 : k = 2720 then subst e2720; exact slawChunk_2720 else
  if e2721 : k = 2721 then subst e2721; exact slawChunk_2721 else
  if e2722 : k = 2722 then subst e2722; exact slawChunk_2722 else
  if e2723 : k = 2723 then subst e2723; exact slawChunk_2723 else
  if e2724 : k = 2724 then subst e2724; exact slawChunk_2724 else
  if e2725 : k = 2725 then subst e2725; exact slawChunk_2725 else
  if e2726 : k = 2726 then subst e2726; exact slawChunk_2726 else
  if e2727 : k = 2727 then subst e2727; exact slawChunk_2727 else
  omega
end D2
