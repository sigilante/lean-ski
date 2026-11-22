import Ski.D2Base
import Ski.D2K.S89
/-! Generated.  S-law of D: chunks 720..727 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_720 : slawChunk 720 = true := by decide +kernel
theorem slawChunk_721 : slawChunk 721 = true := by decide +kernel
theorem slawChunk_722 : slawChunk 722 = true := by decide +kernel
theorem slawChunk_723 : slawChunk 723 = true := by decide +kernel
theorem slawChunk_724 : slawChunk 724 = true := by decide +kernel
theorem slawChunk_725 : slawChunk 725 = true := by decide +kernel
theorem slawChunk_726 : slawChunk 726 = true := by decide +kernel
theorem slawChunk_727 : slawChunk 727 = true := by decide +kernel
theorem slawC_90 (k : Nat) (h1 : 720 ≤ k) (h2 : k < 728) : slawChunk k = true := by
  if e720 : k = 720 then subst e720; exact slawChunk_720 else
  if e721 : k = 721 then subst e721; exact slawChunk_721 else
  if e722 : k = 722 then subst e722; exact slawChunk_722 else
  if e723 : k = 723 then subst e723; exact slawChunk_723 else
  if e724 : k = 724 then subst e724; exact slawChunk_724 else
  if e725 : k = 725 then subst e725; exact slawChunk_725 else
  if e726 : k = 726 then subst e726; exact slawChunk_726 else
  if e727 : k = 727 then subst e727; exact slawChunk_727 else
  omega
end D2
