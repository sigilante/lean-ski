import Ski.D2Base
import Ski.D2K.S79
/-! Generated.  S-law of D: chunks 640..647 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_640 : slawChunk 640 = true := by decide +kernel
theorem slawChunk_641 : slawChunk 641 = true := by decide +kernel
theorem slawChunk_642 : slawChunk 642 = true := by decide +kernel
theorem slawChunk_643 : slawChunk 643 = true := by decide +kernel
theorem slawChunk_644 : slawChunk 644 = true := by decide +kernel
theorem slawChunk_645 : slawChunk 645 = true := by decide +kernel
theorem slawChunk_646 : slawChunk 646 = true := by decide +kernel
theorem slawChunk_647 : slawChunk 647 = true := by decide +kernel
theorem slawC_80 (k : Nat) (h1 : 640 ≤ k) (h2 : k < 648) : slawChunk k = true := by
  if e640 : k = 640 then subst e640; exact slawChunk_640 else
  if e641 : k = 641 then subst e641; exact slawChunk_641 else
  if e642 : k = 642 then subst e642; exact slawChunk_642 else
  if e643 : k = 643 then subst e643; exact slawChunk_643 else
  if e644 : k = 644 then subst e644; exact slawChunk_644 else
  if e645 : k = 645 then subst e645; exact slawChunk_645 else
  if e646 : k = 646 then subst e646; exact slawChunk_646 else
  if e647 : k = 647 then subst e647; exact slawChunk_647 else
  omega
end D2
