import Ski.D2Base
import Ski.D2K.S78
/-! Generated.  S-law of D: chunks 632..639 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_632 : slawChunk 632 = true := by decide +kernel
theorem slawChunk_633 : slawChunk 633 = true := by decide +kernel
theorem slawChunk_634 : slawChunk 634 = true := by decide +kernel
theorem slawChunk_635 : slawChunk 635 = true := by decide +kernel
theorem slawChunk_636 : slawChunk 636 = true := by decide +kernel
theorem slawChunk_637 : slawChunk 637 = true := by decide +kernel
theorem slawChunk_638 : slawChunk 638 = true := by decide +kernel
theorem slawChunk_639 : slawChunk 639 = true := by decide +kernel
theorem slawC_79 (k : Nat) (h1 : 632 ≤ k) (h2 : k < 640) : slawChunk k = true := by
  if e632 : k = 632 then subst e632; exact slawChunk_632 else
  if e633 : k = 633 then subst e633; exact slawChunk_633 else
  if e634 : k = 634 then subst e634; exact slawChunk_634 else
  if e635 : k = 635 then subst e635; exact slawChunk_635 else
  if e636 : k = 636 then subst e636; exact slawChunk_636 else
  if e637 : k = 637 then subst e637; exact slawChunk_637 else
  if e638 : k = 638 then subst e638; exact slawChunk_638 else
  if e639 : k = 639 then subst e639; exact slawChunk_639 else
  omega
end D2
