import Ski.D2Base
import Ski.D2K.S87
/-! Generated.  S-law of D: chunks 704..711 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_704 : slawChunk 704 = true := by decide +kernel
theorem slawChunk_705 : slawChunk 705 = true := by decide +kernel
theorem slawChunk_706 : slawChunk 706 = true := by decide +kernel
theorem slawChunk_707 : slawChunk 707 = true := by decide +kernel
theorem slawChunk_708 : slawChunk 708 = true := by decide +kernel
theorem slawChunk_709 : slawChunk 709 = true := by decide +kernel
theorem slawChunk_710 : slawChunk 710 = true := by decide +kernel
theorem slawChunk_711 : slawChunk 711 = true := by decide +kernel
theorem slawC_88 (k : Nat) (h1 : 704 ≤ k) (h2 : k < 712) : slawChunk k = true := by
  if e704 : k = 704 then subst e704; exact slawChunk_704 else
  if e705 : k = 705 then subst e705; exact slawChunk_705 else
  if e706 : k = 706 then subst e706; exact slawChunk_706 else
  if e707 : k = 707 then subst e707; exact slawChunk_707 else
  if e708 : k = 708 then subst e708; exact slawChunk_708 else
  if e709 : k = 709 then subst e709; exact slawChunk_709 else
  if e710 : k = 710 then subst e710; exact slawChunk_710 else
  if e711 : k = 711 then subst e711; exact slawChunk_711 else
  omega
end D2
