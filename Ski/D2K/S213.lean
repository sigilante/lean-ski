import Ski.D2Base
import Ski.D2K.S212
/-! Generated.  S-law of D: chunks 1704..1711 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_1704 : slawChunk 1704 = true := by decide +kernel
theorem slawChunk_1705 : slawChunk 1705 = true := by decide +kernel
theorem slawChunk_1706 : slawChunk 1706 = true := by decide +kernel
theorem slawChunk_1707 : slawChunk 1707 = true := by decide +kernel
theorem slawChunk_1708 : slawChunk 1708 = true := by decide +kernel
theorem slawChunk_1709 : slawChunk 1709 = true := by decide +kernel
theorem slawChunk_1710 : slawChunk 1710 = true := by decide +kernel
theorem slawChunk_1711 : slawChunk 1711 = true := by decide +kernel
theorem slawC_213 (k : Nat) (h1 : 1704 ≤ k) (h2 : k < 1712) : slawChunk k = true := by
  if e1704 : k = 1704 then subst e1704; exact slawChunk_1704 else
  if e1705 : k = 1705 then subst e1705; exact slawChunk_1705 else
  if e1706 : k = 1706 then subst e1706; exact slawChunk_1706 else
  if e1707 : k = 1707 then subst e1707; exact slawChunk_1707 else
  if e1708 : k = 1708 then subst e1708; exact slawChunk_1708 else
  if e1709 : k = 1709 then subst e1709; exact slawChunk_1709 else
  if e1710 : k = 1710 then subst e1710; exact slawChunk_1710 else
  if e1711 : k = 1711 then subst e1711; exact slawChunk_1711 else
  omega
end D2
