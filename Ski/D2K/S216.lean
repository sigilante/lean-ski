import Ski.D2Base
import Ski.D2K.S215
/-! Generated.  S-law of D: chunks 1728..1735 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_1728 : slawChunk 1728 = true := by decide +kernel
theorem slawChunk_1729 : slawChunk 1729 = true := by decide +kernel
theorem slawChunk_1730 : slawChunk 1730 = true := by decide +kernel
theorem slawChunk_1731 : slawChunk 1731 = true := by decide +kernel
theorem slawChunk_1732 : slawChunk 1732 = true := by decide +kernel
theorem slawChunk_1733 : slawChunk 1733 = true := by decide +kernel
theorem slawChunk_1734 : slawChunk 1734 = true := by decide +kernel
theorem slawChunk_1735 : slawChunk 1735 = true := by decide +kernel
theorem slawC_216 (k : Nat) (h1 : 1728 ≤ k) (h2 : k < 1736) : slawChunk k = true := by
  if e1728 : k = 1728 then subst e1728; exact slawChunk_1728 else
  if e1729 : k = 1729 then subst e1729; exact slawChunk_1729 else
  if e1730 : k = 1730 then subst e1730; exact slawChunk_1730 else
  if e1731 : k = 1731 then subst e1731; exact slawChunk_1731 else
  if e1732 : k = 1732 then subst e1732; exact slawChunk_1732 else
  if e1733 : k = 1733 then subst e1733; exact slawChunk_1733 else
  if e1734 : k = 1734 then subst e1734; exact slawChunk_1734 else
  if e1735 : k = 1735 then subst e1735; exact slawChunk_1735 else
  omega
end D2
