import Ski.D2Base
import Ski.D2K.S218
/-! Generated.  S-law of D: chunks 1752..1759 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_1752 : slawChunk 1752 = true := by decide +kernel
theorem slawChunk_1753 : slawChunk 1753 = true := by decide +kernel
theorem slawChunk_1754 : slawChunk 1754 = true := by decide +kernel
theorem slawChunk_1755 : slawChunk 1755 = true := by decide +kernel
theorem slawChunk_1756 : slawChunk 1756 = true := by decide +kernel
theorem slawChunk_1757 : slawChunk 1757 = true := by decide +kernel
theorem slawChunk_1758 : slawChunk 1758 = true := by decide +kernel
theorem slawChunk_1759 : slawChunk 1759 = true := by decide +kernel
theorem slawC_219 (k : Nat) (h1 : 1752 ≤ k) (h2 : k < 1760) : slawChunk k = true := by
  if e1752 : k = 1752 then subst e1752; exact slawChunk_1752 else
  if e1753 : k = 1753 then subst e1753; exact slawChunk_1753 else
  if e1754 : k = 1754 then subst e1754; exact slawChunk_1754 else
  if e1755 : k = 1755 then subst e1755; exact slawChunk_1755 else
  if e1756 : k = 1756 then subst e1756; exact slawChunk_1756 else
  if e1757 : k = 1757 then subst e1757; exact slawChunk_1757 else
  if e1758 : k = 1758 then subst e1758; exact slawChunk_1758 else
  if e1759 : k = 1759 then subst e1759; exact slawChunk_1759 else
  omega
end D2
