import Ski.D2Base
import Ski.D2K.S225
/-! Generated.  S-law of D: chunks 1808..1815 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_1808 : slawChunk 1808 = true := by decide +kernel
theorem slawChunk_1809 : slawChunk 1809 = true := by decide +kernel
theorem slawChunk_1810 : slawChunk 1810 = true := by decide +kernel
theorem slawChunk_1811 : slawChunk 1811 = true := by decide +kernel
theorem slawChunk_1812 : slawChunk 1812 = true := by decide +kernel
theorem slawChunk_1813 : slawChunk 1813 = true := by decide +kernel
theorem slawChunk_1814 : slawChunk 1814 = true := by decide +kernel
theorem slawChunk_1815 : slawChunk 1815 = true := by decide +kernel
theorem slawC_226 (k : Nat) (h1 : 1808 ≤ k) (h2 : k < 1816) : slawChunk k = true := by
  if e1808 : k = 1808 then subst e1808; exact slawChunk_1808 else
  if e1809 : k = 1809 then subst e1809; exact slawChunk_1809 else
  if e1810 : k = 1810 then subst e1810; exact slawChunk_1810 else
  if e1811 : k = 1811 then subst e1811; exact slawChunk_1811 else
  if e1812 : k = 1812 then subst e1812; exact slawChunk_1812 else
  if e1813 : k = 1813 then subst e1813; exact slawChunk_1813 else
  if e1814 : k = 1814 then subst e1814; exact slawChunk_1814 else
  if e1815 : k = 1815 then subst e1815; exact slawChunk_1815 else
  omega
end D2
