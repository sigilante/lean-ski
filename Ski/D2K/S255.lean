import Ski.D2Base
import Ski.D2K.S254
/-! Generated.  S-law of D: chunks 2040..2047 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_2040 : slawChunk 2040 = true := by decide +kernel
theorem slawChunk_2041 : slawChunk 2041 = true := by decide +kernel
theorem slawChunk_2042 : slawChunk 2042 = true := by decide +kernel
theorem slawChunk_2043 : slawChunk 2043 = true := by decide +kernel
theorem slawChunk_2044 : slawChunk 2044 = true := by decide +kernel
theorem slawChunk_2045 : slawChunk 2045 = true := by decide +kernel
theorem slawChunk_2046 : slawChunk 2046 = true := by decide +kernel
theorem slawChunk_2047 : slawChunk 2047 = true := by decide +kernel
theorem slawC_255 (k : Nat) (h1 : 2040 ≤ k) (h2 : k < 2048) : slawChunk k = true := by
  if e2040 : k = 2040 then subst e2040; exact slawChunk_2040 else
  if e2041 : k = 2041 then subst e2041; exact slawChunk_2041 else
  if e2042 : k = 2042 then subst e2042; exact slawChunk_2042 else
  if e2043 : k = 2043 then subst e2043; exact slawChunk_2043 else
  if e2044 : k = 2044 then subst e2044; exact slawChunk_2044 else
  if e2045 : k = 2045 then subst e2045; exact slawChunk_2045 else
  if e2046 : k = 2046 then subst e2046; exact slawChunk_2046 else
  if e2047 : k = 2047 then subst e2047; exact slawChunk_2047 else
  omega
end D2
