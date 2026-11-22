import Ski.D2Base
import Ski.D2K.S253
/-! Generated.  S-law of D: chunks 2032..2039 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_2032 : slawChunk 2032 = true := by decide +kernel
theorem slawChunk_2033 : slawChunk 2033 = true := by decide +kernel
theorem slawChunk_2034 : slawChunk 2034 = true := by decide +kernel
theorem slawChunk_2035 : slawChunk 2035 = true := by decide +kernel
theorem slawChunk_2036 : slawChunk 2036 = true := by decide +kernel
theorem slawChunk_2037 : slawChunk 2037 = true := by decide +kernel
theorem slawChunk_2038 : slawChunk 2038 = true := by decide +kernel
theorem slawChunk_2039 : slawChunk 2039 = true := by decide +kernel
theorem slawC_254 (k : Nat) (h1 : 2032 ≤ k) (h2 : k < 2040) : slawChunk k = true := by
  if e2032 : k = 2032 then subst e2032; exact slawChunk_2032 else
  if e2033 : k = 2033 then subst e2033; exact slawChunk_2033 else
  if e2034 : k = 2034 then subst e2034; exact slawChunk_2034 else
  if e2035 : k = 2035 then subst e2035; exact slawChunk_2035 else
  if e2036 : k = 2036 then subst e2036; exact slawChunk_2036 else
  if e2037 : k = 2037 then subst e2037; exact slawChunk_2037 else
  if e2038 : k = 2038 then subst e2038; exact slawChunk_2038 else
  if e2039 : k = 2039 then subst e2039; exact slawChunk_2039 else
  omega
end D2
