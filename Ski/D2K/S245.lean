import Ski.D2Base
import Ski.D2K.S244
/-! Generated.  S-law of D: chunks 1960..1967 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_1960 : slawChunk 1960 = true := by decide +kernel
theorem slawChunk_1961 : slawChunk 1961 = true := by decide +kernel
theorem slawChunk_1962 : slawChunk 1962 = true := by decide +kernel
theorem slawChunk_1963 : slawChunk 1963 = true := by decide +kernel
theorem slawChunk_1964 : slawChunk 1964 = true := by decide +kernel
theorem slawChunk_1965 : slawChunk 1965 = true := by decide +kernel
theorem slawChunk_1966 : slawChunk 1966 = true := by decide +kernel
theorem slawChunk_1967 : slawChunk 1967 = true := by decide +kernel
theorem slawC_245 (k : Nat) (h1 : 1960 ≤ k) (h2 : k < 1968) : slawChunk k = true := by
  if e1960 : k = 1960 then subst e1960; exact slawChunk_1960 else
  if e1961 : k = 1961 then subst e1961; exact slawChunk_1961 else
  if e1962 : k = 1962 then subst e1962; exact slawChunk_1962 else
  if e1963 : k = 1963 then subst e1963; exact slawChunk_1963 else
  if e1964 : k = 1964 then subst e1964; exact slawChunk_1964 else
  if e1965 : k = 1965 then subst e1965; exact slawChunk_1965 else
  if e1966 : k = 1966 then subst e1966; exact slawChunk_1966 else
  if e1967 : k = 1967 then subst e1967; exact slawChunk_1967 else
  omega
end D2
