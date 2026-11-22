import Ski.D2Base
import Ski.D2K.S252
/-! Generated.  S-law of D: chunks 2024..2031 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_2024 : slawChunk 2024 = true := by decide +kernel
theorem slawChunk_2025 : slawChunk 2025 = true := by decide +kernel
theorem slawChunk_2026 : slawChunk 2026 = true := by decide +kernel
theorem slawChunk_2027 : slawChunk 2027 = true := by decide +kernel
theorem slawChunk_2028 : slawChunk 2028 = true := by decide +kernel
theorem slawChunk_2029 : slawChunk 2029 = true := by decide +kernel
theorem slawChunk_2030 : slawChunk 2030 = true := by decide +kernel
theorem slawChunk_2031 : slawChunk 2031 = true := by decide +kernel
theorem slawC_253 (k : Nat) (h1 : 2024 ≤ k) (h2 : k < 2032) : slawChunk k = true := by
  if e2024 : k = 2024 then subst e2024; exact slawChunk_2024 else
  if e2025 : k = 2025 then subst e2025; exact slawChunk_2025 else
  if e2026 : k = 2026 then subst e2026; exact slawChunk_2026 else
  if e2027 : k = 2027 then subst e2027; exact slawChunk_2027 else
  if e2028 : k = 2028 then subst e2028; exact slawChunk_2028 else
  if e2029 : k = 2029 then subst e2029; exact slawChunk_2029 else
  if e2030 : k = 2030 then subst e2030; exact slawChunk_2030 else
  if e2031 : k = 2031 then subst e2031; exact slawChunk_2031 else
  omega
end D2
