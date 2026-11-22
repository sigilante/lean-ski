import Ski.D2Base
import Ski.D2K.S368
/-! Generated.  S-law of D: chunks 2952..2959 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_2952 : slawChunk 2952 = true := by decide +kernel
theorem slawChunk_2953 : slawChunk 2953 = true := by decide +kernel
theorem slawChunk_2954 : slawChunk 2954 = true := by decide +kernel
theorem slawChunk_2955 : slawChunk 2955 = true := by decide +kernel
theorem slawChunk_2956 : slawChunk 2956 = true := by decide +kernel
theorem slawChunk_2957 : slawChunk 2957 = true := by decide +kernel
theorem slawChunk_2958 : slawChunk 2958 = true := by decide +kernel
theorem slawChunk_2959 : slawChunk 2959 = true := by decide +kernel
theorem slawC_369 (k : Nat) (h1 : 2952 ≤ k) (h2 : k < 2960) : slawChunk k = true := by
  if e2952 : k = 2952 then subst e2952; exact slawChunk_2952 else
  if e2953 : k = 2953 then subst e2953; exact slawChunk_2953 else
  if e2954 : k = 2954 then subst e2954; exact slawChunk_2954 else
  if e2955 : k = 2955 then subst e2955; exact slawChunk_2955 else
  if e2956 : k = 2956 then subst e2956; exact slawChunk_2956 else
  if e2957 : k = 2957 then subst e2957; exact slawChunk_2957 else
  if e2958 : k = 2958 then subst e2958; exact slawChunk_2958 else
  if e2959 : k = 2959 then subst e2959; exact slawChunk_2959 else
  omega
end D2
