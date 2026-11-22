import Ski.D2Base
import Ski.D2K.S370
/-! Generated.  S-law of D: chunks 2968..2975 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_2968 : slawChunk 2968 = true := by decide +kernel
theorem slawChunk_2969 : slawChunk 2969 = true := by decide +kernel
theorem slawChunk_2970 : slawChunk 2970 = true := by decide +kernel
theorem slawChunk_2971 : slawChunk 2971 = true := by decide +kernel
theorem slawChunk_2972 : slawChunk 2972 = true := by decide +kernel
theorem slawChunk_2973 : slawChunk 2973 = true := by decide +kernel
theorem slawChunk_2974 : slawChunk 2974 = true := by decide +kernel
theorem slawChunk_2975 : slawChunk 2975 = true := by decide +kernel
theorem slawC_371 (k : Nat) (h1 : 2968 ≤ k) (h2 : k < 2976) : slawChunk k = true := by
  if e2968 : k = 2968 then subst e2968; exact slawChunk_2968 else
  if e2969 : k = 2969 then subst e2969; exact slawChunk_2969 else
  if e2970 : k = 2970 then subst e2970; exact slawChunk_2970 else
  if e2971 : k = 2971 then subst e2971; exact slawChunk_2971 else
  if e2972 : k = 2972 then subst e2972; exact slawChunk_2972 else
  if e2973 : k = 2973 then subst e2973; exact slawChunk_2973 else
  if e2974 : k = 2974 then subst e2974; exact slawChunk_2974 else
  if e2975 : k = 2975 then subst e2975; exact slawChunk_2975 else
  omega
end D2
