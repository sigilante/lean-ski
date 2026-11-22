import Ski.D2Base
import Ski.D2K.S369
/-! Generated.  S-law of D: chunks 2960..2967 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_2960 : slawChunk 2960 = true := by decide +kernel
theorem slawChunk_2961 : slawChunk 2961 = true := by decide +kernel
theorem slawChunk_2962 : slawChunk 2962 = true := by decide +kernel
theorem slawChunk_2963 : slawChunk 2963 = true := by decide +kernel
theorem slawChunk_2964 : slawChunk 2964 = true := by decide +kernel
theorem slawChunk_2965 : slawChunk 2965 = true := by decide +kernel
theorem slawChunk_2966 : slawChunk 2966 = true := by decide +kernel
theorem slawChunk_2967 : slawChunk 2967 = true := by decide +kernel
theorem slawC_370 (k : Nat) (h1 : 2960 ≤ k) (h2 : k < 2968) : slawChunk k = true := by
  if e2960 : k = 2960 then subst e2960; exact slawChunk_2960 else
  if e2961 : k = 2961 then subst e2961; exact slawChunk_2961 else
  if e2962 : k = 2962 then subst e2962; exact slawChunk_2962 else
  if e2963 : k = 2963 then subst e2963; exact slawChunk_2963 else
  if e2964 : k = 2964 then subst e2964; exact slawChunk_2964 else
  if e2965 : k = 2965 then subst e2965; exact slawChunk_2965 else
  if e2966 : k = 2966 then subst e2966; exact slawChunk_2966 else
  if e2967 : k = 2967 then subst e2967; exact slawChunk_2967 else
  omega
end D2
