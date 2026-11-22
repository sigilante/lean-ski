import Ski.D2Base
import Ski.D2K.S366
/-! Generated.  S-law of D: chunks 2936..2943 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_2936 : slawChunk 2936 = true := by decide +kernel
theorem slawChunk_2937 : slawChunk 2937 = true := by decide +kernel
theorem slawChunk_2938 : slawChunk 2938 = true := by decide +kernel
theorem slawChunk_2939 : slawChunk 2939 = true := by decide +kernel
theorem slawChunk_2940 : slawChunk 2940 = true := by decide +kernel
theorem slawChunk_2941 : slawChunk 2941 = true := by decide +kernel
theorem slawChunk_2942 : slawChunk 2942 = true := by decide +kernel
theorem slawChunk_2943 : slawChunk 2943 = true := by decide +kernel
theorem slawC_367 (k : Nat) (h1 : 2936 ≤ k) (h2 : k < 2944) : slawChunk k = true := by
  if e2936 : k = 2936 then subst e2936; exact slawChunk_2936 else
  if e2937 : k = 2937 then subst e2937; exact slawChunk_2937 else
  if e2938 : k = 2938 then subst e2938; exact slawChunk_2938 else
  if e2939 : k = 2939 then subst e2939; exact slawChunk_2939 else
  if e2940 : k = 2940 then subst e2940; exact slawChunk_2940 else
  if e2941 : k = 2941 then subst e2941; exact slawChunk_2941 else
  if e2942 : k = 2942 then subst e2942; exact slawChunk_2942 else
  if e2943 : k = 2943 then subst e2943; exact slawChunk_2943 else
  omega
end D2
