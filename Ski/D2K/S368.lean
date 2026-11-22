import Ski.D2Base
import Ski.D2K.S367
/-! Generated.  S-law of D: chunks 2944..2951 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_2944 : slawChunk 2944 = true := by decide +kernel
theorem slawChunk_2945 : slawChunk 2945 = true := by decide +kernel
theorem slawChunk_2946 : slawChunk 2946 = true := by decide +kernel
theorem slawChunk_2947 : slawChunk 2947 = true := by decide +kernel
theorem slawChunk_2948 : slawChunk 2948 = true := by decide +kernel
theorem slawChunk_2949 : slawChunk 2949 = true := by decide +kernel
theorem slawChunk_2950 : slawChunk 2950 = true := by decide +kernel
theorem slawChunk_2951 : slawChunk 2951 = true := by decide +kernel
theorem slawC_368 (k : Nat) (h1 : 2944 ≤ k) (h2 : k < 2952) : slawChunk k = true := by
  if e2944 : k = 2944 then subst e2944; exact slawChunk_2944 else
  if e2945 : k = 2945 then subst e2945; exact slawChunk_2945 else
  if e2946 : k = 2946 then subst e2946; exact slawChunk_2946 else
  if e2947 : k = 2947 then subst e2947; exact slawChunk_2947 else
  if e2948 : k = 2948 then subst e2948; exact slawChunk_2948 else
  if e2949 : k = 2949 then subst e2949; exact slawChunk_2949 else
  if e2950 : k = 2950 then subst e2950; exact slawChunk_2950 else
  if e2951 : k = 2951 then subst e2951; exact slawChunk_2951 else
  omega
end D2
