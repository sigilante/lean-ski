import Ski.D2Base
import Ski.D2K.S116
/-! Generated.  S-law of D: chunks 936..943 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_936 : slawChunk 936 = true := by decide +kernel
theorem slawChunk_937 : slawChunk 937 = true := by decide +kernel
theorem slawChunk_938 : slawChunk 938 = true := by decide +kernel
theorem slawChunk_939 : slawChunk 939 = true := by decide +kernel
theorem slawChunk_940 : slawChunk 940 = true := by decide +kernel
theorem slawChunk_941 : slawChunk 941 = true := by decide +kernel
theorem slawChunk_942 : slawChunk 942 = true := by decide +kernel
theorem slawChunk_943 : slawChunk 943 = true := by decide +kernel
theorem slawC_117 (k : Nat) (h1 : 936 ≤ k) (h2 : k < 944) : slawChunk k = true := by
  if e936 : k = 936 then subst e936; exact slawChunk_936 else
  if e937 : k = 937 then subst e937; exact slawChunk_937 else
  if e938 : k = 938 then subst e938; exact slawChunk_938 else
  if e939 : k = 939 then subst e939; exact slawChunk_939 else
  if e940 : k = 940 then subst e940; exact slawChunk_940 else
  if e941 : k = 941 then subst e941; exact slawChunk_941 else
  if e942 : k = 942 then subst e942; exact slawChunk_942 else
  if e943 : k = 943 then subst e943; exact slawChunk_943 else
  omega
end D2
