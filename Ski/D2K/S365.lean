import Ski.D2Base
import Ski.D2K.S364
/-! Generated.  S-law of D: chunks 2920..2927 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_2920 : slawChunk 2920 = true := by decide +kernel
theorem slawChunk_2921 : slawChunk 2921 = true := by decide +kernel
theorem slawChunk_2922 : slawChunk 2922 = true := by decide +kernel
theorem slawChunk_2923 : slawChunk 2923 = true := by decide +kernel
theorem slawChunk_2924 : slawChunk 2924 = true := by decide +kernel
theorem slawChunk_2925 : slawChunk 2925 = true := by decide +kernel
theorem slawChunk_2926 : slawChunk 2926 = true := by decide +kernel
theorem slawChunk_2927 : slawChunk 2927 = true := by decide +kernel
theorem slawC_365 (k : Nat) (h1 : 2920 ≤ k) (h2 : k < 2928) : slawChunk k = true := by
  if e2920 : k = 2920 then subst e2920; exact slawChunk_2920 else
  if e2921 : k = 2921 then subst e2921; exact slawChunk_2921 else
  if e2922 : k = 2922 then subst e2922; exact slawChunk_2922 else
  if e2923 : k = 2923 then subst e2923; exact slawChunk_2923 else
  if e2924 : k = 2924 then subst e2924; exact slawChunk_2924 else
  if e2925 : k = 2925 then subst e2925; exact slawChunk_2925 else
  if e2926 : k = 2926 then subst e2926; exact slawChunk_2926 else
  if e2927 : k = 2927 then subst e2927; exact slawChunk_2927 else
  omega
end D2
