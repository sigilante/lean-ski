import Ski.D2Base
import Ski.D2K.S359
/-! Generated.  S-law of D: chunks 2880..2887 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_2880 : slawChunk 2880 = true := by decide +kernel
theorem slawChunk_2881 : slawChunk 2881 = true := by decide +kernel
theorem slawChunk_2882 : slawChunk 2882 = true := by decide +kernel
theorem slawChunk_2883 : slawChunk 2883 = true := by decide +kernel
theorem slawChunk_2884 : slawChunk 2884 = true := by decide +kernel
theorem slawChunk_2885 : slawChunk 2885 = true := by decide +kernel
theorem slawChunk_2886 : slawChunk 2886 = true := by decide +kernel
theorem slawChunk_2887 : slawChunk 2887 = true := by decide +kernel
theorem slawC_360 (k : Nat) (h1 : 2880 ≤ k) (h2 : k < 2888) : slawChunk k = true := by
  if e2880 : k = 2880 then subst e2880; exact slawChunk_2880 else
  if e2881 : k = 2881 then subst e2881; exact slawChunk_2881 else
  if e2882 : k = 2882 then subst e2882; exact slawChunk_2882 else
  if e2883 : k = 2883 then subst e2883; exact slawChunk_2883 else
  if e2884 : k = 2884 then subst e2884; exact slawChunk_2884 else
  if e2885 : k = 2885 then subst e2885; exact slawChunk_2885 else
  if e2886 : k = 2886 then subst e2886; exact slawChunk_2886 else
  if e2887 : k = 2887 then subst e2887; exact slawChunk_2887 else
  omega
end D2
