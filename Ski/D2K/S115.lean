import Ski.D2Base
import Ski.D2K.S114
/-! Generated.  S-law of D: chunks 920..927 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_920 : slawChunk 920 = true := by decide +kernel
theorem slawChunk_921 : slawChunk 921 = true := by decide +kernel
theorem slawChunk_922 : slawChunk 922 = true := by decide +kernel
theorem slawChunk_923 : slawChunk 923 = true := by decide +kernel
theorem slawChunk_924 : slawChunk 924 = true := by decide +kernel
theorem slawChunk_925 : slawChunk 925 = true := by decide +kernel
theorem slawChunk_926 : slawChunk 926 = true := by decide +kernel
theorem slawChunk_927 : slawChunk 927 = true := by decide +kernel
theorem slawC_115 (k : Nat) (h1 : 920 ≤ k) (h2 : k < 928) : slawChunk k = true := by
  if e920 : k = 920 then subst e920; exact slawChunk_920 else
  if e921 : k = 921 then subst e921; exact slawChunk_921 else
  if e922 : k = 922 then subst e922; exact slawChunk_922 else
  if e923 : k = 923 then subst e923; exact slawChunk_923 else
  if e924 : k = 924 then subst e924; exact slawChunk_924 else
  if e925 : k = 925 then subst e925; exact slawChunk_925 else
  if e926 : k = 926 then subst e926; exact slawChunk_926 else
  if e927 : k = 927 then subst e927; exact slawChunk_927 else
  omega
end D2
