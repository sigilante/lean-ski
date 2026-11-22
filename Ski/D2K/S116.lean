import Ski.D2Base
import Ski.D2K.S115
/-! Generated.  S-law of D: chunks 928..935 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_928 : slawChunk 928 = true := by decide +kernel
theorem slawChunk_929 : slawChunk 929 = true := by decide +kernel
theorem slawChunk_930 : slawChunk 930 = true := by decide +kernel
theorem slawChunk_931 : slawChunk 931 = true := by decide +kernel
theorem slawChunk_932 : slawChunk 932 = true := by decide +kernel
theorem slawChunk_933 : slawChunk 933 = true := by decide +kernel
theorem slawChunk_934 : slawChunk 934 = true := by decide +kernel
theorem slawChunk_935 : slawChunk 935 = true := by decide +kernel
theorem slawC_116 (k : Nat) (h1 : 928 ≤ k) (h2 : k < 936) : slawChunk k = true := by
  if e928 : k = 928 then subst e928; exact slawChunk_928 else
  if e929 : k = 929 then subst e929; exact slawChunk_929 else
  if e930 : k = 930 then subst e930; exact slawChunk_930 else
  if e931 : k = 931 then subst e931; exact slawChunk_931 else
  if e932 : k = 932 then subst e932; exact slawChunk_932 else
  if e933 : k = 933 then subst e933; exact slawChunk_933 else
  if e934 : k = 934 then subst e934; exact slawChunk_934 else
  if e935 : k = 935 then subst e935; exact slawChunk_935 else
  omega
end D2
