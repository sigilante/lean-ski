import Ski.D2Base
import Ski.D2K.S117
/-! Generated.  S-law of D: chunks 944..951 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_944 : slawChunk 944 = true := by decide +kernel
theorem slawChunk_945 : slawChunk 945 = true := by decide +kernel
theorem slawChunk_946 : slawChunk 946 = true := by decide +kernel
theorem slawChunk_947 : slawChunk 947 = true := by decide +kernel
theorem slawChunk_948 : slawChunk 948 = true := by decide +kernel
theorem slawChunk_949 : slawChunk 949 = true := by decide +kernel
theorem slawChunk_950 : slawChunk 950 = true := by decide +kernel
theorem slawChunk_951 : slawChunk 951 = true := by decide +kernel
theorem slawC_118 (k : Nat) (h1 : 944 ≤ k) (h2 : k < 952) : slawChunk k = true := by
  if e944 : k = 944 then subst e944; exact slawChunk_944 else
  if e945 : k = 945 then subst e945; exact slawChunk_945 else
  if e946 : k = 946 then subst e946; exact slawChunk_946 else
  if e947 : k = 947 then subst e947; exact slawChunk_947 else
  if e948 : k = 948 then subst e948; exact slawChunk_948 else
  if e949 : k = 949 then subst e949; exact slawChunk_949 else
  if e950 : k = 950 then subst e950; exact slawChunk_950 else
  if e951 : k = 951 then subst e951; exact slawChunk_951 else
  omega
end D2
