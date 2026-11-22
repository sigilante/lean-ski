import Ski.D2Base
import Ski.D2K.S352
/-! Generated.  S-law of D: chunks 2824..2831 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_2824 : slawChunk 2824 = true := by decide +kernel
theorem slawChunk_2825 : slawChunk 2825 = true := by decide +kernel
theorem slawChunk_2826 : slawChunk 2826 = true := by decide +kernel
theorem slawChunk_2827 : slawChunk 2827 = true := by decide +kernel
theorem slawChunk_2828 : slawChunk 2828 = true := by decide +kernel
theorem slawChunk_2829 : slawChunk 2829 = true := by decide +kernel
theorem slawChunk_2830 : slawChunk 2830 = true := by decide +kernel
theorem slawChunk_2831 : slawChunk 2831 = true := by decide +kernel
theorem slawC_353 (k : Nat) (h1 : 2824 ≤ k) (h2 : k < 2832) : slawChunk k = true := by
  if e2824 : k = 2824 then subst e2824; exact slawChunk_2824 else
  if e2825 : k = 2825 then subst e2825; exact slawChunk_2825 else
  if e2826 : k = 2826 then subst e2826; exact slawChunk_2826 else
  if e2827 : k = 2827 then subst e2827; exact slawChunk_2827 else
  if e2828 : k = 2828 then subst e2828; exact slawChunk_2828 else
  if e2829 : k = 2829 then subst e2829; exact slawChunk_2829 else
  if e2830 : k = 2830 then subst e2830; exact slawChunk_2830 else
  if e2831 : k = 2831 then subst e2831; exact slawChunk_2831 else
  omega
end D2
