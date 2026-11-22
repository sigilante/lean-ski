import Ski.D2Base
import Ski.D2K.S102
/-! Generated.  S-law of D: chunks 824..831 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_824 : slawChunk 824 = true := by decide +kernel
theorem slawChunk_825 : slawChunk 825 = true := by decide +kernel
theorem slawChunk_826 : slawChunk 826 = true := by decide +kernel
theorem slawChunk_827 : slawChunk 827 = true := by decide +kernel
theorem slawChunk_828 : slawChunk 828 = true := by decide +kernel
theorem slawChunk_829 : slawChunk 829 = true := by decide +kernel
theorem slawChunk_830 : slawChunk 830 = true := by decide +kernel
theorem slawChunk_831 : slawChunk 831 = true := by decide +kernel
theorem slawC_103 (k : Nat) (h1 : 824 ≤ k) (h2 : k < 832) : slawChunk k = true := by
  if e824 : k = 824 then subst e824; exact slawChunk_824 else
  if e825 : k = 825 then subst e825; exact slawChunk_825 else
  if e826 : k = 826 then subst e826; exact slawChunk_826 else
  if e827 : k = 827 then subst e827; exact slawChunk_827 else
  if e828 : k = 828 then subst e828; exact slawChunk_828 else
  if e829 : k = 829 then subst e829; exact slawChunk_829 else
  if e830 : k = 830 then subst e830; exact slawChunk_830 else
  if e831 : k = 831 then subst e831; exact slawChunk_831 else
  omega
end D2
