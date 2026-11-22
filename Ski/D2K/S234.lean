import Ski.D2Base
import Ski.D2K.S233
/-! Generated.  S-law of D: chunks 1872..1879 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_1872 : slawChunk 1872 = true := by decide +kernel
theorem slawChunk_1873 : slawChunk 1873 = true := by decide +kernel
theorem slawChunk_1874 : slawChunk 1874 = true := by decide +kernel
theorem slawChunk_1875 : slawChunk 1875 = true := by decide +kernel
theorem slawChunk_1876 : slawChunk 1876 = true := by decide +kernel
theorem slawChunk_1877 : slawChunk 1877 = true := by decide +kernel
theorem slawChunk_1878 : slawChunk 1878 = true := by decide +kernel
theorem slawChunk_1879 : slawChunk 1879 = true := by decide +kernel
theorem slawC_234 (k : Nat) (h1 : 1872 ≤ k) (h2 : k < 1880) : slawChunk k = true := by
  if e1872 : k = 1872 then subst e1872; exact slawChunk_1872 else
  if e1873 : k = 1873 then subst e1873; exact slawChunk_1873 else
  if e1874 : k = 1874 then subst e1874; exact slawChunk_1874 else
  if e1875 : k = 1875 then subst e1875; exact slawChunk_1875 else
  if e1876 : k = 1876 then subst e1876; exact slawChunk_1876 else
  if e1877 : k = 1877 then subst e1877; exact slawChunk_1877 else
  if e1878 : k = 1878 then subst e1878; exact slawChunk_1878 else
  if e1879 : k = 1879 then subst e1879; exact slawChunk_1879 else
  omega
end D2
