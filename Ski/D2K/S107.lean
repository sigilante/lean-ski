import Ski.D2Base
import Ski.D2K.S106
/-! Generated.  S-law of D: chunks 856..863 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_856 : slawChunk 856 = true := by decide +kernel
theorem slawChunk_857 : slawChunk 857 = true := by decide +kernel
theorem slawChunk_858 : slawChunk 858 = true := by decide +kernel
theorem slawChunk_859 : slawChunk 859 = true := by decide +kernel
theorem slawChunk_860 : slawChunk 860 = true := by decide +kernel
theorem slawChunk_861 : slawChunk 861 = true := by decide +kernel
theorem slawChunk_862 : slawChunk 862 = true := by decide +kernel
theorem slawChunk_863 : slawChunk 863 = true := by decide +kernel
theorem slawC_107 (k : Nat) (h1 : 856 ≤ k) (h2 : k < 864) : slawChunk k = true := by
  if e856 : k = 856 then subst e856; exact slawChunk_856 else
  if e857 : k = 857 then subst e857; exact slawChunk_857 else
  if e858 : k = 858 then subst e858; exact slawChunk_858 else
  if e859 : k = 859 then subst e859; exact slawChunk_859 else
  if e860 : k = 860 then subst e860; exact slawChunk_860 else
  if e861 : k = 861 then subst e861; exact slawChunk_861 else
  if e862 : k = 862 then subst e862; exact slawChunk_862 else
  if e863 : k = 863 then subst e863; exact slawChunk_863 else
  omega
end D2
