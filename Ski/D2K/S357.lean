import Ski.D2Base
import Ski.D2K.S356
/-! Generated.  S-law of D: chunks 2856..2863 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_2856 : slawChunk 2856 = true := by decide +kernel
theorem slawChunk_2857 : slawChunk 2857 = true := by decide +kernel
theorem slawChunk_2858 : slawChunk 2858 = true := by decide +kernel
theorem slawChunk_2859 : slawChunk 2859 = true := by decide +kernel
theorem slawChunk_2860 : slawChunk 2860 = true := by decide +kernel
theorem slawChunk_2861 : slawChunk 2861 = true := by decide +kernel
theorem slawChunk_2862 : slawChunk 2862 = true := by decide +kernel
theorem slawChunk_2863 : slawChunk 2863 = true := by decide +kernel
theorem slawC_357 (k : Nat) (h1 : 2856 ≤ k) (h2 : k < 2864) : slawChunk k = true := by
  if e2856 : k = 2856 then subst e2856; exact slawChunk_2856 else
  if e2857 : k = 2857 then subst e2857; exact slawChunk_2857 else
  if e2858 : k = 2858 then subst e2858; exact slawChunk_2858 else
  if e2859 : k = 2859 then subst e2859; exact slawChunk_2859 else
  if e2860 : k = 2860 then subst e2860; exact slawChunk_2860 else
  if e2861 : k = 2861 then subst e2861; exact slawChunk_2861 else
  if e2862 : k = 2862 then subst e2862; exact slawChunk_2862 else
  if e2863 : k = 2863 then subst e2863; exact slawChunk_2863 else
  omega
end D2
