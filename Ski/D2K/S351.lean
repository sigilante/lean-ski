import Ski.D2Base
import Ski.D2K.S350
/-! Generated.  S-law of D: chunks 2808..2815 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_2808 : slawChunk 2808 = true := by decide +kernel
theorem slawChunk_2809 : slawChunk 2809 = true := by decide +kernel
theorem slawChunk_2810 : slawChunk 2810 = true := by decide +kernel
theorem slawChunk_2811 : slawChunk 2811 = true := by decide +kernel
theorem slawChunk_2812 : slawChunk 2812 = true := by decide +kernel
theorem slawChunk_2813 : slawChunk 2813 = true := by decide +kernel
theorem slawChunk_2814 : slawChunk 2814 = true := by decide +kernel
theorem slawChunk_2815 : slawChunk 2815 = true := by decide +kernel
theorem slawC_351 (k : Nat) (h1 : 2808 ≤ k) (h2 : k < 2816) : slawChunk k = true := by
  if e2808 : k = 2808 then subst e2808; exact slawChunk_2808 else
  if e2809 : k = 2809 then subst e2809; exact slawChunk_2809 else
  if e2810 : k = 2810 then subst e2810; exact slawChunk_2810 else
  if e2811 : k = 2811 then subst e2811; exact slawChunk_2811 else
  if e2812 : k = 2812 then subst e2812; exact slawChunk_2812 else
  if e2813 : k = 2813 then subst e2813; exact slawChunk_2813 else
  if e2814 : k = 2814 then subst e2814; exact slawChunk_2814 else
  if e2815 : k = 2815 then subst e2815; exact slawChunk_2815 else
  omega
end D2
