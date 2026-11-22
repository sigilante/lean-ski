import Ski.D2Base
import Ski.D2K.S340
/-! Generated.  S-law of D: chunks 2728..2735 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_2728 : slawChunk 2728 = true := by decide +kernel
theorem slawChunk_2729 : slawChunk 2729 = true := by decide +kernel
theorem slawChunk_2730 : slawChunk 2730 = true := by decide +kernel
theorem slawChunk_2731 : slawChunk 2731 = true := by decide +kernel
theorem slawChunk_2732 : slawChunk 2732 = true := by decide +kernel
theorem slawChunk_2733 : slawChunk 2733 = true := by decide +kernel
theorem slawChunk_2734 : slawChunk 2734 = true := by decide +kernel
theorem slawChunk_2735 : slawChunk 2735 = true := by decide +kernel
theorem slawC_341 (k : Nat) (h1 : 2728 ≤ k) (h2 : k < 2736) : slawChunk k = true := by
  if e2728 : k = 2728 then subst e2728; exact slawChunk_2728 else
  if e2729 : k = 2729 then subst e2729; exact slawChunk_2729 else
  if e2730 : k = 2730 then subst e2730; exact slawChunk_2730 else
  if e2731 : k = 2731 then subst e2731; exact slawChunk_2731 else
  if e2732 : k = 2732 then subst e2732; exact slawChunk_2732 else
  if e2733 : k = 2733 then subst e2733; exact slawChunk_2733 else
  if e2734 : k = 2734 then subst e2734; exact slawChunk_2734 else
  if e2735 : k = 2735 then subst e2735; exact slawChunk_2735 else
  omega
end D2
