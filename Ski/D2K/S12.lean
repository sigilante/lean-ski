import Ski.D2Base
import Ski.D2K.S11
/-! Generated.  S-law of D: chunks 96..103 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_96 : slawChunk 96 = true := by decide +kernel
theorem slawChunk_97 : slawChunk 97 = true := by decide +kernel
theorem slawChunk_98 : slawChunk 98 = true := by decide +kernel
theorem slawChunk_99 : slawChunk 99 = true := by decide +kernel
theorem slawChunk_100 : slawChunk 100 = true := by decide +kernel
theorem slawChunk_101 : slawChunk 101 = true := by decide +kernel
theorem slawChunk_102 : slawChunk 102 = true := by decide +kernel
theorem slawChunk_103 : slawChunk 103 = true := by decide +kernel
theorem slawC_12 (k : Nat) (h1 : 96 ≤ k) (h2 : k < 104) : slawChunk k = true := by
  if e96 : k = 96 then subst e96; exact slawChunk_96 else
  if e97 : k = 97 then subst e97; exact slawChunk_97 else
  if e98 : k = 98 then subst e98; exact slawChunk_98 else
  if e99 : k = 99 then subst e99; exact slawChunk_99 else
  if e100 : k = 100 then subst e100; exact slawChunk_100 else
  if e101 : k = 101 then subst e101; exact slawChunk_101 else
  if e102 : k = 102 then subst e102; exact slawChunk_102 else
  if e103 : k = 103 then subst e103; exact slawChunk_103 else
  omega
end D2
