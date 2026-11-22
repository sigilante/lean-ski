import Ski.D2Base
import Ski.D2K.Ccols1
/-! Generated.  S-law of D: chunks 0..7 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_0 : slawChunk 0 = true := by decide +kernel
theorem slawChunk_1 : slawChunk 1 = true := by decide +kernel
theorem slawChunk_2 : slawChunk 2 = true := by decide +kernel
theorem slawChunk_3 : slawChunk 3 = true := by decide +kernel
theorem slawChunk_4 : slawChunk 4 = true := by decide +kernel
theorem slawChunk_5 : slawChunk 5 = true := by decide +kernel
theorem slawChunk_6 : slawChunk 6 = true := by decide +kernel
theorem slawChunk_7 : slawChunk 7 = true := by decide +kernel
theorem slawC_0 (k : Nat) (h1 : 0 ≤ k) (h2 : k < 8) : slawChunk k = true := by
  if e0 : k = 0 then subst e0; exact slawChunk_0 else
  if e1 : k = 1 then subst e1; exact slawChunk_1 else
  if e2 : k = 2 then subst e2; exact slawChunk_2 else
  if e3 : k = 3 then subst e3; exact slawChunk_3 else
  if e4 : k = 4 then subst e4; exact slawChunk_4 else
  if e5 : k = 5 then subst e5; exact slawChunk_5 else
  if e6 : k = 6 then subst e6; exact slawChunk_6 else
  if e7 : k = 7 then subst e7; exact slawChunk_7 else
  omega
end D2
