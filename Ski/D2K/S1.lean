import Ski.D2Base
import Ski.D2K.S0
/-! Generated.  S-law of D: chunks 8..15 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_8 : slawChunk 8 = true := by decide +kernel
theorem slawChunk_9 : slawChunk 9 = true := by decide +kernel
theorem slawChunk_10 : slawChunk 10 = true := by decide +kernel
theorem slawChunk_11 : slawChunk 11 = true := by decide +kernel
theorem slawChunk_12 : slawChunk 12 = true := by decide +kernel
theorem slawChunk_13 : slawChunk 13 = true := by decide +kernel
theorem slawChunk_14 : slawChunk 14 = true := by decide +kernel
theorem slawChunk_15 : slawChunk 15 = true := by decide +kernel
theorem slawC_1 (k : Nat) (h1 : 8 ≤ k) (h2 : k < 16) : slawChunk k = true := by
  if e8 : k = 8 then subst e8; exact slawChunk_8 else
  if e9 : k = 9 then subst e9; exact slawChunk_9 else
  if e10 : k = 10 then subst e10; exact slawChunk_10 else
  if e11 : k = 11 then subst e11; exact slawChunk_11 else
  if e12 : k = 12 then subst e12; exact slawChunk_12 else
  if e13 : k = 13 then subst e13; exact slawChunk_13 else
  if e14 : k = 14 then subst e14; exact slawChunk_14 else
  if e15 : k = 15 then subst e15; exact slawChunk_15 else
  omega
end D2
