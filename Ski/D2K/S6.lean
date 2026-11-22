import Ski.D2Base
import Ski.D2K.S5
/-! Generated.  S-law of D: chunks 48..55 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_48 : slawChunk 48 = true := by decide +kernel
theorem slawChunk_49 : slawChunk 49 = true := by decide +kernel
theorem slawChunk_50 : slawChunk 50 = true := by decide +kernel
theorem slawChunk_51 : slawChunk 51 = true := by decide +kernel
theorem slawChunk_52 : slawChunk 52 = true := by decide +kernel
theorem slawChunk_53 : slawChunk 53 = true := by decide +kernel
theorem slawChunk_54 : slawChunk 54 = true := by decide +kernel
theorem slawChunk_55 : slawChunk 55 = true := by decide +kernel
theorem slawC_6 (k : Nat) (h1 : 48 ≤ k) (h2 : k < 56) : slawChunk k = true := by
  if e48 : k = 48 then subst e48; exact slawChunk_48 else
  if e49 : k = 49 then subst e49; exact slawChunk_49 else
  if e50 : k = 50 then subst e50; exact slawChunk_50 else
  if e51 : k = 51 then subst e51; exact slawChunk_51 else
  if e52 : k = 52 then subst e52; exact slawChunk_52 else
  if e53 : k = 53 then subst e53; exact slawChunk_53 else
  if e54 : k = 54 then subst e54; exact slawChunk_54 else
  if e55 : k = 55 then subst e55; exact slawChunk_55 else
  omega
end D2
