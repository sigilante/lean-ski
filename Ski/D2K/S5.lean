import Ski.D2Base
import Ski.D2K.S4
/-! Generated.  S-law of D: chunks 40..47 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_40 : slawChunk 40 = true := by decide +kernel
theorem slawChunk_41 : slawChunk 41 = true := by decide +kernel
theorem slawChunk_42 : slawChunk 42 = true := by decide +kernel
theorem slawChunk_43 : slawChunk 43 = true := by decide +kernel
theorem slawChunk_44 : slawChunk 44 = true := by decide +kernel
theorem slawChunk_45 : slawChunk 45 = true := by decide +kernel
theorem slawChunk_46 : slawChunk 46 = true := by decide +kernel
theorem slawChunk_47 : slawChunk 47 = true := by decide +kernel
theorem slawC_5 (k : Nat) (h1 : 40 ≤ k) (h2 : k < 48) : slawChunk k = true := by
  if e40 : k = 40 then subst e40; exact slawChunk_40 else
  if e41 : k = 41 then subst e41; exact slawChunk_41 else
  if e42 : k = 42 then subst e42; exact slawChunk_42 else
  if e43 : k = 43 then subst e43; exact slawChunk_43 else
  if e44 : k = 44 then subst e44; exact slawChunk_44 else
  if e45 : k = 45 then subst e45; exact slawChunk_45 else
  if e46 : k = 46 then subst e46; exact slawChunk_46 else
  if e47 : k = 47 then subst e47; exact slawChunk_47 else
  omega
end D2
