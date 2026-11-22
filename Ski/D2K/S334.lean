import Ski.D2Base
import Ski.D2K.S333
/-! Generated.  S-law of D: chunks 2672..2679 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_2672 : slawChunk 2672 = true := by decide +kernel
theorem slawChunk_2673 : slawChunk 2673 = true := by decide +kernel
theorem slawChunk_2674 : slawChunk 2674 = true := by decide +kernel
theorem slawChunk_2675 : slawChunk 2675 = true := by decide +kernel
theorem slawChunk_2676 : slawChunk 2676 = true := by decide +kernel
theorem slawChunk_2677 : slawChunk 2677 = true := by decide +kernel
theorem slawChunk_2678 : slawChunk 2678 = true := by decide +kernel
theorem slawChunk_2679 : slawChunk 2679 = true := by decide +kernel
theorem slawC_334 (k : Nat) (h1 : 2672 ≤ k) (h2 : k < 2680) : slawChunk k = true := by
  if e2672 : k = 2672 then subst e2672; exact slawChunk_2672 else
  if e2673 : k = 2673 then subst e2673; exact slawChunk_2673 else
  if e2674 : k = 2674 then subst e2674; exact slawChunk_2674 else
  if e2675 : k = 2675 then subst e2675; exact slawChunk_2675 else
  if e2676 : k = 2676 then subst e2676; exact slawChunk_2676 else
  if e2677 : k = 2677 then subst e2677; exact slawChunk_2677 else
  if e2678 : k = 2678 then subst e2678; exact slawChunk_2678 else
  if e2679 : k = 2679 then subst e2679; exact slawChunk_2679 else
  omega
end D2
