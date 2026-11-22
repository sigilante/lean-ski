import Ski.D2Base
import Ski.D2K.S76
/-! Generated.  S-law of D: chunks 616..623 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_616 : slawChunk 616 = true := by decide +kernel
theorem slawChunk_617 : slawChunk 617 = true := by decide +kernel
theorem slawChunk_618 : slawChunk 618 = true := by decide +kernel
theorem slawChunk_619 : slawChunk 619 = true := by decide +kernel
theorem slawChunk_620 : slawChunk 620 = true := by decide +kernel
theorem slawChunk_621 : slawChunk 621 = true := by decide +kernel
theorem slawChunk_622 : slawChunk 622 = true := by decide +kernel
theorem slawChunk_623 : slawChunk 623 = true := by decide +kernel
theorem slawC_77 (k : Nat) (h1 : 616 ≤ k) (h2 : k < 624) : slawChunk k = true := by
  if e616 : k = 616 then subst e616; exact slawChunk_616 else
  if e617 : k = 617 then subst e617; exact slawChunk_617 else
  if e618 : k = 618 then subst e618; exact slawChunk_618 else
  if e619 : k = 619 then subst e619; exact slawChunk_619 else
  if e620 : k = 620 then subst e620; exact slawChunk_620 else
  if e621 : k = 621 then subst e621; exact slawChunk_621 else
  if e622 : k = 622 then subst e622; exact slawChunk_622 else
  if e623 : k = 623 then subst e623; exact slawChunk_623 else
  omega
end D2
