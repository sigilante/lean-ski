import Ski.D2Base
import Ski.D2K.S326
/-! Generated.  S-law of D: chunks 2616..2623 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_2616 : slawChunk 2616 = true := by decide +kernel
theorem slawChunk_2617 : slawChunk 2617 = true := by decide +kernel
theorem slawChunk_2618 : slawChunk 2618 = true := by decide +kernel
theorem slawChunk_2619 : slawChunk 2619 = true := by decide +kernel
theorem slawChunk_2620 : slawChunk 2620 = true := by decide +kernel
theorem slawChunk_2621 : slawChunk 2621 = true := by decide +kernel
theorem slawChunk_2622 : slawChunk 2622 = true := by decide +kernel
theorem slawChunk_2623 : slawChunk 2623 = true := by decide +kernel
theorem slawC_327 (k : Nat) (h1 : 2616 ≤ k) (h2 : k < 2624) : slawChunk k = true := by
  if e2616 : k = 2616 then subst e2616; exact slawChunk_2616 else
  if e2617 : k = 2617 then subst e2617; exact slawChunk_2617 else
  if e2618 : k = 2618 then subst e2618; exact slawChunk_2618 else
  if e2619 : k = 2619 then subst e2619; exact slawChunk_2619 else
  if e2620 : k = 2620 then subst e2620; exact slawChunk_2620 else
  if e2621 : k = 2621 then subst e2621; exact slawChunk_2621 else
  if e2622 : k = 2622 then subst e2622; exact slawChunk_2622 else
  if e2623 : k = 2623 then subst e2623; exact slawChunk_2623 else
  omega
end D2
