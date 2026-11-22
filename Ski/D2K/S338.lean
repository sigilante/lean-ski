import Ski.D2Base
import Ski.D2K.S337
/-! Generated.  S-law of D: chunks 2704..2711 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_2704 : slawChunk 2704 = true := by decide +kernel
theorem slawChunk_2705 : slawChunk 2705 = true := by decide +kernel
theorem slawChunk_2706 : slawChunk 2706 = true := by decide +kernel
theorem slawChunk_2707 : slawChunk 2707 = true := by decide +kernel
theorem slawChunk_2708 : slawChunk 2708 = true := by decide +kernel
theorem slawChunk_2709 : slawChunk 2709 = true := by decide +kernel
theorem slawChunk_2710 : slawChunk 2710 = true := by decide +kernel
theorem slawChunk_2711 : slawChunk 2711 = true := by decide +kernel
theorem slawC_338 (k : Nat) (h1 : 2704 ≤ k) (h2 : k < 2712) : slawChunk k = true := by
  if e2704 : k = 2704 then subst e2704; exact slawChunk_2704 else
  if e2705 : k = 2705 then subst e2705; exact slawChunk_2705 else
  if e2706 : k = 2706 then subst e2706; exact slawChunk_2706 else
  if e2707 : k = 2707 then subst e2707; exact slawChunk_2707 else
  if e2708 : k = 2708 then subst e2708; exact slawChunk_2708 else
  if e2709 : k = 2709 then subst e2709; exact slawChunk_2709 else
  if e2710 : k = 2710 then subst e2710; exact slawChunk_2710 else
  if e2711 : k = 2711 then subst e2711; exact slawChunk_2711 else
  omega
end D2
