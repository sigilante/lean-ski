import Ski.D2Base
import Ski.D2K.S313
/-! Generated.  S-law of D: chunks 2512..2519 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_2512 : slawChunk 2512 = true := by decide +kernel
theorem slawChunk_2513 : slawChunk 2513 = true := by decide +kernel
theorem slawChunk_2514 : slawChunk 2514 = true := by decide +kernel
theorem slawChunk_2515 : slawChunk 2515 = true := by decide +kernel
theorem slawChunk_2516 : slawChunk 2516 = true := by decide +kernel
theorem slawChunk_2517 : slawChunk 2517 = true := by decide +kernel
theorem slawChunk_2518 : slawChunk 2518 = true := by decide +kernel
theorem slawChunk_2519 : slawChunk 2519 = true := by decide +kernel
theorem slawC_314 (k : Nat) (h1 : 2512 ≤ k) (h2 : k < 2520) : slawChunk k = true := by
  if e2512 : k = 2512 then subst e2512; exact slawChunk_2512 else
  if e2513 : k = 2513 then subst e2513; exact slawChunk_2513 else
  if e2514 : k = 2514 then subst e2514; exact slawChunk_2514 else
  if e2515 : k = 2515 then subst e2515; exact slawChunk_2515 else
  if e2516 : k = 2516 then subst e2516; exact slawChunk_2516 else
  if e2517 : k = 2517 then subst e2517; exact slawChunk_2517 else
  if e2518 : k = 2518 then subst e2518; exact slawChunk_2518 else
  if e2519 : k = 2519 then subst e2519; exact slawChunk_2519 else
  omega
end D2
