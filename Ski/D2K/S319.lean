import Ski.D2Base
import Ski.D2K.S318
/-! Generated.  S-law of D: chunks 2552..2559 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_2552 : slawChunk 2552 = true := by decide +kernel
theorem slawChunk_2553 : slawChunk 2553 = true := by decide +kernel
theorem slawChunk_2554 : slawChunk 2554 = true := by decide +kernel
theorem slawChunk_2555 : slawChunk 2555 = true := by decide +kernel
theorem slawChunk_2556 : slawChunk 2556 = true := by decide +kernel
theorem slawChunk_2557 : slawChunk 2557 = true := by decide +kernel
theorem slawChunk_2558 : slawChunk 2558 = true := by decide +kernel
theorem slawChunk_2559 : slawChunk 2559 = true := by decide +kernel
theorem slawC_319 (k : Nat) (h1 : 2552 ≤ k) (h2 : k < 2560) : slawChunk k = true := by
  if e2552 : k = 2552 then subst e2552; exact slawChunk_2552 else
  if e2553 : k = 2553 then subst e2553; exact slawChunk_2553 else
  if e2554 : k = 2554 then subst e2554; exact slawChunk_2554 else
  if e2555 : k = 2555 then subst e2555; exact slawChunk_2555 else
  if e2556 : k = 2556 then subst e2556; exact slawChunk_2556 else
  if e2557 : k = 2557 then subst e2557; exact slawChunk_2557 else
  if e2558 : k = 2558 then subst e2558; exact slawChunk_2558 else
  if e2559 : k = 2559 then subst e2559; exact slawChunk_2559 else
  omega
end D2
