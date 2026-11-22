import Ski.D2Base
import Ski.D2K.S321
/-! Generated.  S-law of D: chunks 2576..2583 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_2576 : slawChunk 2576 = true := by decide +kernel
theorem slawChunk_2577 : slawChunk 2577 = true := by decide +kernel
theorem slawChunk_2578 : slawChunk 2578 = true := by decide +kernel
theorem slawChunk_2579 : slawChunk 2579 = true := by decide +kernel
theorem slawChunk_2580 : slawChunk 2580 = true := by decide +kernel
theorem slawChunk_2581 : slawChunk 2581 = true := by decide +kernel
theorem slawChunk_2582 : slawChunk 2582 = true := by decide +kernel
theorem slawChunk_2583 : slawChunk 2583 = true := by decide +kernel
theorem slawC_322 (k : Nat) (h1 : 2576 ≤ k) (h2 : k < 2584) : slawChunk k = true := by
  if e2576 : k = 2576 then subst e2576; exact slawChunk_2576 else
  if e2577 : k = 2577 then subst e2577; exact slawChunk_2577 else
  if e2578 : k = 2578 then subst e2578; exact slawChunk_2578 else
  if e2579 : k = 2579 then subst e2579; exact slawChunk_2579 else
  if e2580 : k = 2580 then subst e2580; exact slawChunk_2580 else
  if e2581 : k = 2581 then subst e2581; exact slawChunk_2581 else
  if e2582 : k = 2582 then subst e2582; exact slawChunk_2582 else
  if e2583 : k = 2583 then subst e2583; exact slawChunk_2583 else
  omega
end D2
