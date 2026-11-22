import Ski.D2Base
import Ski.D2K.S71
/-! Generated.  S-law of D: chunks 576..583 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_576 : slawChunk 576 = true := by decide +kernel
theorem slawChunk_577 : slawChunk 577 = true := by decide +kernel
theorem slawChunk_578 : slawChunk 578 = true := by decide +kernel
theorem slawChunk_579 : slawChunk 579 = true := by decide +kernel
theorem slawChunk_580 : slawChunk 580 = true := by decide +kernel
theorem slawChunk_581 : slawChunk 581 = true := by decide +kernel
theorem slawChunk_582 : slawChunk 582 = true := by decide +kernel
theorem slawChunk_583 : slawChunk 583 = true := by decide +kernel
theorem slawC_72 (k : Nat) (h1 : 576 ≤ k) (h2 : k < 584) : slawChunk k = true := by
  if e576 : k = 576 then subst e576; exact slawChunk_576 else
  if e577 : k = 577 then subst e577; exact slawChunk_577 else
  if e578 : k = 578 then subst e578; exact slawChunk_578 else
  if e579 : k = 579 then subst e579; exact slawChunk_579 else
  if e580 : k = 580 then subst e580; exact slawChunk_580 else
  if e581 : k = 581 then subst e581; exact slawChunk_581 else
  if e582 : k = 582 then subst e582; exact slawChunk_582 else
  if e583 : k = 583 then subst e583; exact slawChunk_583 else
  omega
end D2
