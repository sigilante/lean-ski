import Ski.D2Base
import Ski.D2K.S65
/-! Generated.  S-law of D: chunks 528..535 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_528 : slawChunk 528 = true := by decide +kernel
theorem slawChunk_529 : slawChunk 529 = true := by decide +kernel
theorem slawChunk_530 : slawChunk 530 = true := by decide +kernel
theorem slawChunk_531 : slawChunk 531 = true := by decide +kernel
theorem slawChunk_532 : slawChunk 532 = true := by decide +kernel
theorem slawChunk_533 : slawChunk 533 = true := by decide +kernel
theorem slawChunk_534 : slawChunk 534 = true := by decide +kernel
theorem slawChunk_535 : slawChunk 535 = true := by decide +kernel
theorem slawC_66 (k : Nat) (h1 : 528 ≤ k) (h2 : k < 536) : slawChunk k = true := by
  if e528 : k = 528 then subst e528; exact slawChunk_528 else
  if e529 : k = 529 then subst e529; exact slawChunk_529 else
  if e530 : k = 530 then subst e530; exact slawChunk_530 else
  if e531 : k = 531 then subst e531; exact slawChunk_531 else
  if e532 : k = 532 then subst e532; exact slawChunk_532 else
  if e533 : k = 533 then subst e533; exact slawChunk_533 else
  if e534 : k = 534 then subst e534; exact slawChunk_534 else
  if e535 : k = 535 then subst e535; exact slawChunk_535 else
  omega
end D2
