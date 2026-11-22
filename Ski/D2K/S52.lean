import Ski.D2Base
import Ski.D2K.S51
/-! Generated.  S-law of D: chunks 416..423 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_416 : slawChunk 416 = true := by decide +kernel
theorem slawChunk_417 : slawChunk 417 = true := by decide +kernel
theorem slawChunk_418 : slawChunk 418 = true := by decide +kernel
theorem slawChunk_419 : slawChunk 419 = true := by decide +kernel
theorem slawChunk_420 : slawChunk 420 = true := by decide +kernel
theorem slawChunk_421 : slawChunk 421 = true := by decide +kernel
theorem slawChunk_422 : slawChunk 422 = true := by decide +kernel
theorem slawChunk_423 : slawChunk 423 = true := by decide +kernel
theorem slawC_52 (k : Nat) (h1 : 416 ≤ k) (h2 : k < 424) : slawChunk k = true := by
  if e416 : k = 416 then subst e416; exact slawChunk_416 else
  if e417 : k = 417 then subst e417; exact slawChunk_417 else
  if e418 : k = 418 then subst e418; exact slawChunk_418 else
  if e419 : k = 419 then subst e419; exact slawChunk_419 else
  if e420 : k = 420 then subst e420; exact slawChunk_420 else
  if e421 : k = 421 then subst e421; exact slawChunk_421 else
  if e422 : k = 422 then subst e422; exact slawChunk_422 else
  if e423 : k = 423 then subst e423; exact slawChunk_423 else
  omega
end D2
