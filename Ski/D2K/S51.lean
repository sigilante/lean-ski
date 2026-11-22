import Ski.D2Base
import Ski.D2K.S50
/-! Generated.  S-law of D: chunks 408..415 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_408 : slawChunk 408 = true := by decide +kernel
theorem slawChunk_409 : slawChunk 409 = true := by decide +kernel
theorem slawChunk_410 : slawChunk 410 = true := by decide +kernel
theorem slawChunk_411 : slawChunk 411 = true := by decide +kernel
theorem slawChunk_412 : slawChunk 412 = true := by decide +kernel
theorem slawChunk_413 : slawChunk 413 = true := by decide +kernel
theorem slawChunk_414 : slawChunk 414 = true := by decide +kernel
theorem slawChunk_415 : slawChunk 415 = true := by decide +kernel
theorem slawC_51 (k : Nat) (h1 : 408 ≤ k) (h2 : k < 416) : slawChunk k = true := by
  if e408 : k = 408 then subst e408; exact slawChunk_408 else
  if e409 : k = 409 then subst e409; exact slawChunk_409 else
  if e410 : k = 410 then subst e410; exact slawChunk_410 else
  if e411 : k = 411 then subst e411; exact slawChunk_411 else
  if e412 : k = 412 then subst e412; exact slawChunk_412 else
  if e413 : k = 413 then subst e413; exact slawChunk_413 else
  if e414 : k = 414 then subst e414; exact slawChunk_414 else
  if e415 : k = 415 then subst e415; exact slawChunk_415 else
  omega
end D2
