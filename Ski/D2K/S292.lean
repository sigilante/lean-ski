import Ski.D2Base
import Ski.D2K.S291
/-! Generated.  S-law of D: chunks 2336..2343 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_2336 : slawChunk 2336 = true := by decide +kernel
theorem slawChunk_2337 : slawChunk 2337 = true := by decide +kernel
theorem slawChunk_2338 : slawChunk 2338 = true := by decide +kernel
theorem slawChunk_2339 : slawChunk 2339 = true := by decide +kernel
theorem slawChunk_2340 : slawChunk 2340 = true := by decide +kernel
theorem slawChunk_2341 : slawChunk 2341 = true := by decide +kernel
theorem slawChunk_2342 : slawChunk 2342 = true := by decide +kernel
theorem slawChunk_2343 : slawChunk 2343 = true := by decide +kernel
theorem slawC_292 (k : Nat) (h1 : 2336 ≤ k) (h2 : k < 2344) : slawChunk k = true := by
  if e2336 : k = 2336 then subst e2336; exact slawChunk_2336 else
  if e2337 : k = 2337 then subst e2337; exact slawChunk_2337 else
  if e2338 : k = 2338 then subst e2338; exact slawChunk_2338 else
  if e2339 : k = 2339 then subst e2339; exact slawChunk_2339 else
  if e2340 : k = 2340 then subst e2340; exact slawChunk_2340 else
  if e2341 : k = 2341 then subst e2341; exact slawChunk_2341 else
  if e2342 : k = 2342 then subst e2342; exact slawChunk_2342 else
  if e2343 : k = 2343 then subst e2343; exact slawChunk_2343 else
  omega
end D2
