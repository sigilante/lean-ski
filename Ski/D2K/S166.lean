import Ski.D2Base
import Ski.D2K.S165
/-! Generated.  S-law of D: chunks 1328..1335 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_1328 : slawChunk 1328 = true := by decide +kernel
theorem slawChunk_1329 : slawChunk 1329 = true := by decide +kernel
theorem slawChunk_1330 : slawChunk 1330 = true := by decide +kernel
theorem slawChunk_1331 : slawChunk 1331 = true := by decide +kernel
theorem slawChunk_1332 : slawChunk 1332 = true := by decide +kernel
theorem slawChunk_1333 : slawChunk 1333 = true := by decide +kernel
theorem slawChunk_1334 : slawChunk 1334 = true := by decide +kernel
theorem slawChunk_1335 : slawChunk 1335 = true := by decide +kernel
theorem slawC_166 (k : Nat) (h1 : 1328 ≤ k) (h2 : k < 1336) : slawChunk k = true := by
  if e1328 : k = 1328 then subst e1328; exact slawChunk_1328 else
  if e1329 : k = 1329 then subst e1329; exact slawChunk_1329 else
  if e1330 : k = 1330 then subst e1330; exact slawChunk_1330 else
  if e1331 : k = 1331 then subst e1331; exact slawChunk_1331 else
  if e1332 : k = 1332 then subst e1332; exact slawChunk_1332 else
  if e1333 : k = 1333 then subst e1333; exact slawChunk_1333 else
  if e1334 : k = 1334 then subst e1334; exact slawChunk_1334 else
  if e1335 : k = 1335 then subst e1335; exact slawChunk_1335 else
  omega
end D2
