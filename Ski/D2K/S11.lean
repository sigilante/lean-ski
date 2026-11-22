import Ski.D2Base
import Ski.D2K.S10
/-! Generated.  S-law of D: chunks 88..95 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_88 : slawChunk 88 = true := by decide +kernel
theorem slawChunk_89 : slawChunk 89 = true := by decide +kernel
theorem slawChunk_90 : slawChunk 90 = true := by decide +kernel
theorem slawChunk_91 : slawChunk 91 = true := by decide +kernel
theorem slawChunk_92 : slawChunk 92 = true := by decide +kernel
theorem slawChunk_93 : slawChunk 93 = true := by decide +kernel
theorem slawChunk_94 : slawChunk 94 = true := by decide +kernel
theorem slawChunk_95 : slawChunk 95 = true := by decide +kernel
theorem slawC_11 (k : Nat) (h1 : 88 ≤ k) (h2 : k < 96) : slawChunk k = true := by
  if e88 : k = 88 then subst e88; exact slawChunk_88 else
  if e89 : k = 89 then subst e89; exact slawChunk_89 else
  if e90 : k = 90 then subst e90; exact slawChunk_90 else
  if e91 : k = 91 then subst e91; exact slawChunk_91 else
  if e92 : k = 92 then subst e92; exact slawChunk_92 else
  if e93 : k = 93 then subst e93; exact slawChunk_93 else
  if e94 : k = 94 then subst e94; exact slawChunk_94 else
  if e95 : k = 95 then subst e95; exact slawChunk_95 else
  omega
end D2
