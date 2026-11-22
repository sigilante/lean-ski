import Ski.D2Base
import Ski.D2K.S100
/-! Generated.  S-law of D: chunks 808..815 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_808 : slawChunk 808 = true := by decide +kernel
theorem slawChunk_809 : slawChunk 809 = true := by decide +kernel
theorem slawChunk_810 : slawChunk 810 = true := by decide +kernel
theorem slawChunk_811 : slawChunk 811 = true := by decide +kernel
theorem slawChunk_812 : slawChunk 812 = true := by decide +kernel
theorem slawChunk_813 : slawChunk 813 = true := by decide +kernel
theorem slawChunk_814 : slawChunk 814 = true := by decide +kernel
theorem slawChunk_815 : slawChunk 815 = true := by decide +kernel
theorem slawC_101 (k : Nat) (h1 : 808 ≤ k) (h2 : k < 816) : slawChunk k = true := by
  if e808 : k = 808 then subst e808; exact slawChunk_808 else
  if e809 : k = 809 then subst e809; exact slawChunk_809 else
  if e810 : k = 810 then subst e810; exact slawChunk_810 else
  if e811 : k = 811 then subst e811; exact slawChunk_811 else
  if e812 : k = 812 then subst e812; exact slawChunk_812 else
  if e813 : k = 813 then subst e813; exact slawChunk_813 else
  if e814 : k = 814 then subst e814; exact slawChunk_814 else
  if e815 : k = 815 then subst e815; exact slawChunk_815 else
  omega
end D2
