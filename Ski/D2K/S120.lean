import Ski.D2Base
import Ski.D2K.S119
/-! Generated.  S-law of D: chunks 960..967 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_960 : slawChunk 960 = true := by decide +kernel
theorem slawChunk_961 : slawChunk 961 = true := by decide +kernel
theorem slawChunk_962 : slawChunk 962 = true := by decide +kernel
theorem slawChunk_963 : slawChunk 963 = true := by decide +kernel
theorem slawChunk_964 : slawChunk 964 = true := by decide +kernel
theorem slawChunk_965 : slawChunk 965 = true := by decide +kernel
theorem slawChunk_966 : slawChunk 966 = true := by decide +kernel
theorem slawChunk_967 : slawChunk 967 = true := by decide +kernel
theorem slawC_120 (k : Nat) (h1 : 960 ≤ k) (h2 : k < 968) : slawChunk k = true := by
  if e960 : k = 960 then subst e960; exact slawChunk_960 else
  if e961 : k = 961 then subst e961; exact slawChunk_961 else
  if e962 : k = 962 then subst e962; exact slawChunk_962 else
  if e963 : k = 963 then subst e963; exact slawChunk_963 else
  if e964 : k = 964 then subst e964; exact slawChunk_964 else
  if e965 : k = 965 then subst e965; exact slawChunk_965 else
  if e966 : k = 966 then subst e966; exact slawChunk_966 else
  if e967 : k = 967 then subst e967; exact slawChunk_967 else
  omega
end D2
