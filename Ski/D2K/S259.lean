import Ski.D2Base
import Ski.D2K.S258
/-! Generated.  S-law of D: chunks 2072..2079 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_2072 : slawChunk 2072 = true := by decide +kernel
theorem slawChunk_2073 : slawChunk 2073 = true := by decide +kernel
theorem slawChunk_2074 : slawChunk 2074 = true := by decide +kernel
theorem slawChunk_2075 : slawChunk 2075 = true := by decide +kernel
theorem slawChunk_2076 : slawChunk 2076 = true := by decide +kernel
theorem slawChunk_2077 : slawChunk 2077 = true := by decide +kernel
theorem slawChunk_2078 : slawChunk 2078 = true := by decide +kernel
theorem slawChunk_2079 : slawChunk 2079 = true := by decide +kernel
theorem slawC_259 (k : Nat) (h1 : 2072 ≤ k) (h2 : k < 2080) : slawChunk k = true := by
  if e2072 : k = 2072 then subst e2072; exact slawChunk_2072 else
  if e2073 : k = 2073 then subst e2073; exact slawChunk_2073 else
  if e2074 : k = 2074 then subst e2074; exact slawChunk_2074 else
  if e2075 : k = 2075 then subst e2075; exact slawChunk_2075 else
  if e2076 : k = 2076 then subst e2076; exact slawChunk_2076 else
  if e2077 : k = 2077 then subst e2077; exact slawChunk_2077 else
  if e2078 : k = 2078 then subst e2078; exact slawChunk_2078 else
  if e2079 : k = 2079 then subst e2079; exact slawChunk_2079 else
  omega
end D2
