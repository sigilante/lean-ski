import Ski.D2Base
import Ski.D2K.S269
/-! Generated.  S-law of D: chunks 2160..2167 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_2160 : slawChunk 2160 = true := by decide +kernel
theorem slawChunk_2161 : slawChunk 2161 = true := by decide +kernel
theorem slawChunk_2162 : slawChunk 2162 = true := by decide +kernel
theorem slawChunk_2163 : slawChunk 2163 = true := by decide +kernel
theorem slawChunk_2164 : slawChunk 2164 = true := by decide +kernel
theorem slawChunk_2165 : slawChunk 2165 = true := by decide +kernel
theorem slawChunk_2166 : slawChunk 2166 = true := by decide +kernel
theorem slawChunk_2167 : slawChunk 2167 = true := by decide +kernel
theorem slawC_270 (k : Nat) (h1 : 2160 ≤ k) (h2 : k < 2168) : slawChunk k = true := by
  if e2160 : k = 2160 then subst e2160; exact slawChunk_2160 else
  if e2161 : k = 2161 then subst e2161; exact slawChunk_2161 else
  if e2162 : k = 2162 then subst e2162; exact slawChunk_2162 else
  if e2163 : k = 2163 then subst e2163; exact slawChunk_2163 else
  if e2164 : k = 2164 then subst e2164; exact slawChunk_2164 else
  if e2165 : k = 2165 then subst e2165; exact slawChunk_2165 else
  if e2166 : k = 2166 then subst e2166; exact slawChunk_2166 else
  if e2167 : k = 2167 then subst e2167; exact slawChunk_2167 else
  omega
end D2
