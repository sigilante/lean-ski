import Ski.D2Base
import Ski.D2K.S277
/-! Generated.  S-law of D: chunks 2224..2231 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_2224 : slawChunk 2224 = true := by decide +kernel
theorem slawChunk_2225 : slawChunk 2225 = true := by decide +kernel
theorem slawChunk_2226 : slawChunk 2226 = true := by decide +kernel
theorem slawChunk_2227 : slawChunk 2227 = true := by decide +kernel
theorem slawChunk_2228 : slawChunk 2228 = true := by decide +kernel
theorem slawChunk_2229 : slawChunk 2229 = true := by decide +kernel
theorem slawChunk_2230 : slawChunk 2230 = true := by decide +kernel
theorem slawChunk_2231 : slawChunk 2231 = true := by decide +kernel
theorem slawC_278 (k : Nat) (h1 : 2224 ≤ k) (h2 : k < 2232) : slawChunk k = true := by
  if e2224 : k = 2224 then subst e2224; exact slawChunk_2224 else
  if e2225 : k = 2225 then subst e2225; exact slawChunk_2225 else
  if e2226 : k = 2226 then subst e2226; exact slawChunk_2226 else
  if e2227 : k = 2227 then subst e2227; exact slawChunk_2227 else
  if e2228 : k = 2228 then subst e2228; exact slawChunk_2228 else
  if e2229 : k = 2229 then subst e2229; exact slawChunk_2229 else
  if e2230 : k = 2230 then subst e2230; exact slawChunk_2230 else
  if e2231 : k = 2231 then subst e2231; exact slawChunk_2231 else
  omega
end D2
