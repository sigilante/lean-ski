import Ski.D2Base
import Ski.D2K.S259
/-! Generated.  S-law of D: chunks 2080..2087 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_2080 : slawChunk 2080 = true := by decide +kernel
theorem slawChunk_2081 : slawChunk 2081 = true := by decide +kernel
theorem slawChunk_2082 : slawChunk 2082 = true := by decide +kernel
theorem slawChunk_2083 : slawChunk 2083 = true := by decide +kernel
theorem slawChunk_2084 : slawChunk 2084 = true := by decide +kernel
theorem slawChunk_2085 : slawChunk 2085 = true := by decide +kernel
theorem slawChunk_2086 : slawChunk 2086 = true := by decide +kernel
theorem slawChunk_2087 : slawChunk 2087 = true := by decide +kernel
theorem slawC_260 (k : Nat) (h1 : 2080 ≤ k) (h2 : k < 2088) : slawChunk k = true := by
  if e2080 : k = 2080 then subst e2080; exact slawChunk_2080 else
  if e2081 : k = 2081 then subst e2081; exact slawChunk_2081 else
  if e2082 : k = 2082 then subst e2082; exact slawChunk_2082 else
  if e2083 : k = 2083 then subst e2083; exact slawChunk_2083 else
  if e2084 : k = 2084 then subst e2084; exact slawChunk_2084 else
  if e2085 : k = 2085 then subst e2085; exact slawChunk_2085 else
  if e2086 : k = 2086 then subst e2086; exact slawChunk_2086 else
  if e2087 : k = 2087 then subst e2087; exact slawChunk_2087 else
  omega
end D2
