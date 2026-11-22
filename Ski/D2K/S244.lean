import Ski.D2Base
import Ski.D2K.S243
/-! Generated.  S-law of D: chunks 1952..1959 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_1952 : slawChunk 1952 = true := by decide +kernel
theorem slawChunk_1953 : slawChunk 1953 = true := by decide +kernel
theorem slawChunk_1954 : slawChunk 1954 = true := by decide +kernel
theorem slawChunk_1955 : slawChunk 1955 = true := by decide +kernel
theorem slawChunk_1956 : slawChunk 1956 = true := by decide +kernel
theorem slawChunk_1957 : slawChunk 1957 = true := by decide +kernel
theorem slawChunk_1958 : slawChunk 1958 = true := by decide +kernel
theorem slawChunk_1959 : slawChunk 1959 = true := by decide +kernel
theorem slawC_244 (k : Nat) (h1 : 1952 ≤ k) (h2 : k < 1960) : slawChunk k = true := by
  if e1952 : k = 1952 then subst e1952; exact slawChunk_1952 else
  if e1953 : k = 1953 then subst e1953; exact slawChunk_1953 else
  if e1954 : k = 1954 then subst e1954; exact slawChunk_1954 else
  if e1955 : k = 1955 then subst e1955; exact slawChunk_1955 else
  if e1956 : k = 1956 then subst e1956; exact slawChunk_1956 else
  if e1957 : k = 1957 then subst e1957; exact slawChunk_1957 else
  if e1958 : k = 1958 then subst e1958; exact slawChunk_1958 else
  if e1959 : k = 1959 then subst e1959; exact slawChunk_1959 else
  omega
end D2
