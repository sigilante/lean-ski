import Ski.D2Base
import Ski.D2K.S118
/-! Generated.  S-law of D: chunks 952..959 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_952 : slawChunk 952 = true := by decide +kernel
theorem slawChunk_953 : slawChunk 953 = true := by decide +kernel
theorem slawChunk_954 : slawChunk 954 = true := by decide +kernel
theorem slawChunk_955 : slawChunk 955 = true := by decide +kernel
theorem slawChunk_956 : slawChunk 956 = true := by decide +kernel
theorem slawChunk_957 : slawChunk 957 = true := by decide +kernel
theorem slawChunk_958 : slawChunk 958 = true := by decide +kernel
theorem slawChunk_959 : slawChunk 959 = true := by decide +kernel
theorem slawC_119 (k : Nat) (h1 : 952 ≤ k) (h2 : k < 960) : slawChunk k = true := by
  if e952 : k = 952 then subst e952; exact slawChunk_952 else
  if e953 : k = 953 then subst e953; exact slawChunk_953 else
  if e954 : k = 954 then subst e954; exact slawChunk_954 else
  if e955 : k = 955 then subst e955; exact slawChunk_955 else
  if e956 : k = 956 then subst e956; exact slawChunk_956 else
  if e957 : k = 957 then subst e957; exact slawChunk_957 else
  if e958 : k = 958 then subst e958; exact slawChunk_958 else
  if e959 : k = 959 then subst e959; exact slawChunk_959 else
  omega
end D2
