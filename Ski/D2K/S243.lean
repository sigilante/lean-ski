import Ski.D2Base
import Ski.D2K.S242
/-! Generated.  S-law of D: chunks 1944..1951 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_1944 : slawChunk 1944 = true := by decide +kernel
theorem slawChunk_1945 : slawChunk 1945 = true := by decide +kernel
theorem slawChunk_1946 : slawChunk 1946 = true := by decide +kernel
theorem slawChunk_1947 : slawChunk 1947 = true := by decide +kernel
theorem slawChunk_1948 : slawChunk 1948 = true := by decide +kernel
theorem slawChunk_1949 : slawChunk 1949 = true := by decide +kernel
theorem slawChunk_1950 : slawChunk 1950 = true := by decide +kernel
theorem slawChunk_1951 : slawChunk 1951 = true := by decide +kernel
theorem slawC_243 (k : Nat) (h1 : 1944 ≤ k) (h2 : k < 1952) : slawChunk k = true := by
  if e1944 : k = 1944 then subst e1944; exact slawChunk_1944 else
  if e1945 : k = 1945 then subst e1945; exact slawChunk_1945 else
  if e1946 : k = 1946 then subst e1946; exact slawChunk_1946 else
  if e1947 : k = 1947 then subst e1947; exact slawChunk_1947 else
  if e1948 : k = 1948 then subst e1948; exact slawChunk_1948 else
  if e1949 : k = 1949 then subst e1949; exact slawChunk_1949 else
  if e1950 : k = 1950 then subst e1950; exact slawChunk_1950 else
  if e1951 : k = 1951 then subst e1951; exact slawChunk_1951 else
  omega
end D2
