import Ski.D2Base
import Ski.D2K.S241
/-! Generated.  S-law of D: chunks 1936..1943 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_1936 : slawChunk 1936 = true := by decide +kernel
theorem slawChunk_1937 : slawChunk 1937 = true := by decide +kernel
theorem slawChunk_1938 : slawChunk 1938 = true := by decide +kernel
theorem slawChunk_1939 : slawChunk 1939 = true := by decide +kernel
theorem slawChunk_1940 : slawChunk 1940 = true := by decide +kernel
theorem slawChunk_1941 : slawChunk 1941 = true := by decide +kernel
theorem slawChunk_1942 : slawChunk 1942 = true := by decide +kernel
theorem slawChunk_1943 : slawChunk 1943 = true := by decide +kernel
theorem slawC_242 (k : Nat) (h1 : 1936 ≤ k) (h2 : k < 1944) : slawChunk k = true := by
  if e1936 : k = 1936 then subst e1936; exact slawChunk_1936 else
  if e1937 : k = 1937 then subst e1937; exact slawChunk_1937 else
  if e1938 : k = 1938 then subst e1938; exact slawChunk_1938 else
  if e1939 : k = 1939 then subst e1939; exact slawChunk_1939 else
  if e1940 : k = 1940 then subst e1940; exact slawChunk_1940 else
  if e1941 : k = 1941 then subst e1941; exact slawChunk_1941 else
  if e1942 : k = 1942 then subst e1942; exact slawChunk_1942 else
  if e1943 : k = 1943 then subst e1943; exact slawChunk_1943 else
  omega
end D2
