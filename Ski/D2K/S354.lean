import Ski.D2Base
import Ski.D2K.S353
/-! Generated.  S-law of D: chunks 2832..2839 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_2832 : slawChunk 2832 = true := by decide +kernel
theorem slawChunk_2833 : slawChunk 2833 = true := by decide +kernel
theorem slawChunk_2834 : slawChunk 2834 = true := by decide +kernel
theorem slawChunk_2835 : slawChunk 2835 = true := by decide +kernel
theorem slawChunk_2836 : slawChunk 2836 = true := by decide +kernel
theorem slawChunk_2837 : slawChunk 2837 = true := by decide +kernel
theorem slawChunk_2838 : slawChunk 2838 = true := by decide +kernel
theorem slawChunk_2839 : slawChunk 2839 = true := by decide +kernel
theorem slawC_354 (k : Nat) (h1 : 2832 ≤ k) (h2 : k < 2840) : slawChunk k = true := by
  if e2832 : k = 2832 then subst e2832; exact slawChunk_2832 else
  if e2833 : k = 2833 then subst e2833; exact slawChunk_2833 else
  if e2834 : k = 2834 then subst e2834; exact slawChunk_2834 else
  if e2835 : k = 2835 then subst e2835; exact slawChunk_2835 else
  if e2836 : k = 2836 then subst e2836; exact slawChunk_2836 else
  if e2837 : k = 2837 then subst e2837; exact slawChunk_2837 else
  if e2838 : k = 2838 then subst e2838; exact slawChunk_2838 else
  if e2839 : k = 2839 then subst e2839; exact slawChunk_2839 else
  omega
end D2
