import Ski.D2Base
import Ski.D2K.S109
/-! Generated.  S-law of D: chunks 880..887 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_880 : slawChunk 880 = true := by decide +kernel
theorem slawChunk_881 : slawChunk 881 = true := by decide +kernel
theorem slawChunk_882 : slawChunk 882 = true := by decide +kernel
theorem slawChunk_883 : slawChunk 883 = true := by decide +kernel
theorem slawChunk_884 : slawChunk 884 = true := by decide +kernel
theorem slawChunk_885 : slawChunk 885 = true := by decide +kernel
theorem slawChunk_886 : slawChunk 886 = true := by decide +kernel
theorem slawChunk_887 : slawChunk 887 = true := by decide +kernel
theorem slawC_110 (k : Nat) (h1 : 880 ≤ k) (h2 : k < 888) : slawChunk k = true := by
  if e880 : k = 880 then subst e880; exact slawChunk_880 else
  if e881 : k = 881 then subst e881; exact slawChunk_881 else
  if e882 : k = 882 then subst e882; exact slawChunk_882 else
  if e883 : k = 883 then subst e883; exact slawChunk_883 else
  if e884 : k = 884 then subst e884; exact slawChunk_884 else
  if e885 : k = 885 then subst e885; exact slawChunk_885 else
  if e886 : k = 886 then subst e886; exact slawChunk_886 else
  if e887 : k = 887 then subst e887; exact slawChunk_887 else
  omega
end D2
