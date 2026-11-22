import Ski.D2Base
import Ski.D2K.S86
/-! Generated.  S-law of D: chunks 696..703 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_696 : slawChunk 696 = true := by decide +kernel
theorem slawChunk_697 : slawChunk 697 = true := by decide +kernel
theorem slawChunk_698 : slawChunk 698 = true := by decide +kernel
theorem slawChunk_699 : slawChunk 699 = true := by decide +kernel
theorem slawChunk_700 : slawChunk 700 = true := by decide +kernel
theorem slawChunk_701 : slawChunk 701 = true := by decide +kernel
theorem slawChunk_702 : slawChunk 702 = true := by decide +kernel
theorem slawChunk_703 : slawChunk 703 = true := by decide +kernel
theorem slawC_87 (k : Nat) (h1 : 696 ≤ k) (h2 : k < 704) : slawChunk k = true := by
  if e696 : k = 696 then subst e696; exact slawChunk_696 else
  if e697 : k = 697 then subst e697; exact slawChunk_697 else
  if e698 : k = 698 then subst e698; exact slawChunk_698 else
  if e699 : k = 699 then subst e699; exact slawChunk_699 else
  if e700 : k = 700 then subst e700; exact slawChunk_700 else
  if e701 : k = 701 then subst e701; exact slawChunk_701 else
  if e702 : k = 702 then subst e702; exact slawChunk_702 else
  if e703 : k = 703 then subst e703; exact slawChunk_703 else
  omega
end D2
