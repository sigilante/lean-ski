import Ski.D2Base
import Ski.D2K.S196
/-! Generated.  S-law of D: chunks 1576..1583 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_1576 : slawChunk 1576 = true := by decide +kernel
theorem slawChunk_1577 : slawChunk 1577 = true := by decide +kernel
theorem slawChunk_1578 : slawChunk 1578 = true := by decide +kernel
theorem slawChunk_1579 : slawChunk 1579 = true := by decide +kernel
theorem slawChunk_1580 : slawChunk 1580 = true := by decide +kernel
theorem slawChunk_1581 : slawChunk 1581 = true := by decide +kernel
theorem slawChunk_1582 : slawChunk 1582 = true := by decide +kernel
theorem slawChunk_1583 : slawChunk 1583 = true := by decide +kernel
theorem slawC_197 (k : Nat) (h1 : 1576 ≤ k) (h2 : k < 1584) : slawChunk k = true := by
  if e1576 : k = 1576 then subst e1576; exact slawChunk_1576 else
  if e1577 : k = 1577 then subst e1577; exact slawChunk_1577 else
  if e1578 : k = 1578 then subst e1578; exact slawChunk_1578 else
  if e1579 : k = 1579 then subst e1579; exact slawChunk_1579 else
  if e1580 : k = 1580 then subst e1580; exact slawChunk_1580 else
  if e1581 : k = 1581 then subst e1581; exact slawChunk_1581 else
  if e1582 : k = 1582 then subst e1582; exact slawChunk_1582 else
  if e1583 : k = 1583 then subst e1583; exact slawChunk_1583 else
  omega
end D2
