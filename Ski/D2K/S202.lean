import Ski.D2Base
import Ski.D2K.S201
/-! Generated.  S-law of D: chunks 1616..1623 (chunk k = row k / 8, columns 47 (k % 8) + [0, 47)). -/
namespace D2
theorem slawChunk_1616 : slawChunk 1616 = true := by decide +kernel
theorem slawChunk_1617 : slawChunk 1617 = true := by decide +kernel
theorem slawChunk_1618 : slawChunk 1618 = true := by decide +kernel
theorem slawChunk_1619 : slawChunk 1619 = true := by decide +kernel
theorem slawChunk_1620 : slawChunk 1620 = true := by decide +kernel
theorem slawChunk_1621 : slawChunk 1621 = true := by decide +kernel
theorem slawChunk_1622 : slawChunk 1622 = true := by decide +kernel
theorem slawChunk_1623 : slawChunk 1623 = true := by decide +kernel
theorem slawC_202 (k : Nat) (h1 : 1616 ≤ k) (h2 : k < 1624) : slawChunk k = true := by
  if e1616 : k = 1616 then subst e1616; exact slawChunk_1616 else
  if e1617 : k = 1617 then subst e1617; exact slawChunk_1617 else
  if e1618 : k = 1618 then subst e1618; exact slawChunk_1618 else
  if e1619 : k = 1619 then subst e1619; exact slawChunk_1619 else
  if e1620 : k = 1620 then subst e1620; exact slawChunk_1620 else
  if e1621 : k = 1621 then subst e1621; exact slawChunk_1621 else
  if e1622 : k = 1622 then subst e1622; exact slawChunk_1622 else
  if e1623 : k = 1623 then subst e1623; exact slawChunk_1623 else
  omega
end D2
