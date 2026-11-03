import Ski.ProbeTree

/-!
# A probe tree as words

`lake exe jets plan` and `check-probe`, `lake exe circuit compare-probe`
and ski-air's probe commands take the output they bind as words: `err`,
or `val` and the stack's numbers, the probe trees of SKIlark's outcomes
(`Probe.toV`).  A tree that is none of those, such as the tree of another
language's value encoding, is given literally: `tree`, then its nodes in
preorder, each `c k n` for `V.node c k ch` with `n = ch.length`, every
number in plain decimal and `c < k`.  So one tree has one spelling, and
the plan is `Air.planOf` of the tree as written: the soundness theorems,
generic in the tree (`Air.air_probe_sound`,
`Circuit.probeExport_sound_tree`), apply to it as they are.
-/

namespace Probe

/-- A number in plain decimal: digits only, no leading zero. -/
def decimalWord (w : String) : Option Nat :=
  if !w.isEmpty && w.all Char.isDigit && (w == "0" || w.front != '0') then w.toNat? else none

mutual
  /-- A tree's words: preorder, each node `c k n`. -/
  def vWords : V → List String
    | .node c k ch => toString c :: toString k :: toString ch.length :: vsWords ch
  /-- The words of a list of trees, in order. -/
  def vsWords : List V → List String
    | [] => []
    | v :: vs => vWords v ++ vsWords vs
end

/-- `n` trees from the front of the words, with the words after them.
    `fuel` bounds the recursion; a node is three words, so the words'
    length is enough. -/
def vsOfWords : Nat → Nat → List String → Option (List V × List String)
  | _, 0, ws => some ([], ws)
  | 0, _ + 1, _ => none
  | fuel + 1, n + 1, c :: k :: m :: ws => do
    let c ← decimalWord c
    let k ← decimalWord k
    let m ← decimalWord m
    if k ≤ c then none
    let (ch, ws) ← vsOfWords fuel m ws
    let (vs, ws) ← vsOfWords fuel n ws
    some (.node c k ch :: vs, ws)
  | _ + 1, _ + 1, _ => none

/-- The tree the words spell, all of them, or none. -/
def vOfWords (ws : List String) : Option V :=
  match vsOfWords ws.length 1 ws with
  | some ([v], []) => some v
  | _ => none

end Probe
