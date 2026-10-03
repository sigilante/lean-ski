import Ski.ComposedText
import Ski.ComposedO
import Ski.Predicate
import Ski.BitArith
import Ski.ZK.Poseidon2

/-!
# A composed statement with the Poseidon2 jet: a preimage

`p2pre h`: "I know sixteen 31-bit values whose Poseidon2 permutation
begins with `h`."  The values are the statement's 496 private bits, a comb
of 496 leaves (`combBT 496`), and the region is one cell the verifier does
not read.  The verifier is an open term with the jet's variable `JP2` free:

  `V = λ β w. J ⬝ CHECK_h ⬝ β`

- Bracket abstraction makes `V` the term `S (K K) (J ⬝ CHECK_h)`, so the
  jet receives the comb's root itself, the cell the statement names
  (`CompM.combRoot`), not a thunk of it.  The jet reads the bits from
  their slots and passes the permutation's 496 output bits to `CHECK_h`.
- `CHECK_h` reads the outputs' bits one at a time: the first 31 must be
  `h`'s, least significant first; then it absorbs the other 465 and is `K`
  (`checkO`; tested on runs, not proved).  A wrong bit hands the rest to
  `Θ K`, which absorbs every argument and never becomes `K`
  (`P2Pre.chk_sound`).

`Circuit.compPExport_sound` makes an accepted proof of this statement's
circuit a proof that `V`, with `J` closed to `Poseidon2SKI.Pcomb`,
evaluates to `K` on the bits the memory holds; `Circuit.p2preExport_sound`
reads that as a preimage: the bits' elements permute to a state beginning
with `h`.  The text `public.txt` is `publicTextP`; its header names `h`, the
jet's atom and the comb's root.  `statementOfTextP` parses it back only
when it is exactly that text.
-/

namespace ComposedPText

open Compose CompM ComposedText

/-- The jet's atom: above every bit slot and below the circuit's `2^24`. -/
def JP2 : Nat := 2 ^ 23

/-- `Θ K`: absorbs every argument and never becomes `K`. -/
def badO : OTerm := BitArith.thetaT.toO ⬝ₒ .K

/-- `[x₁ … xₘ] K`. -/
def absorbO : Nat → OTerm
  | 0 => .K
  | m + 1 => .K ⬝ₒ absorbO m

/-- Read bits equal to `es`, then absorb `m` more and be `K`. -/
def chkO : List Bool → Nat → OTerm
  | [], m => absorbO m
  | e :: es, m =>
    absN [0] (.var 0 ⬝ₒ (if e then chkO es m else badO) ⬝ₒ (if e then badO else chkO es m))

/-- The continuation: the first output is `h`. -/
def checkO (h : Nat) : OTerm := chkO (BitArith.bitsOf 31 h) 465

/-- **The verifier**: `λ β w. J ⬝ CHECK_h ⬝ β`. -/
def verifierO (h : Nat) : OTerm :=
  absN [0, 1] (.var JP2 ⬝ₒ checkO h ⬝ₒ .var 0)

/-- The statement's shape, verifiers and region. -/
def shpP : BT := CompM.combBT 496
def VsP (h : Nat) : List OTerm := [verifierO h]
def regionP : List Cell := [.S]

/-- The comb's root: the same for every filling (`CompM.combRoot_public`). -/
def rootP : Nat := combRoot (fun _ => false) shpP regionP

/-- The log heights a statement names: the CPU, the memory, and the jet's
    three tables (input bits, output bits, permutations). -/
structure PLogs where
  rows : Nat
  mem : Nat
  pin : Nat
  pout : Nat
  p2 : Nat
  deriving BEq, Repr

def plogsOK (l : PLogs) : Bool :=
  [l.rows, l.mem, l.pin, l.pout, l.p2].all fun x => 8 ≤ x && x ≤ 20

/-- **The statement** `p2pre h`: the composed machine of the open verifier,
    the bit cells and the region blank. -/
def publicTextP (h : Nat) (lg : PLogs) : String := Id.run do
  let N := BT.nleaves shpP
  let m := cMachineO (fun _ => false) shpP regionP (VsP h)
  let roots := (cHeapO (fun _ => false) shpP regionP (VsP h)).2
  let mut s := s!"p2pre {h} {JP2} {rootP}\nW {regionP.length}\nlog {lg.rows} {lg.mem} {lg.pin} {lg.pout} {lg.p2}\nbits {N}\nroots {" ".intercalate (roots.map toString)}\nnil {m.stk}\n{m.hd} {m.stk} {m.heap.length}\n"
  let mut i := 0
  for c in m.heap do
    s := s ++ (if 3 ≤ i && i < N + 3 + regionP.length then "W" else cellText c) ++ "\n"
    i := i + 1
  return s

/-- The statement, parsed back only when it is exactly `publicTextP`'s text. -/
def statementOfTextP (text : String) : Option (Nat × PLogs) := do
  let ls := text.splitOn "\n"
  let h ← match words (ls.getD 0 "") with
    | ["p2pre", h, j, r] => if j == toString JP2 && r == toString rootP then h.toNat? else none
    | _ => none
  let lg ← match words (ls.getD 2 "") with
    | ["log", r, m, a, b, c] => do some ⟨← r.toNat?, ← m.toNat?, ← a.toNat?, ← b.toNat?, ← c.toNat?⟩
    | _ => none
  if h < Poseidon2.p && plogsOK lg && text == publicTextP h lg then some (h, lg) else none

end ComposedPText
