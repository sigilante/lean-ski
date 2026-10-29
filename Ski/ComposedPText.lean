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

/-- The second jet's atom: the jet on the stack, its inputs a previous
    call's outputs (`P2Jet.p2RowS`). -/
def JP2S : Nat := JP2 + 1

/-- **The chain's verifier**: `λ β w. J ⬝ (J₂ ⬝ CHECK_h) ⬝ β`.  The first
    call's outputs land on the stack under `CHECK_h`, with `J₂` at the head,
    which permutes them again (`Ski/P2Chain.lean`). -/
def verifierChainO (h : Nat) : OTerm :=
  absN [0, 1] (.var JP2 ⬝ₒ (.var JP2S ⬝ₒ checkO h) ⬝ₒ .var 0)

/-- The statement's shape, verifiers and region. -/
def shpP : BT := CompM.combBT 496
def VsP (h : Nat) : List OTerm := [verifierO h]
def VsC (h : Nat) : List OTerm := [verifierChainO h]
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
  [l.rows, l.mem, l.pin, l.pout, l.p2].all fun x => 9 ≤ x && x ≤ 20

-- ---------------------------------------------------------------------------
-- A committed value: `p2commit c pat`
-- ---------------------------------------------------------------------------

/-- `[x₁ … xₘ] F`: absorb `m` arguments, then be `F`. -/
def absorbX : Nat → OTerm → OTerm
  | 0, F => F
  | m + 1, F => .K ⬝ₒ absorbX m F

/-- Read bits equal to `es`, then be `F`; a wrong bit hands the rest to
    `Θ K`. -/
def chkX : List Bool → OTerm → OTerm
  | [], F => F
  | e :: es, F =>
    absN [0] (.var 0 ⬝ₒ (if e then chkX es F else badO) ⬝ₒ (if e then badO else chkX es F))

/-- A pattern's test of one bit `a`: none passes it to `X`, a required bit
    selects `X` only when `a` is it. -/
def selO : Option Bool → OTerm → OTerm → OTerm
  | none, _, X => X
  | some true, a, X => a ⬝ₒ X ⬝ₒ badO
  | some false, a, X => a ⬝ₒ badO ⬝ₒ X

/-- **A pattern's check over a comb**: each leaf against its entry, then
    `K`.  The comb `combT (b :: bs)` passes its leaf and its rest to a
    function. -/
def patO : List (Option Bool) → OTerm
  | [] => .K
  | [p] => absN [0] (selO p (.var 0) .K)
  | p :: q :: ps => absN [0] (.var 0 ⬝ₒ absN [1, 2] (selO p (.var 1) (patO (q :: ps) ⬝ₒ .var 2)))

/-- The bits of eight 31-bit elements, least significant first. -/
def cbits (c : List Nat) : List Bool := c.flatMap (BitArith.bitsOf 31)

/-- The continuation of `p2commit c pat`: the first eight outputs are `c`;
    the other eight are absorbed; then the argument after them, the
    pattern's check of the comb, is the result. -/
def checkC (c : List Nat) : OTerm := chkX (cbits c) (absorbX 248 .I)

/-- **The verifier of `p2commit c pat`**: `λ β w. J ⬝ CHECK_c ⬝ β ⬝ (PAT ⬝ β)`.
    Bracket abstraction makes it `S (K K) (S (J ⬝ CHECK_c) PAT)`, so the jet
    receives the comb's root itself and, past its two arguments, the
    pattern's check of the comb. -/
def verifierC (c : List Nat) (pat : List (Option Bool)) : OTerm :=
  absN [100, 101] (.var JP2 ⬝ₒ checkC c ⬝ₒ .var 100 ⬝ₒ (patO pat ⬝ₒ .var 100))

-- ---------------------------------------------------------------------------
-- The statements
-- ---------------------------------------------------------------------------

/-- **A statement with the Poseidon2 jet**, over 496 private bits: the
    preimage `p2pre h`, the committed value `p2commit c pat` ("a value
    and randomness of 248 bits each that compress to `c`, the 496 bits
    meeting `pat`"), or the chain `p2chain h` ("sixteen values whose
    permutation, permuted again, begins with `h`": two jet calls). -/
inductive PStmt
  | pre (h : Nat)
  | commit (c : List Nat) (pat : List (Option Bool))
  | chain (h : Nat)
  deriving BEq, Repr

def PStmt.Vs : PStmt → List OTerm
  | .pre h => VsP h
  | .commit c pat => [verifierC c pat]
  | .chain h => VsC h

def patChar : Option Bool → Char
  | none => '.'
  | some true => '1'
  | some false => '0'

def charPat : Char → Option (Option Bool)
  | '.' => some none
  | '1' => some (some true)
  | '0' => some (some false)
  | _ => none

/-- The header's words before the jet's atom and the root. -/
def PStmt.head : PStmt → String
  | .pre h => s!"p2pre {h}"
  | .commit c pat => s!"p2commit {" ".intercalate (c.map toString)} {String.ofList (pat.map patChar)}"
  | .chain h => s!"p2chain {h}"

/-- A statement's text is valid: `h` below `p`; eight elements of `c` below
    `p` and 496 pattern entries. -/
def PStmt.ok : PStmt → Bool
  | .pre h => decide (h < Poseidon2.p)
  | .commit c pat => c.length == 8 && c.all (· < Poseidon2.p) && pat.length == 496
  | .chain h => decide (h < Poseidon2.p)

/-- **The statement's text**: the composed machine of the open verifiers,
    the bit cells and the region blank. -/
def publicTextG (st : PStmt) (lg : PLogs) : String := Id.run do
  let N := BT.nleaves shpP
  let m := cMachineO (fun _ => false) shpP regionP st.Vs
  let roots := (cHeapO (fun _ => false) shpP regionP st.Vs).2
  let mut s := s!"{st.head} {JP2} {rootP}\nW {regionP.length}\nlog {lg.rows} {lg.mem} {lg.pin} {lg.pout} {lg.p2}\nbits {N}\nroots {" ".intercalate (roots.map toString)}\nnil {m.stk}\n{m.hd} {m.stk} {m.heap.length}\n"
  let mut i := 0
  for c in m.heap do
    s := s ++ (if 3 ≤ i && i < N + 3 + regionP.length then "W" else cellText c) ++ "\n"
    i := i + 1
  return s

/-- **The statement** `p2pre h`. -/
def publicTextP (h : Nat) (lg : PLogs) : String := publicTextG (.pre h) lg

/-- The statement, parsed back only when it is exactly `publicTextG`'s text
    of a valid statement. -/
def statementOfTextG (text : String) : Option (PStmt × PLogs) := do
  let ls := text.splitOn "\n"
  let st ← match words (ls.getD 0 "") with
    | ["p2pre", h, j, r] => if j == toString JP2 && r == toString rootP then (h.toNat?).map .pre else none
    | ["p2chain", h, j, r] => if j == toString JP2 && r == toString rootP then (h.toNat?).map .chain else none
    | ["p2commit", c0, c1, c2, c3, c4, c5, c6, c7, pat, j, r] =>
      if j == toString JP2 && r == toString rootP then do
        let c ← [c0, c1, c2, c3, c4, c5, c6, c7].mapM String.toNat?
        let ps ← pat.toList.mapM charPat
        some (.commit c ps)
      else none
    | _ => none
  let lg ← match words (ls.getD 2 "") with
    | ["log", r, m, a, b, c] => do some ⟨← r.toNat?, ← m.toNat?, ← a.toNat?, ← b.toNat?, ← c.toNat?⟩
    | _ => none
  if st.ok && plogsOK lg && text == publicTextG st lg then some (st, lg) else none

/-- `p2pre`'s statement, as before. -/
def statementOfTextP (text : String) : Option (Nat × PLogs) :=
  match statementOfTextG text with
  | some (.pre h, lg) => some (h, lg)
  | _ => none

end ComposedPText
