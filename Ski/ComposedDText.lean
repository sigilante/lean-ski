import Ski.ComposedText
import Ski.ComposedO
import Ski.DecJet

/-!
# A composed statement with the `dec` jet: a decrement

`decpre p`: "I know a stack noun `[n r]`, `n` below `2^32`, whose `dec` is
`[p …]`."  The subject is the statement's hidden term, laid out in the
region (`subjRegion`: `encNn` of the noun, the combinators' cells shared,
its root the region's last cell, which the composed machine reads as the
witness `w`); the statement has one unused bit.  The verifier is an open
term with the jet's variable `JD` free:

  `V = λ β w. CHECK_p ⬝ (J ⬝ w)`

`CHECK_p` eliminates the result as a noun: a cell whose head is an atom
whose bits are exactly `p`'s, least significant first, is `K`; anything
else hands the rest to `Θ K`, which absorbs every argument and never
becomes `K` (`DecPre.chkL_sound`).  The jet fires at `J ⬝ w` when `CHECK_p`
applies the result to its four continuations: the subject's pointer is
the one argument on the stack, and the row writes the outcome
(`DecJet.decRow`).

`Circuit.compDAirsG` is the circuit for such statements; the text
`public.txt` is `publicTextD`, and `statementOfTextD` parses it back only
when it is exactly that text.
-/

namespace ComposedDText

open Compose CompM ComposedText DecJet

/-- The jet's atom: above every slot and below the circuit's `2^24`. -/
def JD : Nat := 2 ^ 23

/-- `Θ K`: absorbs every argument and never becomes `K`. -/
def badO : OTerm := BitArith.thetaT.toO ⬝ₒ .K

/-- The canonical bits of `n`, least significant first (skinock's `bits`). -/
def bitsN : Nat → List Bool
  | 0 => []
  | n + 1 => ((n + 1) % 2 == 1) :: bitsN ((n + 1) / 2)
  decreasing_by omega

theorem bitsN_zero : bitsN 0 = [] := by rw [bitsN]

theorem bitsN_pos {n : Nat} (h : 0 < n) : bitsN n = (n % 2 == 1) :: bitsN (n / 2) := by
  cases n with
  | zero => omega
  | succ n => rw [bitsN]

theorem val_bitsN (n : Nat) : BitArith.val (bitsN n) = n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    cases n with
    | zero => rw [bitsN_zero]; rfl
    | succ n =>
      rw [bitsN_pos (Nat.succ_pos n)]
      show ((n + 1) % 2 == 1).toNat + 2 * BitArith.val (bitsN ((n + 1) / 2)) = n + 1
      rw [ih ((n + 1) / 2) (by omega)]
      have hd := Nat.div_add_mod (n + 1) 2
      rcases Nat.mod_two_eq_zero_or_one (n + 1) with h | h <;> rw [h] at hd ⊢
      · have e : (0 == 1).toNat = 0 := rfl
        rw [e]; omega
      · have e : (1 == 1).toNat = 1 := rfl
        rw [e]; omega

theorem canonB_bitsN (n : Nat) : canonB (bitsN n) = true := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    cases n with
    | zero => rw [bitsN_zero]; rfl
    | succ n =>
      rw [bitsN_pos (Nat.succ_pos n)]
      have ih' := ih ((n + 1) / 2) (by omega)
      cases hb : bitsN ((n + 1) / 2) with
      | nil =>
        have : (n + 1) / 2 = 0 := by
          have := val_bitsN ((n + 1) / 2); rw [hb] at this; exact this.symm
        have : n = 0 := by omega
        subst this; rfl
      | cons c cs => rw [hb] at ih'; exact ih'

/-- **The decrement on canonical bits is the predecessor**: `decB` of
    `n + 1`'s bits is `n`'s, what a consumer needs to match `decSpec` with
    skinock's `decC` (`bits` there is `bitsN` here). -/
theorem decB_bitsN (n : Nat) : decB (bitsN (n + 1)) = bitsN n := by
  have hne : bitsN (n + 1) ≠ [] := by rw [bitsN_pos (Nat.succ_pos n)]; exact List.cons_ne_nil _ _
  have hv := decB_val (canonB_bitsN (n + 1)) hne
  rw [val_bitsN] at hv
  exact canon_val_inj (decB_canon (canonB_bitsN (n + 1))) (canonB_bitsN n) (by rw [val_bitsN]; omega)

/-- Canonical bits are a number's bits. -/
theorem bitsN_val {b : List Bool} (h : canonB b = true) : bitsN (BitArith.val b) = b :=
  canon_val_inj (canonB_bitsN _) h (val_bitsN _)

/-- **Read a Scott list against the bits `es`, then be `K`**: `nil` passes
    when `es` is empty; a `cons` passes its bit to the next test and its
    tail to the rest.  A mismatch hands everything to `Θ K`. -/
def chkL : List Bool → OTerm
  | [] => absN [0] (.var 0 ⬝ₒ .K ⬝ₒ (.K ⬝ₒ (.K ⬝ₒ badO)))
  | e :: es =>
    absN [0] (.var 0 ⬝ₒ badO ⬝ₒ
      absN [1, 2] (.var 1 ⬝ₒ (if e then chkL es ⬝ₒ .var 2 else badO) ⬝ₒ (if e then badO else chkL es ⬝ₒ .var 2)))

/-- **The continuation**: the result is a cell whose head is the atom `p`. -/
def checkD (p : Nat) : OTerm :=
  absN [0] (.var 0 ⬝ₒ badO ⬝ₒ absN [1, 2] (.var 1 ⬝ₒ chkL (bitsN p) ⬝ₒ badO ⬝ₒ badO ⬝ₒ badO) ⬝ₒ badO ⬝ₒ badO)

/-- **The verifier**: `λ β w. CHECK_p ⬝ (J ⬝ w)`. -/
def verifierD (p : Nat) : OTerm := absN [0, 1] (checkD p ⬝ₒ (.var JD ⬝ₒ .var 1))

/-- The statement's shape: one unused bit. -/
def shpD : BT := .leaf false
def VsD (p : Nat) : List OTerm := [verifierD p]

/-- The log heights a statement names: the CPU, the memory, and the jet's
    table. -/
structure DLogs where
  rows : Nat
  mem : Nat
  dec : Nat
  deriving BEq, Repr

def dlogsOK (l : DLogs) : Bool := [l.rows, l.mem, l.dec].all fun x => 9 ≤ x && x ≤ 22

/-- The region's size is within the witness table's private cells. -/
def regionOKD (W : Nat) : Bool := 0 < W && 1 + W ≤ 2 ^ 8

/-- **The statement's text**: the composed machine of the open verifier,
    the bit cell and the region blank. -/
def publicTextD (p W : Nat) (lg : DLogs) : String := Id.run do
  let N := BT.nleaves shpD
  let region := List.replicate W Cell.S
  let m := cMachineO (fun _ => false) shpD region (VsD p)
  let roots := (cHeapO (fun _ => false) shpD region (VsD p)).2
  let mut s := s!"decpre {p} {JD}\nW {W}\nlog {lg.rows} {lg.mem} {lg.dec}\nbits {N}\nroots {" ".intercalate (roots.map toString)}\nnil {m.stk}\n{m.hd} {m.stk} {m.heap.length}\n"
  let mut i := 0
  for c in m.heap do
    s := s ++ (if 3 ≤ i && i < N + 3 + W then "W" else cellText c) ++ "\n"
    i := i + 1
  return s

/-- The statement, parsed back only when it is exactly `publicTextD`'s
    text. -/
def statementOfTextD (text : String) : Option (Nat × Nat × DLogs) := do
  let ls := text.splitOn "\n"
  let p ← match words (ls.getD 0 "") with
    | ["decpre", p, j] => if j == toString JD then p.toNat? else none
    | _ => none
  let W ← match words (ls.getD 1 "") with
    | ["W", n] => n.toNat?
    | _ => none
  let lg ← match words (ls.getD 2 "") with
    | ["log", r, m, d] => do some ⟨← r.toNat?, ← m.toNat?, ← d.toNat?⟩
    | _ => none
  if regionOKD W && dlogsOK lg && text == publicTextD p W lg then some (p, W, lg) else none

-- ---------------------------------------------------------------------------
-- The witness: the subject laid out in the region
-- ---------------------------------------------------------------------------

/-- The bit list's `Cons` cells from the top bit down, each over the one
    before, ending at the slot `K` (nil): six cells per bit, over the
    region's `S` at `sA`, `S I` at `siA`, and the slots `K` (0) and
    `K I` (2).  Returns the cells and the list's root. -/
def bitCellsR (sA siA : Nat) : List Bool → Nat → List Cell × Nat
  | [], _ => ([], 0)
  | b :: bs, base =>
    let (rest, next) := bitCellsR sA siA bs base
    let c := base + rest.length
    (rest ++ [.app 0 (if b then 0 else 2), .app siA c, .app sA (c + 1), .app 0 next, .app (c + 2) (c + 3),
      .app 0 (c + 4)], c + 5)

/-- `Atom root` at `base`: five cells, the last its root. -/
def atomCellsR (skkA siA root base : Nat) : List Cell :=
  [.app 0 root, .app siA base, .app skkA (base + 1), .app skkA (base + 2), .app skkA (base + 3)]

/-- **The subject `[b 0]` in a region of `W` cells** starting at address
    `base`: the shared combinators, the bits, the head atom, the tail
    atom `0`, and the cell, its root the region's last cell; padded before
    with `K`. -/
def subjRegion (b : List Bool) (W base : Nat) : Option (List Cell) :=
  let n := 6 * b.length + 22
  if n ≤ W then
    let pad := W - n
    let s := base + pad
    let skk := s + 2
    let si := s + 3
    let pre := [Cell.S, .app 0 0, .app s (s + 1), .app s 1]
    let (bits, root) := bitCellsR s si b (s + 4)
    let a := s + 4 + bits.length
    let head := atomCellsR skk si root a
    let z := atomCellsR skk si 0 (a + 5)
    let c := a + 10
    let cell := [Cell.app 0 (a + 9), .app 0 (a + 4), .app si (c + 1), .app s (c + 2), .app (c + 3) c,
      .app skk (c + 4), .app skk (c + 5), .app 0 (c + 6)]
    some (List.replicate pad .K ++ pre ++ bits ++ head ++ z ++ cell)
  else none

end ComposedDText
