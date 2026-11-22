import Ski.D2Data
import Ski.HnfS

/-!
# The 373-element depth-2 S-model `D`: operations and kernel checks

`τ a b` is the product of `D` (element `0` is `S`), read from the bit-packed rows of `D2Data`.
The checks are written for the kernel: every table access in an inner loop is one shift and one
mask on a literal, and the rows are forced before the loop (`force`).

* `slawPart a j`: the S-law `s·a·b·c = a·c·(b·c)` for one `a`, 47 values of `c` and all `b`
  (checked in `D2K/`);
* `colsB`, `closedB`, `homB`, `outB`, `botB`: the columns are the transposed rows; `D` is closed;
  `φD : D → S1 blocks` is a homomorphism; the output conditions T0–T3 of
  `notes/S4-d2-theorem.md`.
-/

namespace D2
open HnfS

/-- Entry `i` of a packed row. -/
def get (r i : Nat) : Nat := Nat.land (Nat.shiftRight r (Nat.mul 9 i)) 511

def rowN (a : Nat) : Nat := rows.getD a 0
def colN (c : Nat) : Nat := cols.getD c 0

/-- The product of `D`. -/
def τ (a b : Nat) : Nat := get (rowN a) b

/-- The S1 block of an element. -/
def φD (d : Nat) : Nat := Nat.land (Nat.shiftRight phiN (Nat.mul 6 d)) 63

/-- The output code of an element: `0` for `S`; `4 + k`, `8 + k`, `12 + k` for `S a`, `S a b`,
no head normal form, where `k` codes the depth-1 prefix of the last item. -/
def outC (d : Nat) : Nat := Nat.land (Nat.shiftRight outN (Nat.mul 4 d)) 15

/-- `p i` for all `i < n`. -/
def allB : Nat → (Nat → Bool) → Bool
  | 0, _ => true
  | n + 1, p => p n && allB n p

theorem allB_spec {n : Nat} {p : Nat → Bool} : allB n p = true ↔ ∀ i, i < n → p i = true := by
  induction n with
  | zero => simp [allB]
  | succ n ih =>
    simp only [allB, Bool.and_eq_true, ih]
    constructor
    · intro h i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h' | rfl
      · exact h.2 i h'
      · exact h.1
    · intro h
      exact ⟨h n (Nat.lt_succ_self n), fun i hi => h i (Nat.lt_succ_of_lt hi)⟩

/-- Evaluate `x` before calling `k` (the kernel is call-by-name). -/
def force (x : Nat) (k : Nat → Bool) : Bool :=
  match x with
  | 0 => k 0
  | n + 1 => k (n + 1)

theorem force_eq (x : Nat) (k : Nat → Bool) : force x k = k x := by
  cases x <;> rfl

theorem chunk_get {p : Nat → Bool} {lo n : Nat} (h : allB n (fun i => p (lo + i)) = true) {a : Nat}
    (h1 : lo ≤ a) (h2 : a < lo + n) : p a = true := by
  have h3 := allB_spec.mp h (a - lo) (by omega)
  rwa [show lo + (a - lo) = a by omega] at h3

def slawIn (cc rx rsa : Nat) : Bool :=
  allB 373 fun b => Nat.beq (get cc (get rsa b)) (get rx (get cc b))

/-- The S-law for one `a` and the `c` in `[47 j, 47 j + 47)`: `(s·a·b)·c = (a·c)·(b·c)` for all
`b`.  (Split by `c` to bound the kernel's memory.) -/
def slawPart (a j : Nat) : Bool :=
  force (rowN a) fun ra => force (rowN (get (rowN 0) a)) fun rsa =>
    allB 47 fun i => force (47 * j + i) fun c => Nat.ble 373 c ||
      (force (colN c) fun cc => force (rowN (get ra c)) fun rx => slawIn cc rx rsa)

def slawChunk (k : Nat) : Bool := slawPart (k / 8) (k % 8)

/-- The columns are the transposed rows. -/
def colsIn (cc c : Nat) : List Nat → Nat → Bool
  | [], _ => true
  | r :: rs, y => Nat.beq (get cc y) (get r c) && force (y + 1) fun y' => colsIn cc c rs y'
def colsRow (c : Nat) : Bool := force (colN c) fun cc => colsIn cc c rows 0

theorem colsIn_spec {cc c : Nat} : ∀ {l : List Nat} {y : Nat}, colsIn cc c l y = true →
    ∀ i, i < l.length → get cc (y + i) = get (l.getD i 0) c := by
  intro l
  induction l with
  | nil => intro y _ i hi; exact absurd hi (Nat.not_lt_zero i)
  | cons r rs ih =>
    intro y h i hi
    simp only [colsIn, force_eq, Bool.and_eq_true] at h
    cases i with
    | zero => exact Nat.eq_of_beq_eq_true h.1
    | succ i =>
      have h2 := ih h.2 i (Nat.lt_of_succ_lt_succ hi)
      rw [show y + (i + 1) = y + 1 + i by omega]
      exact h2

theorem rows_len : rows.length = 373 := by decide +kernel
def colsB (lo n : Nat) : Bool := allB n fun i => colsRow (lo + i)

def closedRow (a : Nat) : Bool :=
  force (rowN a) fun ra => allB 373 fun b => Nat.ble (Nat.succ (get ra b)) 373
def closedB (lo n : Nat) : Bool := allB n fun i => closedRow (lo + i)

/-- `φD` is a homomorphism to S1's blocks. -/
def homRow (a : Nat) : Bool :=
  force (rowN a) fun ra => force (φD a) fun pa =>
    allB 373 fun b => Nat.beq (φD (get ra b)) (β pa (φD b))
def homB (lo n : Nat) : Bool := allB n fun i => homRow (lo + i)

/-- T0, T1: the outputs of `S` and `S a`. -/
def out1B : Bool := Nat.beq (outC 0) 0 && allB 373 fun e => Nat.beq (outC (τ 0 e)) (4 + outC e / 4)

/-- T2: the outputs of `S a b`. -/
def out2Row (e : Nat) : Bool :=
  force (rowN (get (rowN 0) e)) fun r => allB 373 fun f => Nat.beq (outC (get r f)) (8 + outC f / 4)
def out2B (lo n : Nat) : Bool := allB n fun i => out2Row (lo + i)

/-- T3: the outputs over the bottom block. -/
def botB : Bool :=
  allB 373 fun d => Nat.beq (φD d) 36 == false ||
    (Nat.beq (outC d / 4) 3 &&
      force (rowN d) fun r => allB 373 fun e => Nat.beq (outC (get r e)) (12 + outC e / 4))

theorem out1B_eq : out1B = true := by decide +kernel
theorem botB_eq : botB = true := by decide +kernel
theorem phi0 : φD 0 = 0 := by decide +kernel

end D2
