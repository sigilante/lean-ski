import Ski.ZK.ROMMerkleRows

/-!
# The Merkle leaves' positions as Plonky3 hashes them

`ROMMerkleRows`'s `posRows` carries the leaf index, so distinct leaves never
share a position.  Plonky3 hashes a leaf's row and salt alone: `posRowsP`,
the salt and the row's hash, no index.  It meets the hypotheses the
collision-aware theorems keep after dropping `hdist` (`ROMMerkleColl`,
`ROMInstMC`, `ROMFamilyMC`): positions in range (`posRowsP_lt`, below
`NSl Mh`), one salt per position value (`posRowsP_spread`, `s = 1`), and the
opened leaves' positions fixed by the opened values (`posRowsP_hposO`).
Two leaves with equal rows and salts share a position (`posRowsP_meet`).
One salt per leaf stands for Plonky3's per-matrix salts, uniform over their
product; all groups sit in one leaf, where Plonky3 injects shorter
matrices' rows into internal nodes (`ROMMerkleRows`'s caveats).
-/

set_option autoImplicit false

namespace Circuit
open ZKF

/-- A leaf's position as Plonky3 hashes it: its salt and a hash `h` of its
    row, no leaf index. -/
def posRowsP (xs : Nat → Nat → F) (mk : List Nat) (h : List (List F) → Nat) (NSl Mh : Nat)
    (d : List (List (List F))) (l a : Nat) : Nat :=
  a % NSl + NSl * (h (rowAt xs mk d l) % Mh)

/-- Positions lie below `NSl Mh`. -/
theorem posRowsP_lt {xs : Nat → Nat → F} {mk : List Nat} {h : List (List F) → Nat} {L NSl Mh : Nat}
    (hN : 0 < NSl) (hMh : 0 < Mh) : ∀ d l a, l < L → posRowsP xs mk h NSl Mh d l a < NSl * Mh := by
  intro d l a _
  unfold posRowsP
  have hm : h (rowAt xs mk d l) % Mh + 1 ≤ Mh := Nat.mod_lt _ hMh
  calc a % NSl + NSl * (h (rowAt xs mk d l) % Mh) < NSl + NSl * (h (rowAt xs mk d l) % Mh) :=
        Nat.add_lt_add_right (Nat.mod_lt _ hN) _
    _ = NSl * (h (rowAt xs mk d l) % Mh + 1) := by rw [Nat.mul_succ, Nat.add_comm]
    _ ≤ NSl * Mh := Nat.mul_le_mul_left _ hm

/-- A leaf's salt fixes its position: one salt per value (`s = 1`). -/
theorem posRowsP_spread {xs : Nat → Nat → F} {mk : List Nat} {h : List (List F) → Nat} {NSl Mh : Nat} :
    ∀ d l v, sumTo NSl (fun x => indB (decide (posRowsP xs mk h NSl Mh d l x = v))) ≤ 1 := by
  intro d l v
  have key : ∀ x, x < NSl → indB (decide (posRowsP xs mk h NSl Mh d l x = v)) ≤ indB (decide (x = v % NSl)) := by
    intro x hx
    cases e : decide (posRowsP xs mk h NSl Mh d l x = v)
    · exact Nat.zero_le _
    · have ev : posRowsP xs mk h NSl Mh d l x = v := of_decide_eq_true e
      have hx' : x = v % NSl := by
        rw [← ev]; unfold posRowsP
        rw [Nat.add_mul_mod_self_left, Nat.mod_mod, Nat.mod_eq_of_lt hx]
      rw [decide_eq_true hx']; exact Nat.le_refl _
  exact Nat.le_trans (sumTo_mono _ key) (sumTo_indEq _ NSl).1

/-- **`hposO` is met by Plonky3's positions** at `opF`'s opened set
    (`rowAt_opF`). -/
theorem posRowsP_hposO {xs : Nat → Nat → F} {mk : List Nat} {h : List (List F) → Nat} {NSl Mh : Nat} (Ss : List (List F)) :
    ∀ d d', opF Ss mk d = opF Ss mk d' → ∀ l a, isOfRows Ss mk xs l = true →
      posRowsP xs mk h NSl Mh d l a = posRowsP xs mk h NSl Mh d' l a := by
  intro d d' e l a hi
  unfold posRowsP; rw [rowAt_opF mk d d' e hi]

/-- **Leaves with equal rows and salts meet**: what `hdist` excluded. -/
theorem posRowsP_meet {xs : Nat → Nat → F} {mk : List Nat} {h : List (List F) → Nat} {NSl Mh : Nat}
    (d : List (List (List F))) {l l' : Nat} (hr : rowAt xs mk d l = rowAt xs mk d l') (a : Nat) :
    posRowsP xs mk h NSl Mh d l a = posRowsP xs mk h NSl Mh d l' a := by
  unfold posRowsP; rw [hr]

/-- Plonky3's position read off the indexed one: drop the index. -/
theorem posRowsP_of_posRows {xs : Nat → Nat → F} {mk : List Nat} {h : List (List F) → Nat} {L NSl Mh : Nat}
    (hL : 0 < L) (d : List (List (List F))) (l a : Nat) :
    posRowsP xs mk h NSl Mh d l a = (posRows xs mk h L NSl Mh d l a - l) / L := by
  unfold posRowsP posRows; rw [Nat.add_sub_cancel_left, Nat.mul_div_cancel_left _ hL]

end Circuit
