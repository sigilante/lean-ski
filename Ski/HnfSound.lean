import Ski.HnfS
open Term

/-!
# Soundness of the fold: *Dance of the Starlings*, Question 10, in full

`HnfS.q10_of_soundness` proves Question 10 from one hypothesis: a closed pure-S term
whose 38-block fold is not ⊥ has a head normal form.  This module proves that
hypothesis, so Question 10 holds outright (`q10`).

The proof is a termination argument for the root (leftmost-outermost) run, by a weight
summed along the walk of the frame.  Write a term as `S u₁ ⋯ uₘ`, its frame.  The walk
reads the frame from state `0` (the block of `S`) through the block table, and the
weight `r₁` adds `c(state, block of item)` at each item.  A root step replaces the
window `u₁ u₂ u₃` by the frame of `u₁` followed by `u₃` and `u₂ u₃`, and because the
block table is a model of the S law the walk reaches the rest of the frame in the same
state as before.  So the change in weight is decided by the window alone, which is a
finite check over 9,725 windows (`window`).  The frame of `u₁` is bounded by a
potential `π` (`wt_le_pot`).  The weight strictly drops except when the head's block
is `0` (then `u₁ = S`, and the number of `S` items drops) or one of the tower blocks
`2, 4, 8, 17` (then `u₁ = S v` with `v ≠ S`, the number of `S` items does not grow, and
the head's tower depth drops).  The lexicographic measure (weight, `S` count, head
depth) therefore decreases along the run, so the run reaches a head normal form.

The weights (`wTable`, values `0`–`6`) and potentials (`piTable`) were found by integer
programming; the module only checks them, by `decide +kernel`.  This replaces the
89,658-node interface machine of Murmuration I's proof.
-/

namespace HnfSound
open HnfS

/-! ## Weights -/

/-- The window weights `c(state, class)`, found by integer programming; row 36 (⊥) is unused. -/
def wTable : List (List Nat) := [
  [0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [2, 2, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [1, 2, 2, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [2, 2, 2, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [1, 2, 2, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 1, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]

/-- The deposit potentials `π(state)`. -/
def piTable : List Nat := [0, 0, 1, 0, 1, 0, 0, 2, 1, 0, 0, 1, 0, 1, 2, 1, 2, 1, 0, 0, 0, 2, 2, 2, 2, 3, 2, 0, 0, 1, 2, 6, 2, 2, 3, 3, 0, 0]

def cw (q a : Nat) : Nat := (wTable.getD q []).getD a 0
def pw (q : Nat) : Nat := piTable.getD q 0

/-! ## Finite checks -/

def towerBlock (a : Nat) : Bool := a == 2 || a == 4 || a == 8 || a == 17
def exempt (a : Nat) : Bool := a == 0 || towerBlock a

def windowB : Bool :=
  r38.all fun cx => r38.all fun cy => r38.all fun cz =>
    decide (cx ≠ 36 → β (β (β 0 cx) cy) cz ≠ 36 →
      (if cx = 0 then 0 else pw cx) + cw cx cz + cw (β cx cz) (β cy cz)
        + (if exempt cx then 0 else 1)
        ≤ cw 0 cx + cw (β 0 cx) cy + cw (β (β 0 cx) cy) cz)
def potB : Bool :=
  r38.all fun s => r38.all fun a => decide (s ≠ 36 → β s a ≠ 36 → pw s + cw s a ≤ pw (β s a))
def zeroB : Bool := r38.all fun a => r38.all fun b => decide (β a b ≠ 0)
def towerB : Bool := r38.all fun a => r38.all fun b => decide (towerBlock (β a b) = true → a = 0 ∧ b ≠ 0)
def absorbB : Bool := r38.all fun b => decide (β 36 b = 36)

theorem windowB_eq : windowB = true := by decide +kernel
theorem potB_eq : potB = true := by decide +kernel
theorem zeroB_eq : zeroB = true := by decide +kernel
theorem towerB_eq : towerB = true := by decide +kernel
theorem absorbB_eq : absorbB = true := by decide +kernel

theorem window {cx cy cz : Nat} (hx : cx < 38) (hy : cy < 38) (hz : cz < 38) (hx36 : cx ≠ 36)
    (h3 : β (β (β 0 cx) cy) cz ≠ 36) :
    (if cx = 0 then 0 else pw cx) + cw cx cz + cw (β cx cz) (β cy cz)
        + (if exempt cx then 0 else 1)
      ≤ cw 0 cx + cw (β 0 cx) cy + cw (β (β 0 cx) cy) cz := by
  have h := windowB_eq
  simp only [windowB, r38, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  exact h cx hx cy hy cz hz hx36 h3

theorem pot {s a : Nat} (hs : s < 38) (ha : a < 38) (hs36 : s ≠ 36) (h : β s a ≠ 36) :
    pw s + cw s a ≤ pw (β s a) := by
  have h' := potB_eq
  simp only [potB, r38, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h'
  exact h' s hs a ha hs36 h

theorem beta_ne_zero {a b : Nat} (ha : a < 38) (hb : b < 38) : β a b ≠ 0 := by
  have h := zeroB_eq
  simp only [zeroB, r38, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  exact h a ha b hb

theorem tower_entry {a b : Nat} (ha : a < 38) (hb : b < 38) (h : towerBlock (β a b) = true) :
    a = 0 ∧ b ≠ 0 := by
  have h' := towerB_eq
  simp only [towerB, r38, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h'
  exact h' a ha b hb h

theorem absorb {b : Nat} (hb : b < 38) : β 36 b = 36 := by
  have h := absorbB_eq
  simp only [absorbB, r38, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  exact h b hb

/-! ## Frames and walks -/

/-- The frame of a term: `spine (S u₁ ⋯ uₘ) = [u₁, …, uₘ]`. -/
def spine : Term → List Term
  | .app f x => spine f ++ [x]
  | _ => []

theorem spine_foldl (f : Term) (w : List Term) : spine (w.foldl Term.app f) = spine f ++ w := by
  induction w generalizing f with
  | nil => simp
  | cons x w ih => simp [List.foldl, ih, spine]

theorem pure_eq_foldl {t : Term} (ht : PureS t) : t = (spine t).foldl Term.app S := by
  induction ht with
  | S => rfl
  | app _ _ ihf _ =>
    simp only [spine, List.foldl_append, List.foldl]
    rw [← ihf]

theorem spine_pure {t : Term} (ht : PureS t) : ∀ u ∈ spine t, PureS u := by
  induction ht with
  | S => simp [spine]
  | app _ hx ihf _ =>
    intro u hu
    simp only [spine, List.mem_append, List.mem_singleton] at hu
    rcases hu with hu | rfl
    · exact ihf u hu
    · exact hx

/-- The block walk of a list of items from state `q`. -/
def walk (q : Nat) (w : List Term) : Nat := w.foldl (fun q u => β q (fold u)) q

theorem walk_append (q : Nat) (w₁ w₂ : List Term) : walk q (w₁ ++ w₂) = walk (walk q w₁) w₂ := by
  simp [walk, List.foldl_append]

theorem walk_spine {t : Term} (ht : PureS t) : walk 0 (spine t) = fold t := by
  induction ht with
  | S => rfl
  | app _ _ ihf _ =>
    simp only [spine, walk_append]
    simp only [walk, List.foldl] at ihf ⊢
    rw [ihf]; rfl

/-- Every state of the walk, including the first and the last, is not ⊥. -/
def AllH : Nat → List Term → Prop
  | q, [] => q ≠ 36
  | q, u :: w => q ≠ 36 ∧ AllH (β q (fold u)) w

theorem AllH.head : ∀ {q : Nat} {w : List Term}, AllH q w → q ≠ 36
  | _, [], h => h
  | _, _ :: _, h => h.1

theorem walk_bot (w : List Term) (hw : ∀ u ∈ w, PureS u) : walk 36 w = 36 := by
  induction w with
  | nil => rfl
  | cons u w ih =>
    simp only [walk, List.foldl] at ih ⊢
    rw [absorb (fold_lt (hw u (by simp)))]
    exact ih (fun v hv => hw v (by simp [hv]))

theorem allH_of_walk (q : Nat) (w : List Term) (hw : ∀ u ∈ w, PureS u) (h : walk q w ≠ 36) :
    AllH q w := by
  induction w generalizing q with
  | nil => exact h
  | cons u w ih =>
    have hw' : ∀ v ∈ w, PureS v := fun v hv => hw v (by simp [hv])
    refine ⟨?_, ih _ hw' h⟩
    rintro rfl
    apply h
    simp only [walk, List.foldl]
    rw [absorb (fold_lt (hw u (by simp)))]
    exact walk_bot w hw'

theorem allH_spine {t : Term} (ht : PureS t) (hb : fold t ≠ 36) : AllH 0 (spine t) :=
  allH_of_walk 0 _ (spine_pure ht) (by rw [walk_spine ht]; exact hb)

theorem walk_lt (q : Nat) (hq : q < 38) (w : List Term) (hw : ∀ u ∈ w, PureS u) : walk q w < 38 := by
  induction w generalizing q with
  | nil => exact hq
  | cons u w ih =>
    exact ih _ (β_lt hq (fold_lt (hw u (by simp)))) (fun v hv => hw v (by simp [hv]))

/-! ## The weight -/

/-- The weight of a list of items read from state `q`. -/
def wt : Nat → List Term → Nat
  | _, [] => 0
  | q, u :: w => cw q (fold u) + wt (β q (fold u)) w

theorem wt_append (q : Nat) (w₁ w₂ : List Term) : wt q (w₁ ++ w₂) = wt q w₁ + wt (walk q w₁) w₂ := by
  induction w₁ generalizing q with
  | nil => simp [wt, walk]
  | cons u w ih =>
    simp only [List.cons_append, wt, ih]
    simp only [walk, List.foldl]
    omega

/-- A walk that avoids ⊥ gains at most the potential difference. -/
theorem wt_le_pot (q : Nat) (hq : q < 38) (w : List Term) (hw : ∀ u ∈ w, PureS u) (h : AllH q w) :
    pw q + wt q w ≤ pw (walk q w) := by
  induction w generalizing q with
  | nil => simp [wt, walk]
  | cons u w ih =>
    obtain ⟨hq36, hrest⟩ := h
    have hu := fold_lt (hw u (by simp))
    have hnext : β q (fold u) ≠ 36 := hrest.head
    have hp := pot hq hu hq36 hnext
    have := ih _ (β_lt hq hu) (fun v hv => hw v (by simp [hv])) hrest
    simp only [wt, walk, List.foldl] at this ⊢
    omega

/-- The weight of a term: its frame read from `S`'s block. -/
def r₁ (t : Term) : Nat := wt 0 (spine t)

/-- The number of `S` items in a frame. -/
def nS : List Term → Nat
  | [] => 0
  | u :: w => (if u = S then 1 else 0) + nS w

theorem nS_append (w₁ w₂ : List Term) : nS (w₁ ++ w₂) = nS w₁ + nS w₂ := by
  induction w₁ with
  | nil => simp [nS]
  | cons u w ih => simp only [List.cons_append, nS, ih]; omega

/-- Tower depth: `S (S (⋯ (S v)))`, counting the leading `S` applications. -/
def td : Term → Nat
  | .app .S v => td v + 1
  | _ => 0

/-- The tower depth of the first frame item. -/
def hd (t : Term) : Nat :=
  match spine t with
  | u :: _ => td u
  | [] => 0

/-! ## One root step -/

theorem fold_eq_zero {u : Term} (hu : PureS u) (h : fold u = 0) : u = S := by
  cases hu with
  | S => rfl
  | app hf hx => exact absurd h (beta_ne_zero (fold_lt hf) (fold_lt hx))

theorem wstep_foldl {a b : Term} (h : WStep a b) (w : List Term) :
    WStep (w.foldl Term.app a) (w.foldl Term.app b) := by
  induction w generalizing a b with
  | nil => exact h
  | cons x w ih => exact ih (.left x h)

/-- The root step of a term with at least three frame items: the target, its frame,
and the decrease of the measure. -/
theorem root_step {t : Term} (ht : PureS t) (hb : fold t ≠ 36)
    {u₁ u₂ u₃ : Term} {rest : List Term} (hs : spine t = u₁ :: u₂ :: u₃ :: rest) :
    let t' := rest.foldl Term.app (u₁ ⬝ u₃ ⬝ (u₂ ⬝ u₃))
    WStep t t' ∧ spine t' = spine u₁ ++ u₃ :: (u₂ ⬝ u₃) :: rest ∧
    r₁ t' + (if exempt (fold u₁) then 0 else 1) ≤ r₁ t ∧
    (fold u₁ = 0 → u₁ = S) ∧
    (towerBlock (fold u₁) = true → ∃ v, u₁ = S ⬝ v ∧ v ≠ S) := by
  intro t'
  have hp := spine_pure ht
  rw [hs] at hp
  have p₁ := hp u₁ (by simp); have p₂ := hp u₂ (by simp); have p₃ := hp u₃ (by simp)
  have hrest : ∀ u ∈ rest, PureS u := fun u hu => hp u (by simp [hu])
  have a₁ := fold_lt p₁; have a₂ := fold_lt p₂; have a₃ := fold_lt p₃
  have hall := allH_spine ht hb
  rw [hs] at hall
  obtain ⟨-, h1, h2, h3⟩ := hall
  have hs3 : β (β (β 0 (fold u₁)) (fold u₂)) (fold u₃) ≠ 36 := h3.head
  have hx36 : fold u₁ ≠ 36 := by
    intro h; apply hs3; rw [compat a₁ a₂ a₃, h, absorb a₃, absorb (β_lt a₂ a₃)]
  refine ⟨?_, ?_, ?_, fold_eq_zero p₁, ?_⟩
  · -- the step
    have ht_eq : t = rest.foldl Term.app (S ⬝ u₁ ⬝ u₂ ⬝ u₃) := by
      have := pure_eq_foldl ht; rw [hs] at this; exact this
    rw [ht_eq]; exact wstep_foldl (WStep.S u₁ u₂ u₃) rest
  · rw [spine_foldl]; simp [spine]
  · -- the weight
    have hsp : spine t' = spine u₁ ++ u₃ :: (u₂ ⬝ u₃) :: rest := by rw [spine_foldl]; simp [spine]
    have hold : r₁ t = cw 0 (fold u₁) + (cw (β 0 (fold u₁)) (fold u₂)
        + (cw (β (β 0 (fold u₁)) (fold u₂)) (fold u₃)
        + wt (β (β (β 0 (fold u₁)) (fold u₂)) (fold u₃)) rest)) := by
      simp only [r₁, hs, wt]
    have hnew : r₁ t' = wt 0 (spine u₁) + (cw (fold u₁) (fold u₃)
        + (cw (β (fold u₁) (fold u₃)) (β (fold u₂) (fold u₃))
        + wt (β (β (fold u₁) (fold u₃)) (β (fold u₂) (fold u₃))) rest)) := by
      simp only [r₁, hsp, wt_append, walk_spine p₁, wt, fold]
    rw [← compat a₁ a₂ a₃] at hnew
    have hdep : wt 0 (spine u₁) ≤ (if fold u₁ = 0 then 0 else pw (fold u₁)) := by
      by_cases hz : fold u₁ = 0
      · rw [if_pos hz, fold_eq_zero p₁ hz]; simp [spine, wt]
      · rw [if_neg hz]
        have := wt_le_pot 0 (by decide) (spine u₁) (spine_pure p₁) (allH_spine p₁ hx36)
        rw [walk_spine p₁] at this
        omega
    have hw := window a₁ a₂ a₃ hx36 hs3
    omega
  · intro htw
    cases p₁ with
    | S => simp [fold, towerBlock] at htw
    | @app f v hf hv =>
      obtain ⟨hf0, hv0⟩ := tower_entry (fold_lt hf) (fold_lt hv) htw
      refine ⟨v, by rw [fold_eq_zero hf hf0], ?_⟩
      rintro rfl; exact hv0 rfl

/-! ## Termination -/

theorem lex3 {a b c a' b' c' : Nat} (h : a' < a ∨ (a' = a ∧ (b' < b ∨ (b' = b ∧ c' < c)))) :
    Prod.Lex (fun x y : Nat => x < y) (Prod.Lex (fun x y : Nat => x < y) fun x y : Nat => x < y)
      (a', b', c') (a, b, c) := by
  rcases h with h | ⟨rfl, h | ⟨rfl, h⟩⟩
  · exact .left _ _ h
  · exact .right _ (.left _ _ h)
  · exact .right _ (.right _ h)

/-- The measure (weight, `S` count, head tower depth) drops lexicographically. -/
theorem measure_dec {t t' u₁ u₂ u₃ : Term} {rest : List Term}
    (hs : spine t = u₁ :: u₂ :: u₃ :: rest) (hsp : spine t' = spine u₁ ++ u₃ :: (u₂ ⬝ u₃) :: rest)
    (hr : r₁ t' + (if exempt (fold u₁) then 0 else 1) ≤ r₁ t) (hz : fold u₁ = 0 → u₁ = S)
    (htw : towerBlock (fold u₁) = true → ∃ v, u₁ = S ⬝ v ∧ v ≠ S) :
    r₁ t' < r₁ t ∨ (r₁ t' = r₁ t ∧ (nS (spine t') < nS (spine t) ∨
      (nS (spine t') = nS (spine t) ∧ hd t' < hd t))) := by
  by_cases hex : exempt (fold u₁) = true
  · rw [if_pos hex] at hr
    by_cases hlt : r₁ t' < r₁ t
    · exact Or.inl hlt
    refine Or.inr ⟨by omega, ?_⟩
    simp only [exempt, Bool.or_eq_true, beq_iff_eq] at hex
    rcases hex with h0 | htb
    · -- atom head: `u₁ = S`, one `S` item fewer
      have h1 := hz h0; subst h1
      left
      rw [hs, hsp]
      simp only [spine, List.nil_append, nS]
      have e : (if u₂ ⬝ u₃ = S then 1 else 0) = 0 := if_neg (fun h => nomatch h)
      rw [e, if_pos trivial]
      omega
    · -- tower head: `u₁ = S v`, the head's depth drops
      obtain ⟨v, rfl, hv⟩ := htw htb
      have hsv : spine (S ⬝ v) = [v] := by simp [spine]
      rw [hsv] at hsp
      have hle : nS (spine t') ≤ nS (spine t) := by
        rw [hs, hsp]; simp only [List.singleton_append, nS, if_neg hv]
        have e1 : (if u₂ ⬝ u₃ = S then 1 else 0) = 0 := if_neg (fun h => nomatch h)
        have e2 : (if S ⬝ v = S then 1 else 0) = 0 := if_neg (fun h => nomatch h)
        rw [e1, e2]
        omega
      by_cases hlt2 : nS (spine t') < nS (spine t)
      · exact Or.inl hlt2
      refine Or.inr ⟨by omega, ?_⟩
      simp only [hd, hs, hsp, List.singleton_append, td]
      omega
  · rw [if_neg hex] at hr
    exact Or.inl (by omega)

theorem isHnf_of_short {t : Term} (ht : PureS t) (h : (spine t).length ≤ 2) : IsHnf t := by
  rw [pure_eq_foldl ht]
  match hs : spine t, h with
  | [], _ => exact Or.inl rfl
  | [a], _ => exact Or.inr (Or.inl ⟨a, rfl⟩)
  | [a, b], _ => exact Or.inr (Or.inr ⟨a, b, rfl⟩)

/-- **Soundness of the fold.**  A closed pure-S term whose fold is not ⊥ reduces to a
head normal form. -/
theorem sound (t : Term) (ht : PureS t) (hb : fold t ≠ 36) : HasHnf t := by
  match hs : spine t with
  | u₁ :: u₂ :: u₃ :: rest =>
    obtain ⟨hstep, hsp, hr, hz, htw⟩ := root_step ht hb hs
    have ⟨hp', he⟩ := wstep_pure hstep ht
    have hb' : fold (rest.foldl Term.app (u₁ ⬝ u₃ ⬝ (u₂ ⬝ u₃))) ≠ 36 := by rw [he]; exact hb
    obtain ⟨u, hus, hu⟩ := sound _ hp' hb'
    exact ⟨u, .step hstep hus, hu⟩
  | [] => exact ⟨t, .refl t, isHnf_of_short ht (by simp [hs])⟩
  | [_] => exact ⟨t, .refl t, isHnf_of_short ht (by simp [hs])⟩
  | [_, _] => exact ⟨t, .refl t, isHnf_of_short ht (by simp [hs])⟩
termination_by (r₁ t, nS (spine t), hd t)
decreasing_by
  exact lex3 (measure_dec hs hsp hr hz htw)

/-- **Question 10 of *Dance of the Starlings*.**  The automaton of Fig. 5.14 accepts
exactly the closed S-terms with a head normal form. -/
theorem q10 {t : Term} (ht : PureS t) : HasHnf t ↔ dance t ≠ P :=
  q10_of_soundness sound ht

end HnfSound
