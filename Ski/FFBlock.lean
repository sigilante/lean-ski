import Ski.Congruence
open Term

/-!
# The 38-block fold is a function of the tree (Lock 1, FF for 𝔹)

`fold_eqv`: for pure S-terms, `Congruence.Eqv t u` (equal `NF` prefixes at every depth) gives
`HnfS.fold t = HnfS.fold u`.  Proof of `notes/LOCK1-FF.md` with the Wizard repairs WF.5, WF.6:

* `tower k` = `S (S (⋯ (S S)))` with `k` outer `S`; `eq_tower` (Lemma B): a
  pure S-term whose block is in `{0, 1, 2, 4, 8, 17}` is a tower (no table entry is `0`, and the
  preimages of `1, 2, 4, 8, 17` lie in row `0`, at columns in the same set);
* `eqv_tower` (Lemma A′): `u ≈ tower k` gives `fold u = fold (tower k)`, by induction on `k`
  with `factK`;
* a rank certificate (`rankTable`, from `notes/checks/s4/lock1-ff/ff_rank.py`) replaces the
  pair iteration C2: `rank x y = 0` only when `x = y` or the pair touches `17` or `36`
  (`base_cert`), and every hnf configuration of a pair of positive rank has a differing child
  pair of strictly smaller rank (`k1_cert` for `S a`, `k2_cert` for `S a c`, where the first
  child pair is the pair of blocks of `S a`, `S a′`, which lie in `img0`, the image of row 0);
* `ff_le` (strong induction on the rank) and `fold_eqv`.

All table facts are `decide +kernel` on `Bool` checks, split per row of `img0` for the kind-2
certificate; no `native_decide`.  Case splits are on decidable `Nat` equalities only.
-/

namespace FFBlock
open HnfS HnfSound TopTerm InfNF Congruence

/-! ## Lemma B: blocks 0, 1, 2, 4, 8, 17 are carried only by towers -/

/-- `tower k = S (S (⋯ (S S)))`, `k` outer `S`.  Not `BExp.tower`, which is `iterS k (S ⬝ S)`: `FFBlock.tower (k + 1) = BExp.tower k`. -/
def tower : Nat → Term
  | 0 => .S
  | k + 1 => S ⬝ tower k

theorem tower_pure : ∀ k, PureS (tower k)
  | 0 => .S
  | k + 1 => .app .S (tower_pure k)

/-- The tower blocks. -/
def towerSet (x : Nat) : Bool := x == 0 || x == 1 || x == 2 || x == 4 || x == 8 || x == 17

def towerB : Bool := HnfS.r38.all fun i => HnfS.r38.all fun j =>
  β i j != 0 && (!towerSet (β i j) || (i == 0 && towerSet j))

theorem towerB_eq : towerB = true := by decide +kernel

theorem tower_cert {i j : Nat} (hi : i < 38) (hj : j < 38) :
    β i j ≠ 0 ∧ (towerSet (β i j) = true → i = 0 ∧ towerSet j = true) := by
  have h := towerB_eq
  simp only [towerB, HnfS.r38, List.all_eq_true, List.mem_range, Bool.and_eq_true, bne_iff_ne,
    ne_eq, Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq] at h
  obtain ⟨h1, h2⟩ := h i hi j hj
  refine ⟨h1, fun ht => ?_⟩
  rcases h2 with h2 | h2
  · rw [ht] at h2; cases h2
  · exact h2

theorem fold_ne_zero {f x : Term} (hf : PureS f) (hx : PureS x) : fold (f ⬝ x) ≠ 0 :=
  (tower_cert (fold_lt hf) (fold_lt hx)).1

theorem eq_S_of_fold {f : Term} (hf : PureS f) (h : fold f = 0) : f = S := by
  cases hf with
  | S => rfl
  | app h1 h2 => exact absurd h (fold_ne_zero h1 h2)

/-- **Lemma B.**  A pure S-term whose block is a tower block is a tower. -/
theorem eq_tower {u : Term} (hu : PureS u) (h : towerSet (fold u) = true) :
    ∃ k, u = tower k := by
  induction hu with
  | S => exact ⟨0, rfl⟩
  | @app f x hf hx _ ihx =>
    obtain ⟨h0, hj⟩ := (tower_cert (fold_lt hf) (fold_lt hx)).2 h
    obtain ⟨k, rfl⟩ := ihx hj
    exact ⟨k + 1, by rw [eq_S_of_fold hf h0]; rfl⟩

/-! ## Lemma A′: the `≈`-class of a tower -/

/-- **Lemma A′** (WF.5).  `u ≈ tower k` gives `fold u = fold (tower k)`. -/
theorem eqv_tower : ∀ (k : Nat) {u : Term}, PureS u → Eqv u (tower k) →
    fold u = fold (tower k)
  | 0, u, hu, h => by
    obtain ⟨u', hs, hm⟩ := factK (tower_pure 0) hu h.symm (.refl _) (.inl rfl)
    rw [← steps_fold hu hs]
    rcases hm with ⟨_, rfl⟩ | ⟨_, _, h1, _⟩ | ⟨_, _, _, _, h1, _⟩
    · rfl
    · cases h1
    · cases h1
  | k + 1, u, hu, h => by
    obtain ⟨u', hs, hm⟩ := factK (tower_pure (k + 1)) hu h.symm (.refl _) (.inr (.inl ⟨_, rfl⟩))
    have hu' := steps_pure hu hs
    rw [← steps_fold hu hs]
    rcases hm with ⟨h1, _⟩ | ⟨a, a', h1, rfl, ea⟩ | ⟨_, _, _, _, h1, _⟩
    · cases h1
    · injection h1 with _ h2
      subst h2
      show β (fold S) (fold a') = β (fold S) (fold (tower k))
      rw [eqv_tower k hu'.app_inv.2 ea.symm]
    · cases h1

/-- Block `17` (or any tower block) on one side of `≈` forces equal blocks. -/
theorem eqv_towerSet {t u : Term} (ht : PureS t) (hu : PureS u) (h : Eqv t u)
    (h17 : towerSet (fold t) = true) : fold t = fold u := by
  obtain ⟨k, rfl⟩ := eq_tower ht h17
  exact (eqv_tower k hu h.symm).symm

/-! ## The rank certificate -/

def rankTable : List (List Nat) := [
  [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1],
  [1, 0, 2, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 1, 1, 0, 2, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 0, 1],
  [1, 2, 0, 1, 3, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 1, 1, 0, 3, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 1, 1, 0, 1],
  [1, 1, 1, 0, 1, 1, 2, 3, 1, 1, 1, 1, 2, 2, 3, 3, 3, 0, 1, 1, 1, 2, 2, 2, 2, 3, 3, 1, 1, 2, 2, 3, 2, 2, 3, 3, 0, 3],
  [1, 2, 3, 1, 0, 2, 1, 1, 4, 3, 2, 2, 1, 1, 1, 1, 1, 0, 4, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 1, 1, 1, 1, 1, 1, 0, 1],
  [1, 2, 2, 1, 2, 0, 1, 1, 2, 3, 3, 4, 1, 1, 1, 1, 1, 0, 4, 4, 4, 1, 1, 1, 1, 1, 1, 4, 3, 1, 1, 1, 1, 1, 1, 1, 0, 1],
  [1, 1, 1, 2, 1, 1, 0, 2, 1, 1, 1, 1, 3, 3, 3, 2, 2, 0, 1, 1, 1, 2, 3, 3, 3, 3, 2, 1, 1, 3, 3, 3, 3, 2, 3, 2, 0, 2],
  [1, 1, 1, 3, 1, 1, 2, 0, 1, 1, 1, 1, 2, 2, 4, 4, 3, 0, 1, 1, 1, 2, 2, 2, 2, 4, 3, 1, 1, 2, 2, 4, 2, 2, 4, 3, 0, 3],
  [1, 2, 3, 1, 4, 2, 1, 1, 0, 3, 2, 2, 1, 1, 1, 1, 1, 0, 4, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 1, 1, 1, 1, 1, 1, 0, 1],
  [1, 2, 3, 1, 3, 3, 1, 1, 3, 0, 4, 3, 1, 1, 1, 1, 1, 0, 6, 3, 3, 1, 1, 1, 1, 1, 1, 6, 5, 1, 1, 1, 1, 1, 1, 1, 0, 1],
  [1, 2, 2, 1, 2, 3, 1, 1, 2, 4, 0, 3, 1, 1, 1, 1, 1, 0, 4, 3, 3, 1, 1, 1, 1, 1, 1, 4, 4, 1, 1, 1, 1, 1, 1, 1, 0, 1],
  [1, 2, 2, 1, 2, 4, 1, 1, 2, 3, 3, 0, 1, 1, 1, 1, 1, 0, 5, 5, 4, 1, 1, 1, 1, 1, 1, 5, 3, 1, 1, 1, 1, 1, 1, 1, 0, 1],
  [1, 1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 1, 0, 3, 3, 2, 2, 0, 1, 1, 1, 3, 3, 3, 3, 3, 2, 1, 1, 3, 3, 3, 3, 3, 3, 2, 0, 2],
  [1, 1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 0, 3, 2, 2, 0, 1, 1, 1, 2, 4, 3, 3, 3, 2, 1, 1, 3, 4, 4, 3, 2, 3, 2, 0, 2],
  [1, 1, 1, 3, 1, 1, 3, 4, 1, 1, 1, 1, 3, 3, 0, 5, 3, 0, 1, 1, 1, 2, 4, 3, 3, 4, 3, 1, 1, 4, 4, 6, 3, 2, 5, 3, 0, 3],
  [1, 1, 1, 3, 1, 1, 2, 4, 1, 1, 1, 1, 2, 2, 5, 0, 3, 0, 1, 1, 1, 2, 2, 2, 2, 4, 3, 1, 1, 2, 2, 5, 2, 2, 5, 3, 0, 3],
  [1, 1, 1, 3, 1, 1, 2, 3, 1, 1, 1, 1, 2, 2, 3, 3, 0, 0, 1, 1, 1, 2, 2, 2, 2, 5, 4, 1, 1, 2, 2, 5, 2, 2, 5, 5, 0, 4],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [1, 2, 3, 1, 4, 4, 1, 1, 4, 6, 4, 5, 1, 1, 1, 1, 1, 0, 0, 6, 6, 1, 1, 1, 1, 1, 1, 8, 5, 1, 1, 1, 1, 1, 1, 1, 0, 1],
  [1, 2, 2, 1, 2, 4, 1, 1, 2, 3, 3, 5, 1, 1, 1, 1, 1, 0, 6, 0, 4, 1, 1, 1, 1, 1, 1, 6, 3, 1, 1, 1, 1, 1, 1, 1, 0, 1],
  [1, 2, 2, 1, 2, 4, 1, 1, 2, 3, 3, 4, 1, 1, 1, 1, 1, 0, 6, 4, 0, 1, 1, 1, 1, 1, 1, 6, 3, 1, 1, 1, 1, 1, 1, 1, 0, 1],
  [1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 0, 1, 1, 1, 0, 4, 2, 2, 3, 2, 1, 1, 2, 4, 4, 3, 3, 3, 2, 0, 2],
  [1, 1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 4, 4, 2, 2, 0, 1, 1, 1, 4, 0, 3, 3, 3, 2, 1, 1, 4, 5, 5, 3, 3, 3, 2, 0, 2],
  [1, 1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 3, 3, 2, 2, 0, 1, 1, 1, 2, 3, 0, 3, 5, 2, 1, 1, 3, 3, 5, 4, 2, 5, 2, 0, 2],
  [1, 1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 3, 3, 2, 2, 0, 1, 1, 1, 2, 3, 3, 0, 5, 2, 1, 1, 3, 3, 5, 4, 2, 5, 2, 0, 2],
  [1, 1, 1, 3, 1, 1, 3, 4, 1, 1, 1, 1, 3, 3, 4, 4, 5, 0, 1, 1, 1, 3, 3, 5, 5, 0, 5, 1, 1, 3, 3, 7, 5, 5, 7, 6, 0, 6],
  [1, 1, 1, 3, 1, 1, 2, 3, 1, 1, 1, 1, 2, 2, 3, 3, 4, 0, 1, 1, 1, 2, 2, 2, 2, 5, 0, 1, 1, 2, 2, 5, 2, 2, 5, 4, 0, 5],
  [1, 2, 3, 1, 4, 4, 1, 1, 5, 6, 4, 5, 1, 1, 1, 1, 1, 0, 8, 6, 6, 1, 1, 1, 1, 1, 1, 0, 6, 1, 1, 1, 1, 1, 1, 1, 0, 1],
  [1, 2, 2, 1, 2, 3, 1, 1, 2, 5, 4, 3, 1, 1, 1, 1, 1, 0, 5, 3, 3, 1, 1, 1, 1, 1, 1, 6, 0, 1, 1, 1, 1, 1, 1, 1, 0, 1],
  [1, 1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 3, 4, 2, 2, 0, 1, 1, 1, 2, 4, 3, 3, 3, 2, 1, 1, 0, 5, 4, 3, 2, 3, 2, 0, 2],
  [1, 1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 4, 4, 2, 2, 0, 1, 1, 1, 4, 5, 3, 3, 3, 2, 1, 1, 5, 0, 6, 3, 3, 3, 2, 0, 2],
  [1, 1, 1, 3, 1, 1, 3, 4, 1, 1, 1, 1, 3, 4, 6, 5, 5, 0, 1, 1, 1, 4, 5, 5, 5, 7, 5, 1, 1, 4, 6, 0, 5, 5, 9, 7, 0, 7],
  [1, 1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 3, 3, 2, 2, 0, 1, 1, 1, 3, 3, 4, 4, 5, 2, 1, 1, 3, 3, 5, 0, 4, 5, 2, 0, 2],
  [1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 0, 1, 1, 1, 3, 3, 2, 2, 5, 2, 1, 1, 2, 3, 5, 4, 0, 5, 2, 0, 2],
  [1, 1, 1, 3, 1, 1, 3, 4, 1, 1, 1, 1, 3, 3, 5, 5, 5, 0, 1, 1, 1, 3, 3, 5, 5, 7, 5, 1, 1, 3, 3, 9, 5, 5, 0, 7, 0, 6],
  [1, 1, 1, 3, 1, 1, 2, 3, 1, 1, 1, 1, 2, 2, 3, 3, 5, 0, 1, 1, 1, 2, 2, 2, 2, 6, 4, 1, 1, 2, 2, 7, 2, 2, 7, 0, 0, 4],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [1, 1, 1, 3, 1, 1, 2, 3, 1, 1, 1, 1, 2, 2, 3, 3, 4, 0, 1, 1, 1, 2, 2, 2, 2, 6, 5, 1, 1, 2, 2, 7, 2, 2, 6, 4, 0, 0]]

/-- The rank of a block pair: the round in which the pair leaves the pair automaton of
`ff_rank.py` (`0` for equal pairs and for pairs touching `17` or `36`). -/
def rank (x y : Nat) : Nat := (rankTable.getD x []).getD y 0

/-- The image of row 0: the blocks of terms `S a`. -/
def img0 : List Nat := [1, 2, 4, 5, 8, 9, 10, 11, 17, 18, 19, 20, 27, 28]

/-- A child pair that differs and has rank below `r`. -/
def usable (x y r : Nat) : Bool := x != y && decide (rank x y < r)

def img0B : Bool := HnfS.r38.all fun a => img0.contains (β 0 a)

def baseB : Bool := HnfS.r38.all fun x => HnfS.r38.all fun y =>
  rank x y != 0 || x == y || x == 17 || x == 36 || y == 17 || y == 36

def k1B : Bool := HnfS.r38.all fun a => HnfS.r38.all fun a' =>
  rank (β 0 a) (β 0 a') == 0 || usable a a' (rank (β 0 a) (β 0 a'))

/-- The kind-2 certificate for one row `p` of `img0`. -/
def k2Row (p : Nat) : Bool := img0.all fun p' => HnfS.r38.all fun c => HnfS.r38.all fun c' =>
  rank (β p c) (β p' c') == 0 || usable p p' (rank (β p c) (β p' c')) ||
    usable c c' (rank (β p c) (β p' c'))

theorem img0B_eq : img0B = true := by decide +kernel
theorem baseB_eq : baseB = true := by decide +kernel
theorem k1B_eq : k1B = true := by decide +kernel
theorem k2Row_1 : k2Row 1 = true := by decide +kernel
theorem k2Row_2 : k2Row 2 = true := by decide +kernel
theorem k2Row_4 : k2Row 4 = true := by decide +kernel
theorem k2Row_5 : k2Row 5 = true := by decide +kernel
theorem k2Row_8 : k2Row 8 = true := by decide +kernel
theorem k2Row_9 : k2Row 9 = true := by decide +kernel
theorem k2Row_10 : k2Row 10 = true := by decide +kernel
theorem k2Row_11 : k2Row 11 = true := by decide +kernel
theorem k2Row_17 : k2Row 17 = true := by decide +kernel
theorem k2Row_18 : k2Row 18 = true := by decide +kernel
theorem k2Row_19 : k2Row 19 = true := by decide +kernel
theorem k2Row_20 : k2Row 20 = true := by decide +kernel
theorem k2Row_27 : k2Row 27 = true := by decide +kernel
theorem k2Row_28 : k2Row 28 = true := by decide +kernel

theorem usable_iff {x y r : Nat} : usable x y r = true ↔ x ≠ y ∧ rank x y < r := by
  simp only [usable, Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq]

theorem img0_mem {a : Nat} (ha : a < 38) : β 0 a ∈ img0 := by
  have h := img0B_eq
  simp only [img0B, HnfS.r38, List.all_eq_true, List.mem_range, List.contains_iff_mem] at h
  exact h a ha

theorem base_cert {x y : Nat} (hx : x < 38) (hy : y < 38) :
    rank x y ≠ 0 ∨ x = y ∨ x = 17 ∨ x = 36 ∨ y = 17 ∨ y = 36 := by
  have h := baseB_eq
  simp only [baseB, HnfS.r38, List.all_eq_true, List.mem_range, Bool.or_eq_true, bne_iff_ne,
    ne_eq, beq_iff_eq] at h
  have := h x hx y hy
  rcases this with (((((h1 | h1) | h1) | h1) | h1) | h1)
  · exact .inl h1
  · exact .inr (.inl h1)
  · exact .inr (.inr (.inl h1))
  · exact .inr (.inr (.inr (.inl h1)))
  · exact .inr (.inr (.inr (.inr (.inl h1))))
  · exact .inr (.inr (.inr (.inr (.inr h1))))

theorem k1_cert {a a' : Nat} (ha : a < 38) (ha' : a' < 38) :
    rank (β 0 a) (β 0 a') = 0 ∨ (a ≠ a' ∧ rank a a' < rank (β 0 a) (β 0 a')) := by
  have h := k1B_eq
  simp only [k1B, HnfS.r38, List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq] at h
  rcases h a ha a' ha' with h1 | h1
  · exact .inl h1
  · exact .inr (usable_iff.1 h1)

theorem k2_of_row {p : Nat} (hrow : k2Row p = true) {p' c c' : Nat} (hp' : p' ∈ img0)
    (hc : c < 38) (hc' : c' < 38) :
    rank (β p c) (β p' c') = 0 ∨ (p ≠ p' ∧ rank p p' < rank (β p c) (β p' c')) ∨
      (c ≠ c' ∧ rank c c' < rank (β p c) (β p' c')) := by
  simp only [k2Row, HnfS.r38, List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq] at hrow
  rcases hrow p' hp' c hc c' hc' with (h1 | h1) | h1
  · exact .inl h1
  · exact .inr (.inl (usable_iff.1 h1))
  · exact .inr (.inr (usable_iff.1 h1))

theorem k2_cert {p p' c c' : Nat} (hp : p ∈ img0) (hp' : p' ∈ img0) (hc : c < 38)
    (hc' : c' < 38) :
    rank (β p c) (β p' c') = 0 ∨ (p ≠ p' ∧ rank p p' < rank (β p c) (β p' c')) ∨
      (c ≠ c' ∧ rank c c' < rank (β p c) (β p' c')) := by
  simp only [img0, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact k2_of_row k2Row_1 hp' hc hc'
  · exact k2_of_row k2Row_2 hp' hc hc'
  · exact k2_of_row k2Row_4 hp' hc hc'
  · exact k2_of_row k2Row_5 hp' hc hc'
  · exact k2_of_row k2Row_8 hp' hc hc'
  · exact k2_of_row k2Row_9 hp' hc hc'
  · exact k2_of_row k2Row_10 hp' hc hc'
  · exact k2_of_row k2Row_11 hp' hc hc'
  · exact k2_of_row k2Row_17 hp' hc hc'
  · exact k2_of_row k2Row_18 hp' hc hc'
  · exact k2_of_row k2Row_19 hp' hc hc'
  · exact k2_of_row k2Row_20 hp' hc hc'
  · exact k2_of_row k2Row_27 hp' hc hc'
  · exact k2_of_row k2Row_28 hp' hc hc'

/-! ## The theorem -/

/-- One rank level, after the decidable splits: `t ≈ u` with blocks that differ and avoid
`17` and `36`.  Every `≈` pair of smaller rank has equal blocks, so a hnf configuration with
a differing child pair of smaller rank (`k1_cert`, `k2_cert`) is impossible. -/
theorem ff_core (r : Nat)
    (ih : ∀ {t u : Term}, PureS t → PureS u → Eqv t u → rank (fold t) (fold u) < r →
      fold t = fold u)
    {t u : Term} (ht : PureS t) (hu : PureS u) (h : Eqv t u) (hr : rank (fold t) (fold u) = r)
    (heq : fold t ≠ fold u) (h36 : fold t ≠ 36) (h36' : fold u ≠ 36) (h17 : fold t ≠ 17)
    (h17' : fold u ≠ 17) : fold t = fold u := by
  have hr0 : r ≠ 0 := by
    rcases base_cert (fold_lt ht) (fold_lt hu) with h1 | h1 | h1 | h1 | h1 | h1
    · exact hr ▸ h1
    · exact absurd h1 heq
    · exact absurd h1 h17
    · exact absurd h1 h36
    · exact absurd h1 h17'
    · exact absurd h1 h36'
  obtain ⟨t0, hc, _, ht0⟩ := sound_head t ht h36
  have hs := headChain_steps hc
  obtain ⟨u0, hs', hm⟩ := factK ht hu h hs ht0
  have pt := steps_pure ht hs
  have pu := steps_pure hu hs'
  have et := steps_fold ht hs
  have eu := steps_fold hu hs'
  rw [← et, ← eu] at hr heq ⊢
  rcases hm with ⟨rfl, rfl⟩ | ⟨a, a', rfl, rfl, ea⟩ | ⟨a, c, a', c', rfl, rfl, ea, ec⟩
  · rfl
  · have pa := pt.app_inv.2
    have pa' := pu.app_inv.2
    change rank (β 0 (fold a)) (β 0 (fold a')) = r at hr
    rcases k1_cert (fold_lt pa) (fold_lt pa') with h1 | ⟨h1, h2⟩
    · exact absurd (hr ▸ h1) hr0
    · exact absurd (ih pa pa' ea (hr ▸ h2)) h1
  · have pSa := pt.app_inv.1
    have pSa' := pu.app_inv.1
    have pc := pt.app_inv.2
    have pc' := pu.app_inv.2
    have eSa : Eqv (S ⬝ a) (S ⬝ a') :=
      eqv_app .S .S pSa.app_inv.2 pSa'.app_inv.2 (Eqv.refl _) ea
    change rank (β (fold (S ⬝ a)) (fold c)) (β (fold (S ⬝ a')) (fold c')) = r at hr
    rcases k2_cert (img0_mem (fold_lt pSa.app_inv.2)) (img0_mem (fold_lt pSa'.app_inv.2))
      (fold_lt pc) (fold_lt pc') with h1 | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact absurd (hr ▸ h1) hr0
    · exact absurd (ih pSa pSa' eSa (hr ▸ h2)) h1
    · exact absurd (ih pc pc' ec (hr ▸ h2)) h1

/-- One rank level: if every `≈` pair of smaller rank has equal blocks, so does every `≈`
pair of rank `r`.  The splits are on decidable `Nat` equalities. -/
theorem ff_step (r : Nat)
    (ih : ∀ {t u : Term}, PureS t → PureS u → Eqv t u → rank (fold t) (fold u) < r →
      fold t = fold u)
    {t u : Term} (ht : PureS t) (hu : PureS u) (h : Eqv t u) (hr : rank (fold t) (fold u) = r) :
    fold t = fold u :=
  if heq : fold t = fold u then heq else
  if h36 : fold t = 36 then h36.trans (eqv_bot ht hu h h36).symm else
  if h36' : fold u = 36 then (eqv_bot hu ht h.symm h36').trans h36'.symm else
  if h17 : fold t = 17 then eqv_towerSet ht hu h (by rw [h17]; rfl) else
  if h17' : fold u = 17 then (eqv_towerSet hu ht h.symm (by rw [h17']; rfl)).symm else
  ff_core r ih ht hu h hr heq h36 h36' h17 h17'

/-- Strong induction on the rank. -/
theorem ff_le : ∀ (n : Nat) {t u : Term}, PureS t → PureS u → Eqv t u →
    rank (fold t) (fold u) ≤ n → fold t = fold u
  | 0, _, _, ht, hu, h, hn =>
    ff_step _ (fun _ _ _ hr => absurd hr (Nat.not_lt_zero _)) ht hu h (Nat.le_zero.1 hn)
  | n + 1, _, _, ht, hu, h, hn =>
    ff_step _ (fun ht' hu' h' hr => ff_le n ht' hu' h' (Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hr hn)))
      ht hu h rfl

/-- **FF for 𝔹.**  For pure S-terms, `t ≈ u` gives equal 38-block folds. -/
theorem fold_eqv {t u : Term} (ht : PureS t) (hu : PureS u) (h : Eqv t u) :
    fold t = fold u :=
  ff_le _ ht hu h (Nat.le_refl _)

end FFBlock
