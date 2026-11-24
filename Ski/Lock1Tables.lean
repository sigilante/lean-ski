import Ski.HnfSound
open Term

/-!
# Lock 1, Conj. CT: the five table facts T1–T5 on S1's 38-block table

`notes/LOCK1-CT.md` §10 proves Theorems Q, TR and VIS from S1's block model of head normal
forms (`HnfS`, `HnfSound`) and five finite facts T1–T5 about the block table `HnfS.β`,
checked there by a script (`s10tab.py`).  This module states the five facts and proves
each by kernel evaluation (`decide +kernel`; no `native_decide`), and lifts the ones the
note uses first to terms.

* `K1`, `K2`: the blocks `β 0 x`, and `β k y` with `k ∈ K1` (`mem_K1`, `mem_K2`); a term
  `S c` has its block in `K1` and a term `S c d` in `K2` (`fold_one`, `fold_two`).
* `T1`: `{0}`, `K1`, `K2` are pairwise disjoint and none contains the ⊥ block `36`.
* `G`, `T2`: the only block of `K2` that can revive a dead application is `13`
  (`T2_dead` is the form used).
* `T3a`, `T3b`, `T3c`: the entries with value `13` (first argument in `K1`), `2` (first
  argument `0`) and `1`.
* `T4`: `36` is absorbing on the left (this is `HnfSound.absorb`).
* `T5`: the block recurrence of case (b) of Theorem VIS has solutions at `j = 1` only,
  and with `s = β 0 α` only for `υ = 13`.  It holds for every `j`, with no bound: the
  recurrence dies at its fourth term (`T5_dies`), so the note's periodicity argument is
  not needed.
* Terms: a term `S c d` of block `13` is `S (S S) (S S)` (`lit13`); a pure term has no
  head normal form exactly when its block is `36` (`hnfless_iff`); Theorem Q, item 1:
  if `a w` has no head normal form and `S c d` is not `S (S S) (S S)`, then `S c d a w`
  has none (`thmQ1`); item 2, the reduction of the exception (`thmQ2`).

Not here: Theorem Q item 4, Theorems TR and VIS (they need normal forms, confluence and
the Moves), and the derivation of T5's hypotheses from terms (§10.3).
-/

namespace Lock1Tables
open HnfS HnfSound

/-! ## The sets -/

/-- The blocks `β 0 x`: the blocks of terms `S c`. -/
def K1 : List Nat := r38.filter fun x => r38.any fun y => β 0 y == x

/-- The blocks `β k y`, `k ∈ K1`: the blocks of terms `S c d`. -/
def K2 : List Nat := r38.filter fun x => K1.any fun k => r38.any fun y => β k y == x

/-- The blocks `γ` for which some `α`, `ω` have `β α ω = 36` and `β (β γ α) ω ≠ 36`. -/
def G : List Nat :=
  r38.filter fun g => r38.any fun al => r38.any fun om => β al om == 36 && β (β g al) om != 36

theorem mem_K1 {x : Nat} : x ∈ K1 ↔ x < 38 ∧ ∃ y, y < 38 ∧ β 0 y = x := by
  simp only [K1, r38, List.mem_filter, List.mem_range, List.any_eq_true, beq_iff_eq]

theorem mem_K2 {x : Nat} : x ∈ K2 ↔ x < 38 ∧ ∃ k, k ∈ K1 ∧ ∃ y, y < 38 ∧ β k y = x := by
  simp only [K2, r38, List.mem_filter, List.mem_range, List.any_eq_true, beq_iff_eq]

theorem mem_G {g : Nat} :
    g ∈ G ↔ g < 38 ∧ ∃ al, al < 38 ∧ ∃ om, om < 38 ∧ β al om = 36 ∧ β (β g al) om ≠ 36 := by
  simp only [G, r38, List.mem_filter, List.mem_range, List.any_eq_true, Bool.and_eq_true,
    beq_iff_eq, bne_iff_ne, ne_eq]

theorem K1_eq : K1 = [1, 2, 4, 5, 8, 9, 10, 11, 17, 18, 19, 20, 27, 28] := by decide +kernel

theorem K2_eq : K2 =
    [3, 6, 7, 12, 13, 14, 15, 16, 21, 22, 23, 24, 25, 26, 29, 30, 31, 32, 33, 34, 35, 37] := by
  decide +kernel

theorem G_eq : G = [0, 1, 2, 4, 5, 8, 10, 11, 13, 17, 19, 20] := by decide +kernel

/-! ## T1–T5 -/

/-- **T1.** `{0}`, `K1`, `K2` are pairwise disjoint and none contains `36`. -/
theorem T1 : 0 ∉ K1 ∧ 0 ∉ K2 ∧ (∀ x, x ∈ K1 → x ∉ K2) ∧ 36 ∉ K1 ∧ 36 ∉ K2 := by
  decide +kernel

/-- **T2.** `G ∩ K2 = {13}`. -/
theorem T2 : (∀ g, g ∈ G → g ∈ K2 → g = 13) ∧ 13 ∈ G ∧ 13 ∈ K2 := by decide +kernel

/-- **T3**, first part: `β x y = 13` with `x ∈ K1` only at `(x, y) = (2, 1)`. -/
theorem T3a : (∀ x, x ∈ K1 → ∀ y, y < 38 → β x y = 13 → x = 2 ∧ y = 1) ∧ 2 ∈ K1 ∧ β 2 1 = 13 := by
  decide +kernel

/-- **T3**, second part: `β 0 x = 2` only at `x = 1`. -/
theorem T3b : ∀ x, x < 38 → (β 0 x = 2 ↔ x = 1) := by decide +kernel

/-- **T3**, third part: `β x y = 1` only at `(x, y) = (0, 0)`. -/
theorem T3c : ∀ x, x < 38 → ∀ y, y < 38 → (β x y = 1 ↔ x = 0 ∧ y = 0) := by decide +kernel

/-- **T4.** `36` is absorbing on the left. -/
theorem T4 : ∀ y, y < 38 → β 36 y = 36 := by decide +kernel

/-- The recurrence of T5: `u 0 = ω`, `u 1 = β ya ω`, `u (m + 2) = β (u m) (u (m + 1))`,
as the pair `(u m, u (m + 1))`.  In T5, `ya = β υ s`. -/
def upair (ya ω : Nat) : Nat → Nat × Nat
  | 0 => (ω, β ya ω)
  | m + 1 => ((upair ya ω m).2, β (upair ya ω m).1 (upair ya ω m).2)

/-- The sequence `u_m` of T5. -/
def u (ya ω m : Nat) : Nat := (upair ya ω m).1

theorem u_zero (ya ω : Nat) : u ya ω 0 = ω := rfl
theorem u_one (ya ω : Nat) : u ya ω 1 = β ya ω := rfl
theorem u_add_two (ya ω m : Nat) : u ya ω (m + 2) = β (u ya ω m) (u ya ω (m + 1)) := rfl

/-- The recurrence of T5 dies at its fourth term: if `β υ s`, `u_1`, `u_2` are not `36`
then `u_3 = 36`. -/
theorem T5_dies : ∀ υ, υ ∈ K2 → ∀ s, s ∈ K1 → ∀ ω, ω < 38 → β υ s ≠ 36 → β (β υ s) ω ≠ 36 →
    β ω (β (β υ s) ω) ≠ 36 → β (β (β υ s) ω) (β ω (β (β υ s) ω)) = 36 := by decide +kernel

/-- The solutions of T5 at `j = 1` with `s = β 0 α` have `υ = 13`. -/
theorem T5_one : ∀ υ, υ ∈ K2 → ∀ α, α ∈ K2 → ∀ ω, ω < 38 →
    (ω ≠ 36 ∧ β υ (β 0 α) ≠ 36 ∧ β (β υ (β 0 α)) ω ≠ 36 ∧ β α (β (β υ (β 0 α)) ω) = 36 ∧
      β ω (β (β υ (β 0 α)) ω) ≠ 36) → υ = 13 := by decide +kernel

/-- **T5.** For `υ, α ∈ K2`, `ω ≠ 36`, `s ∈ K1`, `j ≥ 1`: if `β υ s ≠ 36`, `u_0, …, u_j ≠ 36`,
`β α u_j = 36` and `β u_{j-1} u_j ≠ 36`, then `j = 1`; and if moreover `s = β 0 α`, then
`υ = 13`.  For every `j`. -/
theorem T5 {υ α ω s j : Nat} (hυ : υ ∈ K2) (hα : α ∈ K2) (hω : ω < 38) (hω36 : ω ≠ 36)
    (hs : s ∈ K1) (hj : 1 ≤ j) (hys : β υ s ≠ 36) (hu : ∀ m, m ≤ j → u (β υ s) ω m ≠ 36)
    (h1 : β α (u (β υ s) ω j) = 36) (h2 : β (u (β υ s) ω (j - 1)) (u (β υ s) ω j) ≠ 36) :
    j = 1 ∧ (s = β 0 α → υ = 13) := by
  have hj1 : j = 1 := by
    match j, hj, hu, h2 with
    | 1, _, _, _ => rfl
    | j + 2, _, hu, h2 =>
      have d := T5_dies υ hυ s hs ω hω hys (hu 1 (by omega)) (hu 2 (by omega))
      match j, hu, h2 with
      | 0, _, h2 => exact absurd d h2
      | j + 1, hu, _ => exact absurd d (hu 3 (by omega))
  subst hj1
  refine ⟨rfl, fun hsα => ?_⟩
  subst hsα
  exact T5_one υ hυ α hα ω hω ⟨hω36, hys, hu 1 (Nat.le_refl 1), h1, h2⟩

/-! ## Terms -/

/-- A term `S c` has its block in `K1`. -/
theorem fold_one {c : Term} (hc : PureS c) : fold (S ⬝ c) ∈ K1 :=
  mem_K1.2 ⟨β_lt (by decide) (fold_lt hc), fold c, fold_lt hc, rfl⟩

/-- A term `S c d` has its block in `K2`. -/
theorem fold_two {c d : Term} (hc : PureS c) (hd : PureS d) : fold (S ⬝ c ⬝ d) ∈ K2 :=
  mem_K2.2 ⟨β_lt (β_lt (by decide) (fold_lt hc)) (fold_lt hd), fold (S ⬝ c), fold_one hc,
    fold d, fold_lt hd, rfl⟩

/-- A pure term of block `1` is `S S`. -/
theorem eq_SS {t : Term} (ht : PureS t) (h : fold t = 1) : t = S ⬝ S := by
  cases ht with
  | S => exact absurd h (by decide)
  | app hf hx =>
    obtain ⟨h0, h0'⟩ := (T3c _ (fold_lt hf) _ (fold_lt hx)).1 h
    rw [fold_eq_zero hf h0, fold_eq_zero hx h0']

/-- Consequence of T1, T3 and `fold_eq_zero` (§10.0): a term `S c d` of block `13` is
`S (S S) (S S)` literally. -/
theorem lit13 {c d : Term} (hc : PureS c) (hd : PureS d) (h : fold (S ⬝ c ⬝ d) = 13) :
    c = S ⬝ S ∧ d = S ⬝ S := by
  obtain ⟨h2, h1⟩ := T3a.1 _ (fold_one hc) _ (fold_lt hd) h
  exact ⟨eq_SS hc ((T3b _ (fold_lt hc)).1 h2), eq_SS hd h1⟩

/-- A pure term has no head normal form exactly when its block is `36`. -/
theorem hnfless_iff {t : Term} (ht : PureS t) : ¬ HasHnf t ↔ fold t = 36 :=
  ⟨fun hn => if h : fold t = 36 then h else absurd (sound t ht h) hn, no_hnf_of_bot ht⟩

/-- The form of T2 that Theorem Q uses: a block of `K2` other than `13`, applied to a dead
pair, is dead. -/
theorem T2_dead {g al om : Nat} (hg : g ∈ K2) (hal : al < 38) (hom : om < 38)
    (h : β al om = 36) (hne : g ≠ 13) : β (β g al) om = 36 :=
  if h' : β (β g al) om = 36 then h'
  else absurd (T2.1 g (mem_G.2 ⟨(mem_K2.1 hg).1, al, hal, om, hom, h, h'⟩) hg) hne

/-- **Theorem Q, item 1** (§10.1): if `a w` has no head normal form and `S c d` is not
`S (S S) (S S)`, then `S c d a w` has no head normal form. -/
theorem thmQ1 {c d a w : Term} (hc : PureS c) (hd : PureS d) (ha : PureS a) (hw : PureS w)
    (hY : S ⬝ c ⬝ d ≠ S ⬝ (S ⬝ S) ⬝ (S ⬝ S)) (h : ¬ HasHnf (a ⬝ w)) :
    ¬ HasHnf (S ⬝ c ⬝ d ⬝ a ⬝ w) := by
  have haw : β (fold a) (fold w) = 36 := (hnfless_iff (.app ha hw)).1 h
  have hne : fold (S ⬝ c ⬝ d) ≠ 13 := fun h13 => by
    obtain ⟨rfl, rfl⟩ := lit13 hc hd h13
    exact hY rfl
  exact no_hnf_of_bot (.app (.app (.app (.app .S hc) hd) ha) hw)
    (T2_dead (fold_two hc hd) (fold_lt ha) (fold_lt hw) haw hne)

/-- **Theorem Q, item 2** (§10.1): `S (S S) (S S) a w ↠ S w (a w) (a (S S a) w)`. -/
theorem thmQ2 (a w : Term) :
    WSteps (S ⬝ (S ⬝ S) ⬝ (S ⬝ S) ⬝ a ⬝ w) (S ⬝ w ⬝ (a ⬝ w) ⬝ (a ⬝ (S ⬝ S ⬝ a) ⬝ w)) :=
  .step (.left w (.S (S ⬝ S) (S ⬝ S) a)) <|
  .step (.left w (.S S a (S ⬝ S ⬝ a))) <|
  .step (.S (S ⬝ S ⬝ a) (a ⬝ (S ⬝ S ⬝ a)) w) <|
  .step (.left _ (.S S a w)) (.refl _)

end Lock1Tables
