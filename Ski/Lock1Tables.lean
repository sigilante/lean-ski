import Ski.HnfSound
open Term

/-!
# Lock 1, Conj. CT: the table facts T1–T5 and T7–T11 on S1's 38-block table

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

* T7 (§11.4): with `T = S S S`, `U = S T T`, `U_{e+1} = S U_e (S U_e)` (`Ufam`), the blocks
  `f_e = fold U_e` are `33, 31, 31, …` (`fold_Ufam`, `fseq_succ`) and `β f (β 0 f) = 36` for
  `f ∈ {33, 31}` (`T7`); so `U_e (S U_e)` has no head normal form (`T7_hnfless`), the fact
  Theorem FCT uses.  The cross-check `β f f' = 36` (`T7_cross`) gives Lemma F1 (`F1`).

* T8 (§12.0): with `X = S T S`, a base `Y` (`Base`: `X`, or `S X c` with `c` pure) and the
  two sequences `G_e`, `J_e` over `Y` (`Gfam Y e` is `G_e`; `Jfam Y e` is `J_{e+1}`, since
  the note's `J_e` starts at `e = 1`): the lookups (`T8_folds`, `T8_SXc`, `T8`), the blocks
  `fold X = 16`, `fold (S X) = 20`, `fold (S X c) = 34` for every pure `c`,
  `fold G_e = fold J_e = 31` (`fold_X`, `fold_SX`, `fold_SXc`, `fold_Gfam`, `fold_Jfam`), and
  the ten hnf-less terms of the note (`T8_XY`, `T8_YSY`, `T8_XSY`, `T8_XG`, `T8_XJ`, `T8_YG`,
  `T8_YJ`, `T8_GSG`, `T8_JSJ`; `T8_GSG` is stated for all `i`, `e`).
* T9: `X c_j` has a head normal form for every right comb `c_j` (`comb`, `T9_hnf`).
* T10: the self-dead blocks (`SELF`, `SELF_eq`); `W (t W)` has no head normal form for every
  pure `t` when `fold W ∈ SELF` (`self_dead`), in particular for `W` a base, `G_e`, `J_e`,
  `U_e` (`T10_base`, `T10_G`, `T10_J`, `T10_U`); `T` is not self-dead (`T10_T`,
  `T_not_self_dead`).
* T11: the 2-dead blocks (`DEAD2`, `DEAD2_eq`); `W p q` has no head normal form for all pure
  `p`, `q` when `fold W ∈ DEAD2` (`two_dead`), in particular for `W = S (S X c)`, `S (S Y)`,
  `S G_e`, `S J_e`, `S U_{e+1}` (`T11_SSXc`, `T11_SSY`, `T11_SG`, `T11_SJ`, `T11_SU`); `S X`
  and `S U_0` are not 2-dead (`T11_not`, `SX_not_two_dead`, `SU0_not_two_dead`).

"Closed" in the note is `PureS` here (closed terms over `S` alone).

Not here: Theorems X, XCT, LCD, LCD₁ of §12 (T8–T11 are only their table inputs); Theorem FCT itself; Theorem Q item 4, Theorems TR and VIS (they need normal forms, confluence and
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

/-! ## T7 and the family `U_e` (§11.4) -/

/-- `T = S S S`. -/
def T : Term := S ⬝ S ⬝ S

/-- `U = S T T`. -/
def U : Term := S ⬝ T ⬝ T

/-- `D(a) = S a (S a)`. -/
def D (a : Term) : Term := S ⬝ a ⬝ (S ⬝ a)

/-- `U_e = D^e(U)`: `U_0 = U`, `U_{e+1} = S U_e (S U_e)`. -/
def Ufam : Nat → Term
  | 0 => U
  | e + 1 => D (Ufam e)

/-- The block of `D(a)` from the block of `a`: `f ↦ β (β 0 f) (β 0 f)`. -/
def fstep (f : Nat) : Nat := β (β 0 f) (β 0 f)

/-- The sequence of T7: `f_0 = 33`, `f_{e+1} = β (β 0 f_e) (β 0 f_e)`. -/
def fseq : Nat → Nat
  | 0 => 33
  | e + 1 => fstep (fseq e)

theorem pure_T : PureS T := .app (.app .S .S) .S
theorem pure_U : PureS U := .app (.app .S pure_T) pure_T
theorem pure_D {a : Term} (ha : PureS a) : PureS (D a) := .app (.app .S ha) (.app .S ha)

theorem pure_Ufam : ∀ e, PureS (Ufam e)
  | 0 => pure_U
  | e + 1 => pure_D (pure_Ufam e)

/-- `fold U = 33`. -/
theorem fold_U : fold U = 33 := by decide +kernel

theorem fold_D (a : Term) : fold (D a) = fstep (fold a) := rfl

/-- **T7**, the sequence: `33 ↦ 31 ↦ 31`. -/
theorem T7_step : fstep 33 = 31 ∧ fstep 31 = 31 := by decide +kernel

/-- **T7**, the table fact: `β f (β 0 f) = 36` for `f ∈ {33, 31}`. -/
theorem T7 : ∀ f, f = 33 ∨ f = 31 → β f (β 0 f) = 36 := by
  rintro f (rfl | rfl) <;> decide +kernel

/-- The cross-check of T7 (the table fact behind Lemma F1): `β f f' = 36` for
`f, f' ∈ {33, 31}`. -/
theorem T7_cross : ∀ f, f = 33 ∨ f = 31 → ∀ f', f' = 33 ∨ f' = 31 → β f f' = 36 := by
  rintro f (rfl | rfl) f' (rfl | rfl) <;> decide +kernel

/-- The sequence is `33, 31, 31, …`. -/
theorem fseq_succ : ∀ e, fseq (e + 1) = 31
  | 0 => T7_step.1
  | e + 1 => by rw [fseq, fseq_succ e]; exact T7_step.2

theorem fseq_mem : ∀ e, fseq e = 33 ∨ fseq e = 31
  | 0 => .inl rfl
  | e + 1 => .inr (fseq_succ e)

/-- `f_e = fold U_e`. -/
theorem fold_Ufam : ∀ e, fold (Ufam e) = fseq e
  | 0 => fold_U
  | e + 1 => by rw [Ufam, fold_D, fold_Ufam e, fseq]

/-- **T7**, on terms (§11.4): `U_e (S U_e)` has no head normal form, for every `e`. -/
theorem T7_hnfless (e : Nat) : ¬ HasHnf (Ufam e ⬝ (S ⬝ Ufam e)) := by
  refine no_hnf_of_bot (.app (pure_Ufam e) (.app .S (pure_Ufam e))) ?_
  show β (fold (Ufam e)) (β 0 (fold (Ufam e))) = 36
  rw [fold_Ufam]
  exact T7 _ (fseq_mem e)

/-- **Lemma F1** (§8), from the cross-check: `U_j U_m` has no head normal form. -/
theorem F1 (j m : Nat) : ¬ HasHnf (Ufam j ⬝ Ufam m) := by
  refine no_hnf_of_bot (.app (pure_Ufam j) (pure_Ufam m)) ?_
  show β (fold (Ufam j)) (fold (Ufam m)) = 36
  rw [fold_Ufam, fold_Ufam]
  exact T7_cross _ (fseq_mem j) _ (fseq_mem m)

/-! ## T8–T11 and the counters on `X` (§12) -/

/-- `X = S T S`. -/
def X : Term := S ⬝ T ⬝ S

/-- A *base* (§12, Notation): `Y = X`, or `Y = S X c` for a closed `c`. -/
inductive Base : Term → Prop
  | x : Base X
  | sxc {c : Term} : PureS c → Base (S ⬝ X ⬝ c)

/-- `G_e` over `Y`: `G_0 = D(S Y)`, `G_{e+1} = S G_e (S J_{e+1})` with
`J_{e+1} = S (S Y) (S G_e)`. -/
def Gfam (Y : Term) : Nat → Term
  | 0 => D (S ⬝ Y)
  | e + 1 => S ⬝ Gfam Y e ⬝ (S ⬝ (S ⬝ (S ⬝ Y) ⬝ (S ⬝ Gfam Y e)))

/-- `Jfam Y e` is the note's `J_{e+1} = S (S Y) (S G_e)` (the note's `J_e` starts at `e = 1`). -/
def Jfam (Y : Term) (e : Nat) : Term := S ⬝ (S ⬝ Y) ⬝ (S ⬝ Gfam Y e)

theorem Gfam_zero (Y : Term) : Gfam Y 0 = S ⬝ (S ⬝ Y) ⬝ (S ⬝ (S ⬝ Y)) := rfl

/-- `G_{e+1} = S G_e (S J_{e+1})`. -/
theorem Gfam_succ (Y : Term) (e : Nat) : Gfam Y (e + 1) = S ⬝ Gfam Y e ⬝ (S ⬝ Jfam Y e) := rfl

/-- The right combs: `c_0 = S`, `c_{j+1} = S c_j`. -/
def comb : Nat → Term
  | 0 => S
  | j + 1 => S ⬝ comb j

theorem pure_X : PureS X := .app (.app .S pure_T) .S

theorem pure_base {Y : Term} (h : Base Y) : PureS Y := by
  cases h with
  | x => exact pure_X
  | sxc hc => exact .app (.app .S pure_X) hc

theorem pure_Gfam {Y : Term} (hY : PureS Y) : ∀ e, PureS (Gfam Y e)
  | 0 => pure_D (.app .S hY)
  | e + 1 => .app (.app .S (pure_Gfam hY e))
      (.app .S (.app (.app .S (.app .S hY)) (.app .S (pure_Gfam hY e))))

theorem pure_Jfam {Y : Term} (hY : PureS Y) (e : Nat) : PureS (Jfam Y e) :=
  .app (.app .S (.app .S hY)) (.app .S (pure_Gfam hY e))

theorem pure_comb : ∀ j, PureS (comb j)
  | 0 => .S
  | j + 1 => .app .S (pure_comb j)

/-- An application whose block is `36` has no head normal form. -/
theorem dead_app {a b : Term} (ha : PureS a) (hb : PureS b) (h : β (fold a) (fold b) = 36) :
    ¬ HasHnf (a ⬝ b) :=
  no_hnf_of_bot (.app ha hb) h

/-! ### T8 -/

/-- **T8**, the lookups for the folds (all but `β 20 κ`, which is `T8_SXc`). -/
theorem T8_folds : β 0 0 = 1 ∧ β 1 0 = 3 ∧ β 0 3 = 5 ∧ β 5 0 = 16 ∧ β 0 16 = 20 ∧ β 0 34 = 27 ∧
    β 0 20 = 27 ∧ β 0 27 = 27 ∧ β 27 27 = 31 ∧ β 0 31 = 27 := by decide +kernel

/-- **T8**: `β 20 κ = 34` for all 38 blocks `κ`. -/
theorem T8_SXc : ∀ κ, κ < 38 → β 20 κ = 34 := by decide +kernel

/-- **T8**, the eight entries with value `36`. -/
theorem T8 : β 16 16 = 36 ∧ β 16 20 = 36 ∧ β 16 34 = 36 ∧ β 34 27 = 36 ∧ β 16 27 = 36 ∧
    β 16 31 = 36 ∧ β 31 27 = 36 ∧ β 34 31 = 36 := by decide +kernel

/-- `fold T = 3`. -/
theorem fold_T : fold T = 3 := by decide +kernel

/-- `fold X = 16`. -/
theorem fold_X : fold X = 16 := by decide +kernel

/-- `fold (S X) = 20`. -/
theorem fold_SX : fold (S ⬝ X) = 20 := by decide +kernel

/-- `fold (S X c) = 34` for every closed `c`. -/
theorem fold_SXc {c : Term} (hc : PureS c) : fold (S ⬝ X ⬝ c) = 34 := by
  show β (fold (S ⬝ X)) (fold c) = 34
  rw [fold_SX]
  exact T8_SXc _ (fold_lt hc)

/-- The block of a base is `16` (`X`) or `34` (`S X c`). -/
theorem fold_base {Y : Term} (h : Base Y) : fold Y = 16 ∨ fold Y = 34 := by
  cases h with
  | x => exact .inl fold_X
  | sxc hc => exact .inr (fold_SXc hc)

/-- `fold (S Y) ∈ {20, 27}`. -/
theorem fold_S_base {Y : Term} (h : Base Y) : fold (S ⬝ Y) = 20 ∨ fold (S ⬝ Y) = 27 := by
  show β 0 (fold Y) = 20 ∨ β 0 (fold Y) = 27
  rcases fold_base h with e | e <;> rw [e] <;> decide +kernel

/-- `fold (S (S Y)) = 27`. -/
theorem fold_SS_base {Y : Term} (h : Base Y) : fold (S ⬝ (S ⬝ Y)) = 27 := by
  show β 0 (β 0 (fold Y)) = 27
  rcases fold_base h with e | e <;> rw [e] <;> decide +kernel

/-- `fold G_e = 31`, over either base. -/
theorem fold_Gfam {Y : Term} (h : Base Y) : ∀ e, fold (Gfam Y e) = 31
  | 0 => by
    show β (fold (S ⬝ (S ⬝ Y))) (fold (S ⬝ (S ⬝ Y))) = 31
    rw [fold_SS_base h]; decide +kernel
  | e + 1 => by
    show β (β 0 (fold (Gfam Y e))) (β 0 (β (fold (S ⬝ (S ⬝ Y))) (β 0 (fold (Gfam Y e))))) = 31
    rw [fold_Gfam h e, fold_SS_base h]; decide +kernel

/-- `fold J_e = 31` (here `Jfam Y e` is the note's `J_{e+1}`), over either base. -/
theorem fold_Jfam {Y : Term} (h : Base Y) (e : Nat) : fold (Jfam Y e) = 31 := by
  show β (fold (S ⬝ (S ⬝ Y))) (β 0 (fold (Gfam Y e))) = 31
  rw [fold_Gfam h e, fold_SS_base h]; decide +kernel

/-- `fold (S G_e) = 27`. -/
theorem fold_S_Gfam {Y : Term} (h : Base Y) (e : Nat) : fold (S ⬝ Gfam Y e) = 27 := by
  show β 0 (fold (Gfam Y e)) = 27
  rw [fold_Gfam h e]; exact T8_folds.2.2.2.2.2.2.2.2.2

/-- `fold (S J_e) = 27`. -/
theorem fold_S_Jfam {Y : Term} (h : Base Y) (e : Nat) : fold (S ⬝ Jfam Y e) = 27 := by
  show β 0 (fold (Jfam Y e)) = 27
  rw [fold_Jfam h e]; exact T8_folds.2.2.2.2.2.2.2.2.2

/-- **T8**: `X Y` has no head normal form. -/
theorem T8_XY {Y : Term} (h : Base Y) : ¬ HasHnf (X ⬝ Y) := by
  obtain ⟨h1, _, h3, _⟩ := T8
  refine dead_app pure_X (pure_base h) ?_
  rw [fold_X]
  rcases fold_base h with e | e <;> rw [e] <;> assumption

/-- **T8**: `Y (S Y)` has no head normal form. -/
theorem T8_YSY {Y : Term} (h : Base Y) : ¬ HasHnf (Y ⬝ (S ⬝ Y)) := by
  obtain ⟨_, h2, _, h4, _⟩ := T8
  obtain ⟨_, _, _, _, f16, f34, _⟩ := T8_folds
  refine dead_app (pure_base h) (.app .S (pure_base h)) ?_
  show β (fold Y) (β 0 (fold Y)) = 36
  rcases fold_base h with e | e <;> rw [e]
  · rw [f16]; exact h2
  · rw [f34]; exact h4

/-- **T8**: `X (S Y)` has no head normal form. -/
theorem T8_XSY {Y : Term} (h : Base Y) : ¬ HasHnf (X ⬝ (S ⬝ Y)) := by
  obtain ⟨_, h2, _, _, h5, _⟩ := T8
  refine dead_app pure_X (.app .S (pure_base h)) ?_
  rw [fold_X]
  rcases fold_S_base h with e | e <;> rw [e] <;> assumption

/-- **T8**: `X G_e` has no head normal form. -/
theorem T8_XG {Y : Term} (h : Base Y) (e : Nat) : ¬ HasHnf (X ⬝ Gfam Y e) := by
  refine dead_app pure_X (pure_Gfam (pure_base h) e) ?_
  rw [fold_X, fold_Gfam h e]; exact T8.2.2.2.2.2.1

/-- **T8**: `X J_e` has no head normal form (`Jfam Y e` is the note's `J_{e+1}`). -/
theorem T8_XJ {Y : Term} (h : Base Y) (e : Nat) : ¬ HasHnf (X ⬝ Jfam Y e) := by
  refine dead_app pure_X (pure_Jfam (pure_base h) e) ?_
  rw [fold_X, fold_Jfam h e]; exact T8.2.2.2.2.2.1

/-- **T8**: `Y G_e` has no head normal form. -/
theorem T8_YG {Y : Term} (h : Base Y) (e : Nat) : ¬ HasHnf (Y ⬝ Gfam Y e) := by
  obtain ⟨_, _, _, _, _, h6, _, h8⟩ := T8
  refine dead_app (pure_base h) (pure_Gfam (pure_base h) e) ?_
  rw [fold_Gfam h e]
  rcases fold_base h with e | e <;> rw [e] <;> assumption

/-- **T8**: `Y J_e` has no head normal form (`Jfam Y e` is the note's `J_{e+1}`). -/
theorem T8_YJ {Y : Term} (h : Base Y) (e : Nat) : ¬ HasHnf (Y ⬝ Jfam Y e) := by
  obtain ⟨_, _, _, _, _, h6, _, h8⟩ := T8
  refine dead_app (pure_base h) (pure_Jfam (pure_base h) e) ?_
  rw [fold_Jfam h e]
  rcases fold_base h with e | e <;> rw [e] <;> assumption

/-- **T8**: `G_i (S G_e)` has no head normal form, for all `i`, `e` (in particular
`G_e (S G_e)`). -/
theorem T8_GSG {Y : Term} (h : Base Y) (i e : Nat) : ¬ HasHnf (Gfam Y i ⬝ (S ⬝ Gfam Y e)) := by
  refine dead_app (pure_Gfam (pure_base h) i) (.app .S (pure_Gfam (pure_base h) e)) ?_
  rw [fold_Gfam h i, fold_S_Gfam h e]; exact T8.2.2.2.2.2.2.1

/-- **T8**: `J_e (S J_e)` has no head normal form (`Jfam Y e` is the note's `J_{e+1}`). -/
theorem T8_JSJ {Y : Term} (h : Base Y) (e : Nat) : ¬ HasHnf (Jfam Y e ⬝ (S ⬝ Jfam Y e)) := by
  refine dead_app (pure_Jfam (pure_base h) e) (.app .S (pure_Jfam (pure_base h) e)) ?_
  rw [fold_Jfam h e, fold_S_Jfam h e]; exact T8.2.2.2.2.2.2.1

/-! ### T9 -/

/-- **T9**, the blocks of the right combs: `0, 1, 2, 4, 8, 17, 17, …`. -/
theorem T9_folds : β 0 0 = 1 ∧ β 0 1 = 2 ∧ β 0 2 = 4 ∧ β 0 4 = 8 ∧ β 0 8 = 17 ∧ β 0 17 = 17 := by
  decide +kernel

/-- **T9**, the table fact: `β 16 f` for `f` a block of a right comb. -/
theorem T9 : β 16 0 = 21 ∧ β 16 1 = 31 ∧ β 16 2 = 31 ∧ β 16 4 = 31 ∧ β 16 8 = 31 ∧
    β 16 17 = 31 := by decide +kernel

/-- **T9**, the form used: none of these entries is `36`. -/
theorem T9_ne : ∀ f, f ∈ [0, 1, 2, 4, 8, 17] → β 16 f ≠ 36 := by decide +kernel

/-- The blocks of `c_0, …, c_4`. -/
theorem fold_comb_lt : fold (comb 0) = 0 ∧ fold (comb 1) = 1 ∧ fold (comb 2) = 2 ∧
    fold (comb 3) = 4 ∧ fold (comb 4) = 8 := by decide +kernel

/-- The block of `c_j` is `17` for `j ≥ 5`. -/
theorem fold_comb_ge : ∀ j, fold (comb (j + 5)) = 17
  | 0 => by decide +kernel
  | j + 1 => by
    show β 0 (fold (comb (j + 5))) = 17
    rw [fold_comb_ge j]; exact T9_folds.2.2.2.2.2

theorem fold_comb_mem : ∀ j, fold (comb j) ∈ [0, 1, 2, 4, 8, 17]
  | 0 | 1 | 2 | 3 | 4 => by decide +kernel
  | j + 5 => by rw [fold_comb_ge j]; decide

/-- **T9**, on terms: `X c_j` has a head normal form, for every `j`. -/
theorem T9_hnf (j : Nat) : HasHnf (X ⬝ comb j) := by
  refine sound _ (.app pure_X (pure_comb j)) ?_
  show β (fold X) (fold (comb j)) ≠ 36
  rw [fold_X]
  exact T9_ne _ (fold_comb_mem j)

/-! ### T10: self-dead blocks -/

/-- The self-dead blocks: `w` with `β w (β κ w) = 36` for all 38 blocks `κ`. -/
def SELF : List Nat := r38.filter fun w => r38.all fun k => β w (β k w) == 36

theorem mem_SELF {w : Nat} : w ∈ SELF ↔ w < 38 ∧ ∀ k, k < 38 → β w (β k w) = 36 := by
  simp only [SELF, r38, List.mem_filter, List.mem_range, List.all_eq_true, beq_iff_eq]

/-- **T10**, the table fact. -/
theorem SELF_eq : SELF = [16, 23, 24, 25, 26, 31, 32, 33, 34, 35, 36, 37] := by decide +kernel

/-- **T10**: `SELF` contains `16` (`X`), `34` (`S X c`), `31` (`G_e`, `J_e`, `U_{e+1}`) and
`33` (`U_0`). -/
theorem SELF_fam : ∀ w, w = 16 ∨ w = 34 ∨ w = 31 ∨ w = 33 → w ∈ SELF := by
  rintro w (rfl | rfl | rfl | rfl) <;> decide +kernel

/-- **T10**: `SELF` does not contain `3`, the block of `T`. -/
theorem T10_T : fold T = 3 ∧ 3 ∉ SELF := by decide +kernel

/-- A term whose block is self-dead is self-dead: `W (t W)` has no head normal form, for
every closed `t`. -/
theorem self_dead {W t : Term} (hW : PureS W) (ht : PureS t) (h : fold W ∈ SELF) :
    ¬ HasHnf (W ⬝ (t ⬝ W)) :=
  dead_app hW (.app ht hW) ((mem_SELF.1 h).2 _ (fold_lt ht))

/-- **T10**, on terms: a base `W = X` or `W = S X c` is self-dead. -/
theorem T10_base {W t : Term} (h : Base W) (ht : PureS t) : ¬ HasHnf (W ⬝ (t ⬝ W)) :=
  self_dead (pure_base h) ht <| SELF_fam _ <| by
    rcases fold_base h with e | e
    · exact .inl e
    · exact .inr (.inl e)

/-- **T10**, on terms: `G_e` over either base is self-dead. -/
theorem T10_G {Y t : Term} (h : Base Y) (e : Nat) (ht : PureS t) :
    ¬ HasHnf (Gfam Y e ⬝ (t ⬝ Gfam Y e)) :=
  self_dead (pure_Gfam (pure_base h) e) ht (SELF_fam _ (.inr (.inr (.inl (fold_Gfam h e)))))

/-- **T10**, on terms: `J_e` (`Jfam Y e` is the note's `J_{e+1}`) over either base is self-dead. -/
theorem T10_J {Y t : Term} (h : Base Y) (e : Nat) (ht : PureS t) :
    ¬ HasHnf (Jfam Y e ⬝ (t ⬝ Jfam Y e)) :=
  self_dead (pure_Jfam (pure_base h) e) ht (SELF_fam _ (.inr (.inr (.inl (fold_Jfam h e)))))

/-- **T10**, on terms: `U_e` is self-dead, for every `e`. -/
theorem T10_U {t : Term} (e : Nat) (ht : PureS t) : ¬ HasHnf (Ufam e ⬝ (t ⬝ Ufam e)) :=
  self_dead (pure_Ufam e) ht <| SELF_fam _ <| by
    rw [fold_Ufam]
    rcases fseq_mem e with h | h
    · exact .inr (.inr (.inr h))
    · exact .inr (.inr (.inl h))

/-- `T` is not self-dead: `T (S T)` has a head normal form. -/
theorem T_not_self_dead : HasHnf (T ⬝ (S ⬝ T)) :=
  sound _ (.app pure_T (.app .S pure_T)) (by decide +kernel)


/-! ### T12: stacks are self-dead -/

/-- The blocks of `K2` (two-item terms `S c d`) that some block annihilates: the possible
blocks of a stack `A` with `A w` hnf-less. -/
def STK : List Nat := K2.filter fun a => r38.any fun w => β a w == 36

theorem mem_STK {a : Nat} : a ∈ STK ↔ a ∈ K2 ∧ ∃ w, w < 38 ∧ β a w = 36 := by
  simp only [STK, r38, List.mem_filter, List.mem_range, List.any_eq_true, beq_iff_eq]

theorem STK_eq : STK = [16, 23, 24, 25, 26, 31, 32, 33, 34, 35, 37] := by decide +kernel

/-- **T12**: every stack block is self-dead. -/
theorem T12 : ∀ a, a ∈ STK → a ∈ SELF := by decide +kernel

/-- **Lemma SD**: a two-item term `A = S c d` with `A w` hnf-less for some pure `w` is
self-dead: `A (t A)` has no head normal form for every pure `t`. -/
theorem stack_self_dead {c d w t : Term} (hc : PureS c) (hd : PureS d) (hw : PureS w)
    (ht : PureS t) (h : ¬ HasHnf (S ⬝ c ⬝ d ⬝ w)) :
    ¬ HasHnf (S ⬝ c ⬝ d ⬝ (t ⬝ (S ⬝ c ⬝ d))) := by
  have hA : PureS (S ⬝ c ⬝ d) := .app (.app .S hc) hd
  have h36 : β (fold (S ⬝ c ⬝ d)) (fold w) = 36 := (hnfless_iff (.app hA hw)).1 h
  have hK1 : fold (S ⬝ c) ∈ K1 := mem_K1.2 ⟨fold_lt (.app .S hc), fold c, fold_lt hc, rfl⟩
  have hK2 : fold (S ⬝ c ⬝ d) ∈ K2 :=
    mem_K2.2 ⟨fold_lt hA, fold (S ⬝ c), hK1, fold d, fold_lt hd, rfl⟩
  exact self_dead hA ht (T12 _ (mem_STK.2 ⟨hK2, fold w, fold_lt hw, h36⟩))

/-! ### T11: 2-dead blocks -/

/-- The 2-dead blocks: `w` with `β (β w κ₁) κ₂ = 36` for all blocks `κ₁`, `κ₂`. -/
def DEAD2 : List Nat := r38.filter fun w => r38.all fun k1 => r38.all fun k2 => β (β w k1) k2 == 36

theorem mem_DEAD2 {w : Nat} :
    w ∈ DEAD2 ↔ w < 38 ∧ ∀ k1, k1 < 38 → ∀ k2, k2 < 38 → β (β w k1) k2 = 36 := by
  simp only [DEAD2, r38, List.mem_filter, List.mem_range, List.all_eq_true, beq_iff_eq]

/-- **T11**, the table fact. -/
theorem DEAD2_eq : DEAD2 = [25, 27, 30, 31, 34, 36, 37] := by decide +kernel

/-- **T11**: `DEAD2` does not contain `20` (`S X`) or `18` (`S U_0`). -/
theorem T11_not : fold (S ⬝ X) = 20 ∧ 20 ∉ DEAD2 ∧ fold (S ⬝ U) = 18 ∧ 18 ∉ DEAD2 := by
  decide +kernel

/-- A term whose block is 2-dead is 2-dead: `W p q` has no head normal form, for all closed
`p`, `q`. -/
theorem two_dead {W p q : Term} (hW : PureS W) (hp : PureS p) (hq : PureS q)
    (h : fold W ∈ DEAD2) : ¬ HasHnf (W ⬝ p ⬝ q) :=
  dead_app (.app hW hp) hq ((mem_DEAD2.1 h).2 _ (fold_lt hp) _ (fold_lt hq))

/-- `27 ∈ DEAD2`: the block of the one-item heaps below. -/
theorem DEAD2_27 : 27 ∈ DEAD2 := by decide +kernel

/-- **T11**, on terms: `S (S X c)` is 2-dead, for every closed `c`. -/
theorem T11_SSXc {c p q : Term} (hc : PureS c) (hp : PureS p) (hq : PureS q) :
    ¬ HasHnf (S ⬝ (S ⬝ X ⬝ c) ⬝ p ⬝ q) := by
  refine two_dead (.app .S (pure_base (.sxc hc))) hp hq ?_
  show β 0 (fold (S ⬝ X ⬝ c)) ∈ DEAD2
  rw [fold_SXc hc]; decide +kernel

/-- **T11**, on terms: `S (S Y)` is 2-dead, over either base. -/
theorem T11_SSY {Y p q : Term} (h : Base Y) (hp : PureS p) (hq : PureS q) :
    ¬ HasHnf (S ⬝ (S ⬝ Y) ⬝ p ⬝ q) := by
  refine two_dead (.app .S (.app .S (pure_base h))) hp hq ?_
  rw [fold_SS_base h]; exact DEAD2_27

/-- **T11**, on terms: `S G_e` is 2-dead, over either base. -/
theorem T11_SG {Y p q : Term} (h : Base Y) (e : Nat) (hp : PureS p) (hq : PureS q) :
    ¬ HasHnf (S ⬝ Gfam Y e ⬝ p ⬝ q) := by
  refine two_dead (.app .S (pure_Gfam (pure_base h) e)) hp hq ?_
  rw [fold_S_Gfam h e]; exact DEAD2_27

/-- **T11**, on terms: `S J_e` (`Jfam Y e` is the note's `J_{e+1}`) is 2-dead, over either base. -/
theorem T11_SJ {Y p q : Term} (h : Base Y) (e : Nat) (hp : PureS p) (hq : PureS q) :
    ¬ HasHnf (S ⬝ Jfam Y e ⬝ p ⬝ q) := by
  refine two_dead (.app .S (pure_Jfam (pure_base h) e)) hp hq ?_
  rw [fold_S_Jfam h e]; exact DEAD2_27

/-- **T11**, on terms: `S U_e` is 2-dead for `e ≥ 1`. -/
theorem T11_SU {p q : Term} (e : Nat) (hp : PureS p) (hq : PureS q) :
    ¬ HasHnf (S ⬝ Ufam (e + 1) ⬝ p ⬝ q) := by
  refine two_dead (.app .S (pure_Ufam (e + 1))) hp hq ?_
  show β 0 (fold (Ufam (e + 1))) ∈ DEAD2
  rw [fold_Ufam, fseq_succ]; decide +kernel

/-- `S X` is not 2-dead: `S X S S` has a head normal form. -/
theorem SX_not_two_dead : HasHnf (S ⬝ X ⬝ S ⬝ S) :=
  sound _ (.app (.app (.app .S pure_X) .S) .S) (by decide +kernel)

/-- `S U_0` is not 2-dead: `S U S S` has a head normal form. -/
theorem SU0_not_two_dead : HasHnf (S ⬝ U ⬝ S ⬝ S) :=
  sound _ (.app (.app (.app .S pure_U) .S) .S) (by decide +kernel)

end Lock1Tables
