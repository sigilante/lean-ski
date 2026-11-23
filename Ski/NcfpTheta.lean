import Ski.Ncfp
open Term

/-!
# NCFP: leafless sets, Theorem Θ and its relatives

Source: `notes/NCFP-proof.md`, §11.  Setting and notation as in `Ski/Ncfp.lean`.

A *frame* is a closed S-term read as its head `S` followed by its items; a head step is
`S x y z w⃗ → x z (y z) w⃗`, with the *seats* of `x`, `y`, `z` and the *mint* `y z`.  An item `o` of
a frame is written here as a decomposition `apps (c ⬝ o) L`: `o` is the last item of the prefix
`c ⬝ o`, and `L` lists the items behind it.

What is proved:

* `lemma_TD` (Lemma TD, tail discipline), `lemma_SS`, `lemma_SS_sz` (Lemma SS, shape) and
  `cor_SS1` (an SS-chain loses 2 in leaf count per link).
* For a leafless set `Z` (`Leafless`): `lemma_ZA_two`, `lemma_ZA_one` (Lemma ZA), `lemma_NH`
  (Lemma NH), `track_step` (seats and successors of an item), `track_run` and `lemma_ZI_i`
  (Lemma ZI (i)), `lemma_ZI_ii` (Lemma ZI (ii)).
* `theta` (Theorem Θ): no set of closed S-terms in which every member has a two-item head normal
  form with both items in the set has a member.
* `ncfp_two` (Corollary Θ1): NCFP for contexts built from holes by `E ↦ S E′ E″` alone; `no_S_p_p`.
* `theta'` (Theorem Θ′), `no_S_p_Sp`, `no_SSS_p`; `theta''` (Theorem Θ″), `no_S_Sp_p`.

Item-wise convertibility of head normal forms (the proof of S6 Lemma 4: Church–Rosser and
standardization) is `hnf1_conv`, `hnf2_conv`.

What is not proved: NCFP itself; the conjecture that no leafless set exists; the note's remark on
`p =β S (S p) (S p)`.  Lemma TD is stated without the exclusivity of its two cases and without the
clause that every frame before the head normal form has last item `z` in case (A); nothing below
uses them.

All statements about sets are in predicate form (a set is a predicate closed under the stated
condition), and all proofs are constructive: "a member of least size" is strong induction on the
leaf count.
-/

namespace Ncfp
open HnfS HeadRec Conv

/-! ## Lemma TD, Lemma SS -/

/-- **Lemma TD** (tail discipline).  Let the head run of the closed S-term `t` take at least one
step to the two-item head normal form `S z b`.  Then the last frame is `S S y z` and `b = y z`,
and
(A) `t = t⁻ z` and `t⁻` head-reduces to `S S y`, or
(B) the run passes through a three-item frame `S x p q` with `x ≠ S`, `z = p q`, and `x q`
head-reduces to `S S y`.

Not stated: that (A) and (B) exclude each other, that the frame in (B) is the last three-item
frame before the last frame, and that in (A) every frame has last item `z`. -/
theorem lemma_TD {t z b : Term} (ht : PureS t) (h : Plus t (S ⬝ z ⬝ b)) :
    ∃ y, b = y ⬝ z ∧ Steps t (S ⬝ S ⬝ y ⬝ z) ∧
      ((∃ tm, t = tm ⬝ z ∧ Steps tm (S ⬝ S ⬝ y)) ∨
       (∃ x p q, Steps t (S ⬝ x ⬝ p ⬝ q) ∧ x ≠ S ∧ z = p ⬝ q ∧ Steps (x ⬝ q) (S ⬝ S ⬝ y))) := by
  obtain ⟨y, hlast, eb⟩ := lemma_L ht h
  obtain ⟨_, s, _⟩ := h
  obtain ⟨e, l, et⟩ := step_app s
  refine ⟨y, eb, hlast, ?_⟩
  rcases last_root hlast et ht with ⟨e', he, hs⟩ | ⟨x, p, q, e', h1, h2, h3⟩
  · injection he with e1 e2
    rw [← e1] at hs
    exact .inl ⟨e, by rw [et, e2], hs⟩
  · injection h2 with e1 e2
    rw [← e1] at h3
    refine .inr ⟨x, p, q, h1, ?_, e2, h3⟩
    intro ex
    rw [ex] at h3
    have e3 := InfNF.steps_from_hnf (.inr (.inl ⟨q, rfl⟩)) h3
    injection e3 with e4 _
    cases e4

/-- `appS k t = t S ⋯ S` with `k` trailing `S`. -/
def appS : Nat → Term → Term
  | 0, t => t
  | k + 1, t => appS k t ⬝ S

theorem sz_appS (k : Nat) (t : Term) : sz (appS k t) = sz t + k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have e : sz (appS (k + 1) t) = sz (appS k t) + 1 := rfl
    omega

/-- **Lemma SS** (shape).  If the closed S-term `φ` head-reduces to `S S y`, then
`φ = S S c S ⋯ S` and `y = c S ⋯ S` with the same number of trailing `S`. -/
theorem lemma_SS : ∀ (n : Nat) (φ y : Term), sz φ ≤ n → PureS φ → Steps φ (S ⬝ S ⬝ y) →
    ∃ c k, φ = appS k (S ⬝ S ⬝ c) ∧ y = appS k c := by
  intro n
  induction n with
  | zero =>
    intro φ y h
    have := sz_pos φ
    exfalso
    omega
  | succ n ih =>
    intro φ y hsz hp hs
    rcases Decidable.em (φ = S ⬝ S ⬝ y) with e | ne
    · exact ⟨y, 0, e, rfl⟩
    · obtain ⟨h, y', e1, e2, hs'⟩ := ss_link hp (plus_of_steps_ne hs ne)
      rw [e1] at hsz hp
      have e3 : sz (h ⬝ S) = sz h + 1 := rfl
      obtain ⟨c, k, e4, e5⟩ := ih h y' (by omega) hp.app_inv.1 hs'
      exact ⟨c, k + 1, e1.trans (congrArg (· ⬝ S) e4), e2.trans (congrArg (· ⬝ S) e5)⟩

/-- Lemma SS, the size clause: `|φ| = |y| + 2`. -/
theorem lemma_SS_sz {φ y : Term} (hp : PureS φ) (hs : Steps φ (S ⬝ S ⬝ y)) : sz φ = sz y + 2 := by
  obtain ⟨c, k, e1, e2⟩ := lemma_SS (sz φ) φ y (Nat.le_refl _) hp hs
  rw [e1, e2, sz_appS, sz_appS]
  have e : sz (S ⬝ S ⬝ c) = 1 + 1 + sz c := rfl
  omega

/-- **Corollary SS1.**  An SS-chain of `L` links from `g` to `g'` has `sz g = sz g' + 2 L`. -/
theorem cor_SS1 {L : Nat} {g g' : Term} (h : SSPath L g g') : PureS g → sz g = sz g' + 2 * L := by
  induction h with
  | zero g => intro _; omega
  | succ hs _ ih =>
    intro hp
    have h1 := lemma_SS_sz hp hs
    have h2 := ih (steps_pure hp hs).app_inv.2
    omega

/-! ## Items of frames -/

theorem stepsK_steps {k : Nat} {t u : Term} (h : StepsK k t u) : Steps t u := by
  induction h with
  | refl t => exact .refl t
  | step s _ ih => exact .step s ih

theorem pure_args : ∀ {L : List Term} {h : Term}, PureS (apps h L) → ∀ x ∈ L, PureS x := by
  intro L
  induction L with
  | nil => intro _ _ x hx; cases hx
  | cons a L ih =>
    intro h hp x hx
    rcases List.mem_cons.mp hx with e | h'
    · rw [e]; exact (pure_apps (h := h ⬝ a) hp).app_inv.2
    · exact ih hp x h'

/-- The head step of `m w⃗`: inside `m`, or `m` is `S x y`, `S x` or `S` and the step is the root
step of the frame. -/
theorem step_apps_inv : ∀ (L : List Term) (m F' : Term), PureS (apps m L) → Step (apps m L) F' →
    (∃ m', Step m m' ∧ F' = apps m' L) ∨
    (∃ x y z L', m = S ⬝ x ⬝ y ∧ L = z :: L' ∧ F' = apps (x ⬝ z ⬝ (y ⬝ z)) L') ∨
    (∃ x y z L', m = S ⬝ x ∧ L = y :: z :: L' ∧ F' = apps (x ⬝ z ⬝ (y ⬝ z)) L') ∨
    (∃ x y z L', m = S ∧ L = x :: y :: z :: L' ∧ F' = apps (x ⬝ z ⬝ (y ⬝ z)) L') := by
  intro L
  induction L with
  | nil => intro m F' _ s; exact .inl ⟨F', s, rfl⟩
  | cons a L ih =>
    intro m F' hp s
    rcases ih (m ⬝ a) F' hp s with ⟨m'', s', e⟩ | ⟨x, y, z, L', em, eL, eF⟩ |
      ⟨x, y, z, L', em, eL, eF⟩ | ⟨x, y, z, L', em, _, _⟩
    · rcases step_inv (pure_apps (h := m ⬝ a) hp).app_inv.1 s' with ⟨m', sm, e1⟩ | ⟨f, g, e1, e2⟩
      · exact .inl ⟨m', sm, e.trans (congrArg (fun m => apps m L) e1)⟩
      · exact .inr (.inl ⟨f, g, a, L, e1, rfl, e.trans (congrArg (fun m => apps m L) e2)⟩)
    · injection em with e1 e2
      exact .inr (.inr (.inl ⟨x, y, z, L', e1, by rw [e2, eL], eF⟩))
    · injection em with e1 e2
      exact .inr (.inr (.inr ⟨x, y, z, L', e1, by rw [e2, eL], eF⟩))
    · cases em

/-- **Seats and successors.**  A head step from a frame with item `o` (`apps (c ⬝ o) L`):
(T1) `o` is behind the `z`-seat and rides: the next frame is `apps (c' ⬝ o) L`;
(T2) `o` is at the `z`-seat: it is copied, and the mint `g o` is inserted behind it;
(T3) `o` is at the `y`-seat: the next frame has the mint `o z` as an item;
(T4) `o` is at the `x`-seat: the next frame is `o z (y z) w⃗`. -/
theorem track_step {c o F' : Term} {L : List Term} (hp : PureS (apps (c ⬝ o) L))
    (s : Step (apps (c ⬝ o) L) F') :
    (∃ c', F' = apps (c' ⬝ o) L) ∨
    (∃ f g, c = S ⬝ f ⬝ g ∧ F' = apps (f ⬝ o) ((g ⬝ o) :: L)) ∨
    (∃ x z L', c = S ⬝ x ∧ L = z :: L' ∧ F' = apps (x ⬝ z ⬝ (o ⬝ z)) L') ∨
    (∃ y z L', c = S ∧ L = y :: z :: L' ∧ F' = apps (o ⬝ z ⬝ (y ⬝ z)) L') := by
  rcases step_apps_inv L (c ⬝ o) F' hp s with ⟨m', s', e⟩ | ⟨x, y, z, L', em, eL, eF⟩ |
    ⟨x, y, z, L', em, eL, eF⟩ | ⟨x, y, z, L', em, _, _⟩
  · rcases step_inv (pure_apps hp).app_inv.1 s' with ⟨c', _, e1⟩ | ⟨f, g, e1, e2⟩
    · exact .inl ⟨c', by rw [e, e1]⟩
    · exact .inr (.inl ⟨f, g, e1, e.trans (congrArg (fun m => apps m L) e2)⟩)
  · injection em with e1 e2
    exact .inr (.inr (.inl ⟨x, z, L', e1, eL, by rw [eF, e2]⟩))
  · injection em with e1 e2
    exact .inr (.inr (.inr ⟨y, z, L', e1, eL, by rw [eF, e2]⟩))
  · cases em

theorem apps_app_ne_S (c o : Term) (L : List Term) : apps (c ⬝ o) L ≠ S := by
  intro e
  have h := sz_le_apps (c ⬝ o) L
  rw [e] at h
  have := sz_pos c
  have := sz_pos o
  have e1 : sz (c ⬝ o) = sz c + sz o := rfl
  have e2 : sz S = 1 := rfl
  omega

theorem apps_eq_S1 {c o a : Term} {L : List Term} (e : apps (c ⬝ o) L = S ⬝ a) :
    c = S ∧ o = a ∧ L = [] := by
  rcases apps_eq_app e with ⟨eL, e1⟩ | ⟨L₀, _, e1⟩
  · injection e1 with e2 e3
    exact ⟨e2, e3, eL⟩
  · exact absurd e1.symm (apps_app_ne_S c o L₀)

theorem apps_eq_S2 {c o a b : Term} {L : List Term} (e : apps (c ⬝ o) L = S ⬝ a ⬝ b) :
    (c = S ⬝ a ∧ o = b ∧ L = []) ∨ (c = S ∧ o = a ∧ L = [b]) := by
  rcases apps_eq_app e with ⟨eL, e1⟩ | ⟨L₀, eL, e1⟩
  · injection e1 with e2 e3
    exact .inl ⟨e2, e3, eL⟩
  · obtain ⟨h1, h2, h3⟩ := apps_eq_S1 e1.symm
    rw [h3] at eL
    exact .inr ⟨h1, h2, eL⟩

/-- An item of the three-item frame `S S y a` with an item behind it is `y` or the first `S`. -/
theorem frame3_item {c o y a : Term} {L : List Term} (e : apps (c ⬝ o) L = S ⬝ S ⬝ y ⬝ a)
    (hl : 1 ≤ L.length) : o = y ∨ o = S := by
  rcases apps_eq_app e with ⟨eL, _⟩ | ⟨L₀, _, e1⟩
  · rw [eL] at hl
    exact absurd hl (by decide)
  · rcases apps_eq_S2 e1.symm with ⟨_, h2, _⟩ | ⟨_, h2, _⟩
    · exact .inl h2
    · exact .inr h2

/-- A head normal form all of whose items have head normal forms. -/
def GoodHnf (H : Term) : Prop :=
  H = S ∨ (∃ a, H = S ⬝ a ∧ fold a ≠ 36) ∨ ∃ a b, H = S ⬝ a ⬝ b ∧ fold a ≠ 36 ∧ fold b ≠ 36

theorem GoodHnf.isHnf {H : Term} (h : GoodHnf H) : IsHnf H := by
  rcases h with e | ⟨a, e, _⟩ | ⟨a, b, e, _, _⟩
  · exact .inl e
  · exact .inr (.inl ⟨a, e⟩)
  · exact .inr (.inr ⟨a, b, e⟩)

/-- **Lemma NH** (no hnf-less items).  If a head run ends in a head normal form whose items all
have head normal forms, no item of any of its frames is hnf-less. -/
theorem lemma_NH {F H : Term} (h : Steps F H) : PureS F → GoodHnf H →
    ∀ (c w : Term) (L : List Term), F = apps (c ⬝ w) L → fold w = 36 → False := by
  induction h with
  | refl t =>
    intro _ hg c w L e hw
    rcases hg with e' | ⟨a, e', ha⟩ | ⟨a, b, e', ha, hb⟩
    · exact apps_app_ne_S c w L (e.symm.trans e')
    · obtain ⟨_, h2, _⟩ := apps_eq_S1 (e.symm.trans e')
      exact ha (by rw [← h2]; exact hw)
    · rcases apps_eq_S2 (e.symm.trans e') with ⟨_, h2, _⟩ | ⟨_, h2, _⟩
      · exact hb (by rw [← h2]; exact hw)
      · exact ha (by rw [← h2]; exact hw)
  | step s rest ih =>
    intro hp hg c w L e hw
    subst e
    have hp' := (wstep_pure s.weak hp).1
    rcases track_step hp s with ⟨c', e'⟩ | ⟨f, g, _, e'⟩ | ⟨x, z, L', _, _, e'⟩ |
      ⟨y, z, L', _, _, e'⟩
    · exact ih hp' hg c' w L e' hw
    · exact ih hp' hg f w _ e' hw
    · have hp'' := hp'
      rw [e'] at hp''
      have hz := (pure_apps hp'').app_inv.2.app_inv.2
      exact ih hp' hg (x ⬝ z) (w ⬝ z) L' e' (Full.fold_frame hz hw)
    · have hp'' := hp'
      rw [e'] at hp''
      have hin := pure_apps hp''
      have h36 : fold (apps (w ⬝ z ⬝ (y ⬝ z)) L') = 36 :=
        fold_apps (Full.fold_frame hin.app_inv.2 (Full.fold_frame hin.app_inv.1.app_inv.2 hw)) L'
          (pure_args hp'')
      rw [← e'] at h36
      exact fold_hnf (steps_pure hp' rest) hg.isHnf ((InfNF.steps_fold hp' rest).trans h36)

/-! ## Leafless sets -/

/-- `Z` is *leafless*: every member is a closed S-term with a head normal form of one or two
items, all in `Z`. -/
def Leafless (Z : Term → Prop) : Prop :=
  ∀ t, Z t → PureS t ∧
    ((∃ a, Steps t (S ⬝ a) ∧ Z a) ∨ ∃ a b, Steps t (S ⬝ a ⬝ b) ∧ Z a ∧ Z b)

/-- A member of kind 2: its head normal form has two items. -/
def K2 (Z : Term → Prop) (o : Term) : Prop := Z o ∧ ∃ a b, Steps o (S ⬝ a ⬝ b)

theorem Leafless.fold_ne {Z : Term → Prop} (hZ : Leafless Z) {v : Term} (hv : Z v) :
    fold v ≠ 36 := by
  obtain ⟨hp, hk⟩ := hZ v hv
  intro e
  rcases hk with ⟨a, hs, _⟩ | ⟨a, b, hs, _, _⟩
  · exact fold_hnf (steps_pure hp hs) (.inr (.inl ⟨a, rfl⟩)) ((InfNF.steps_fold hp hs).trans e)
  · exact fold_hnf (steps_pure hp hs) (.inr (.inr ⟨a, b, rfl⟩)) ((InfNF.steps_fold hp hs).trans e)

/-- The set `W` of Lemma ZA: a member applied to two or more terms, or a member of kind 2
applied to one or more terms. -/
inductive WZ (Z : Term → Prop) : Term → Prop
  | two {v w₁ w₂ : Term} {L : List Term} : Z v → PureS w₁ → PureS w₂ → (∀ x ∈ L, PureS x) →
      WZ Z (apps (v ⬝ w₁ ⬝ w₂) L)
  | one {v w₁ : Term} {L : List Term} : Z v → (∃ a b, Steps v (S ⬝ a ⬝ b)) → PureS w₁ →
      (∀ x ∈ L, PureS x) → WZ Z (apps (v ⬝ w₁) L)

theorem WZ.pure {Z : Term → Prop} (hZ : Leafless Z) {X : Term} (h : WZ Z X) : PureS X := by
  cases h with
  | two hv h1 h2 hL => exact pure_apps_of (.app (.app (hZ _ hv).1 h1) h2) _ hL
  | one hv _ h1 hL => exact pure_apps_of (.app (hZ _ hv).1 h1) _ hL

/-- Every member of `W` head-reduces in one or more steps to a member of `W`. -/
theorem wz_step {Z : Term → Prop} (hZ : Leafless Z) {X : Term} (h : WZ Z X) :
    ∃ X', WZ Z X' ∧ Plus X X' := by
  have one_case : ∀ {v w₁ : Term} {L : List Term}, Z v → (∃ a b, Steps v (S ⬝ a ⬝ b)) →
      PureS w₁ → (∀ x ∈ L, PureS x) → ∃ X', WZ Z X' ∧ Plus (apps (v ⬝ w₁) L) X' := by
    intro v w₁ L hv hk0 hw hL
    obtain ⟨a0, b0, hs0⟩ := hk0
    obtain ⟨hpv, hk⟩ := hZ v hv
    rcases hk with ⟨a, hs, _⟩ | ⟨a, b, hs, ha, _⟩
    · have e := run_hnf_hnf (.inr (.inl ⟨a, rfl⟩)) (.inr (.inr ⟨a0, b0, rfl⟩)) hs hs0
      injection e with e1 _
      cases e1
    · have hb := (steps_pure hpv hs).app_inv.2
      refine ⟨apps (a ⬝ w₁ ⬝ (b ⬝ w₁)) L, .two ha hw (.app hb hw) hL, ?_⟩
      have h1 : Steps (apps (v ⬝ w₁) L) (apps (S ⬝ a ⬝ b ⬝ w₁) L) :=
        steps_apps L (Steps.left w₁ hs)
      exact steps_step_plus h1 (step_apps L (.S a b w₁))
  cases h with
  | @two v w₁ w₂ L hv h1 h2 hL =>
    obtain ⟨hpv, hk⟩ := hZ v hv
    rcases hk with ⟨a, hs, ha⟩ | ⟨a, b, hs, _, _⟩
    · have e := hnf1_literal hpv hs
      rw [e]
      exact ⟨apps (a ⬝ w₂ ⬝ (w₁ ⬝ w₂)) L, .two ha h2 (.app h1 h2) hL,
        ⟨_, step_apps L (.S a w₁ w₂), .refl _⟩⟩
    · exact one_case (L := w₂ :: L) hv ⟨a, b, hs⟩ h1 (fun x hx => by
        rcases List.mem_cons.mp hx with e | h'
        · rw [e]; exact h2
        · exact hL x h')
  | @one v w₁ L hv hk h1 hL => exact one_case hv hk h1 hL

theorem wz_no_hnf {Z : Term → Prop} (hZ : Leafless Z) : ∀ (n k : Nat) (X H : Term), k ≤ n →
    WZ Z X → StepsK k X H → IsHnf H → False := by
  have next : ∀ (k : Nat) (X H : Term), WZ Z X → StepsK k X H → IsHnf H →
      ∃ k' X', k' < k ∧ WZ Z X' ∧ StepsK k' X' H := by
    intro k X H hW hrun hH
    obtain ⟨X', hW', hplus⟩ := wz_step hZ hW
    have hX'H : Steps X' H := by
      rcases InfNF.steps_cmp hplus.steps (stepsK_steps hrun) with h | h
      · exact h
      · rw [InfNF.steps_from_hnf hH h]
        exact .refl _
    obtain ⟨k', hlt, hk'⟩ := stepsK_plus (hW.pure hZ) hrun hplus hX'H
    exact ⟨k', X', hlt, hW', hk'⟩
  intro n
  induction n with
  | zero =>
    intro k X H hk hW hrun hH
    obtain ⟨k', X', hlt, _, _⟩ := next k X H hW hrun hH
    omega
  | succ n ih =>
    intro k X H hk hW hrun hH
    obtain ⟨k', X', hlt, hW', hk'⟩ := next k X H hW hrun hH
    exact ih k' X' H (by omega) hW' hk' hH

theorem wz_bot {Z : Term → Prop} (hZ : Leafless Z) {X : Term} (hW : WZ Z X) : fold X = 36 := by
  have hp := hW.pure hZ
  rcases Nat.decEq (fold X) 36 with hne | heq
  · exfalso
    obtain ⟨T, hs, hT⟩ := reach_frame hp
    rcases hT with hh | ⟨f, w, e, hf⟩
    · obtain ⟨k, hk⟩ := stepsK_of_steps hs
      exact wz_no_hnf hZ k k X T (Nat.le_refl _) hW hk hh
    · rw [e] at hs
      exact hne ((InfNF.steps_fold hp hs).symm.trans
        (Full.fold_frame (steps_pure hp hs).app_inv.2 hf))
  · exact heq

/-- **Lemma ZA**, first half: a member of a leafless set applied to two or more closed terms is
hnf-less. -/
theorem lemma_ZA_two {Z : Term → Prop} (hZ : Leafless Z) {v w₁ w₂ : Term} {L : List Term}
    (hv : Z v) (h1 : PureS w₁) (h2 : PureS w₂) (hL : ∀ x ∈ L, PureS x) :
    fold (apps (v ⬝ w₁ ⬝ w₂) L) = 36 :=
  wz_bot hZ (.two hv h1 h2 hL)

/-- **Lemma ZA**, second half: a member of kind 2 applied to one or more closed terms is
hnf-less. -/
theorem lemma_ZA_one {Z : Term → Prop} (hZ : Leafless Z) {v w₁ : Term} {L : List Term}
    (hv : K2 Z v) (h1 : PureS w₁) (hL : ∀ x ∈ L, PureS x) : fold (apps (v ⬝ w₁) L) = 36 :=
  wz_bot hZ (.one hv.1 hv.2 h1 hL)

/-- **Lemma ZI (i)**, run form.  Let `o` be a member of kind 2 of a leafless set and an item of
a frame `F` whose head run ends in a head normal form `H` with items that have head normal forms.
Then `o` is an item of every later frame `X` of the run, with at least as many items behind it:
it is never at the `x`-seat or the `y`-seat, and items behind it are never removed. -/
theorem track_run {Z : Term → Prop} (hZ : Leafless Z) {o : Term} (ho : K2 Z o) {F X : Term}
    (h : Steps F X) : PureS F → ∀ H, Steps X H → GoodHnf H →
    ∀ (c : Term) (L : List Term), F = apps (c ⬝ o) L →
      ∃ c' L', X = apps (c' ⬝ o) L' ∧ L.length ≤ L'.length := by
  induction h with
  | refl t => intro _ _ _ _ c L e; exact ⟨c, L, e, Nat.le_refl _⟩
  | step s rest ih =>
    intro hp H hXH hg c L e
    subst e
    have hp' := (wstep_pure s.weak hp).1
    rcases track_step hp s with ⟨c', e'⟩ | ⟨f, g, _, e'⟩ | ⟨x, z, L', _, _, e'⟩ |
      ⟨y, z, L', _, _, e'⟩
    · exact ih hp' H hXH hg c' L e'
    · obtain ⟨c'', L'', e2, hl⟩ := ih hp' H hXH hg f _ e'
      exact ⟨c'', L'', e2, Nat.le_trans (Nat.le_succ _) hl⟩
    · exfalso
      have hp'' := hp'
      rw [e'] at hp''
      have hz := (pure_apps hp'').app_inv.2.app_inv.2
      have h36 : fold (o ⬝ z) = 36 :=
        lemma_ZA_one hZ ho hz (L := []) (fun _ hx => by cases hx)
      exact lemma_NH (rest.trans hXH) hp' hg (x ⬝ z) (o ⬝ z) L' e' h36
    · exfalso
      have hp'' := hp'
      rw [e'] at hp''
      have hin := pure_apps hp''
      have h36 : fold (apps (o ⬝ z ⬝ (y ⬝ z)) L') = 36 :=
        lemma_ZA_two hZ ho.1 hin.app_inv.1.app_inv.2 hin.app_inv.2 (pure_args hp'')
      rw [← e'] at h36
      have hrun := rest.trans hXH
      exact fold_hnf (steps_pure hp' hrun) hg.isHnf ((InfNF.steps_fold hp' hrun).trans h36)

/-- **Lemma ZI (i).**  A member of kind 2 of a leafless set that is an item of a frame of a head
run ending in a head normal form with items that have head normal forms is an item of that head
normal form. -/
theorem lemma_ZI_i {Z : Term → Prop} (hZ : Leafless Z) {o : Term} (ho : K2 Z o) {F H c : Term}
    {L : List Term} (hp : PureS F) (e : F = apps (c ⬝ o) L) (h : Steps F H) (hg : GoodHnf H) :
    H = S ⬝ o ∨ (∃ b, H = S ⬝ o ⬝ b) ∨ ∃ a, H = S ⬝ a ⬝ o := by
  obtain ⟨c', L', e', _⟩ := track_run hZ ho h hp H (.refl _) hg c L e
  rcases hg with e0 | ⟨a, e1, _⟩ | ⟨a, b, e2, _, _⟩
  · exact absurd (e'.symm.trans e0) (apps_app_ne_S c' o L')
  · obtain ⟨_, h2, _⟩ := apps_eq_S1 (e'.symm.trans e1)
    exact .inl (by rw [e1, h2])
  · rcases apps_eq_S2 (e'.symm.trans e2) with ⟨_, h2, _⟩ | ⟨_, h2, _⟩
    · exact .inr (.inr ⟨a, by rw [e2, h2]⟩)
    · exact .inr (.inl ⟨b, by rw [e2, h2]⟩)

/-- `IsItem a X`: `a` is an item of the frame `X`. -/
inductive IsItem (a : Term) : Term → Prop
  | last (c : Term) : IsItem a (c ⬝ a)
  | init {c : Term} (o : Term) : IsItem a c → IsItem a (c ⬝ o)

/-- `ItemSub a X`: `a` is a subterm of an item of the frame `X`. -/
inductive ItemSub (a : Term) : Term → Prop
  | last (c : Term) {o : Term} : HeadRec.Sub a o → ItemSub a (c ⬝ o)
  | init {c : Term} (o : Term) : ItemSub a c → ItemSub a (c ⬝ o)

theorem IsItem.apps {a X : Term} (h : IsItem a X) : ∃ c L, X = apps (c ⬝ a) L := by
  induction h with
  | last c => exact ⟨c, [], rfl⟩
  | init o _ ih =>
    obtain ⟨c, L, e⟩ := ih
    exact ⟨c, L ++ [o], by rw [apps_snoc, e]⟩

/-- A subterm of an item is a proper subterm of the frame. -/
theorem ItemSub.psub {a X : Term} (h : ItemSub a X) : PSub a X := by
  induction h with
  | last c hs => exact .right c hs
  | init o _ ih => exact .left o ih.sub

theorem itemsub_step {X X' a : Term} (s : Step X X') : PureS X → ItemSub a X' →
    ItemSub a X ∨ IsItem a X' := by
  induction s with
  | S f g x =>
    intro _ h
    cases h with
    | last c hs =>
      cases hs with
      | refl => exact .inr (.last _)
      | left _ h1 => exact .inl (.init x (.last _ h1))
      | right _ h2 => exact .inl (.last _ h2)
    | init o hi =>
      cases hi with
      | last c hs => exact .inl (.last _ hs)
      | init _ hf => exact .inl (.init x (.init g (.last S hf.psub.sub)))
  | K x y => intro hp; exact absurd hp.app_inv.1.app_inv.1 PureS.not_K
  | I x => intro hp; exact absurd hp.app_inv.1 PureS.not_I
  | left x _ ih =>
    intro hp h
    cases h with
    | last c hs => exact .inl (.last _ hs)
    | init o hi =>
      rcases ih hp.app_inv.1 hi with h1 | h1
      · exact .inl (.init x h1)
      · exact .inr (.init x h1)

/-- **Lemma ZI (ii).**  A subterm of an item of a frame of the head run of `t` is a subterm of an
item of `t`, or it is an item of a frame of the run (a mint, at the frame where it is minted). -/
theorem lemma_ZI_ii {t X a : Term} (h : Steps t X) : PureS t → ItemSub a X →
    ItemSub a t ∨ ∃ X', Steps t X' ∧ IsItem a X' := by
  induction h with
  | refl t => intro _ hi; exact .inl hi
  | step s _ ih =>
    intro hp hi
    rcases ih (wstep_pure s.weak hp).1 hi with h1 | ⟨X', hs, hit⟩
    · rcases itemsub_step s hp h1 with h2 | h2
      · exact .inl h2
      · exact .inr ⟨_, .single s, h2⟩
    · exact .inr ⟨X', .step s hs, hit⟩

/-! ## Theorem Θ -/

/-- `Z` is a set of closed S-terms in which every member has a two-item head normal form with
both items in `Z` (the members are the Θ-terms). -/
def ThetaSet (Z : Term → Prop) : Prop :=
  ∀ t, Z t → PureS t ∧ ∃ a b, Steps t (S ⬝ a ⬝ b) ∧ Z a ∧ Z b

theorem ThetaSet.leafless {Z : Term → Prop} (hZ : ThetaSet Z) : Leafless Z :=
  fun t ht => ⟨(hZ t ht).1, .inr (hZ t ht).2⟩

theorem ThetaSet.k2 {Z : Term → Prop} (hZ : ThetaSet Z) {t : Term} (ht : Z t) : K2 Z t := by
  obtain ⟨_, a, b, hs, _, _⟩ := hZ t ht
  exact ⟨ht, a, b, hs⟩

theorem ThetaSet.not_S {Z : Term → Prop} (hZ : ThetaSet Z) : ¬ Z S := by
  intro h
  obtain ⟨_, a, b, hs, _, _⟩ := hZ S h
  cases steps_S hs

/-- Step 3 and 4 of the proof of Theorem Θ: from `y₀ z ∈ Z` with `z ∈ Z`, the SS-chain
`y₀, y₁, …` with `yₖ z ∈ Z` reaches some `y_K = S a` with `a ∈ Z`. -/
theorem theta_chain {Z : Term → Prop} (hZ : ThetaSet Z) {y₀ z : Term} (hz : Z z) :
    ∀ i : Nat, Z (y₀ ⬝ z) →
      (∃ K a, SSPath K y₀ (S ⬝ a) ∧ Z a) ∨ ∃ y, SSPath i y₀ y ∧ Z (y ⬝ z) := by
  intro i h0
  induction i with
  | zero => exact .inr ⟨y₀, .zero _, h0⟩
  | succ i ih =>
    rcases ih with done | ⟨y, path, hv⟩
    · exact .inl done
    · obtain ⟨hp, a, b, hs, ha, hb⟩ := hZ _ hv
      rcases Decidable.em (y ⬝ z = S ⬝ a ⬝ b) with e | ne
      · injection e with e1 _
        rw [e1] at path
        exact .inl ⟨i, a, path, ha⟩
      · obtain ⟨y', hlast, eb⟩ := lemma_L' hp hs ne
        rcases split hlast rfl hp with ⟨e', he, hs'⟩ | ⟨f, g, h1, h2⟩
        · injection he with e1 e2
          rw [← e1] at hs'
          rw [eb, e2] at hb
          exact .inr ⟨y', path.snoc hs', hb⟩
        · exfalso
          have hfg := steps_pure hp.app_inv.1 h1
          have hpz := hp.app_inv.2
          have hpF : PureS (f ⬝ z ⬝ (g ⬝ z)) :=
            .app (.app hfg.app_inv.1.app_inv.2 hpz) (.app hfg.app_inv.2 hpz)
          have hg : GoodHnf (S ⬝ a ⬝ b) :=
            .inr (.inr ⟨a, b, rfl, hZ.leafless.fold_ne ha, hZ.leafless.fold_ne hb⟩)
          have hXH : Steps (S ⬝ S ⬝ y' ⬝ a) (S ⬝ a ⬝ b) := by
            rw [eb]
            exact .single (.S S y' a)
          obtain ⟨c', L', eX, hl⟩ := track_run hZ.leafless (hZ.k2 hz) h2 hpF _ hXH hg f
            [g ⬝ z] rfl
          rcases frame3_item eX.symm hl with e1 | e1
          · have hpa := (steps_pure hp hs).app_inv.1.app_inv.2
            have h36 : fold (z ⬝ a) = 36 :=
              lemma_ZA_one hZ.leafless (hZ.k2 hz) hpa (L := []) (fun _ hx => by cases hx)
            rw [eb, ← e1] at hb
            exact hZ.leafless.fold_ne hb h36
          · rw [e1] at hz
            exact hZ.not_S hz

theorem theta_aux {Z : Term → Prop} (hZ : ThetaSet Z) :
    ∀ (n : Nat) (t : Term), sz t ≤ n → Z t → False := by
  intro n
  induction n with
  | zero =>
    intro t h _
    have := sz_pos t
    omega
  | succ n ih =>
    intro t hsz hZt
    obtain ⟨ht, tL, tR, hs, hL, hR⟩ := hZ t hZt
    rcases Decidable.em (t = S ⬝ tL ⬝ tR) with e | ne
    · have hlt : sz tL < sz t := by
        rw [e]
        exact Nat.lt_trans (sz_arg_lt S tL) (sz_fun_lt _ tR)
      exact ih tL (by omega) hL
    · obtain ⟨y, eR, hlast, hcase⟩ := lemma_TD ht (plus_of_steps_ne hs ne)
      rcases hcase with ⟨tm, e, _⟩ | ⟨x, p, q, hfr, _, eL, hφ⟩
      · have hlt : sz tL < sz t := by
          rw [e]
          exact sz_arg_lt tm tL
        exact ih tL (by omega) hL
      · have hy : PureS y := (steps_pure ht hlast).app_inv.1.app_inv.2
        have hRy : Z (y ⬝ tL) := by rw [← eR]; exact hR
        -- steps 3, 4: the chain ends in `S a`, `a ∈ Z`
        obtain ⟨K, a, path, ha⟩ : ∃ K a, SSPath K y (S ⬝ a) ∧ Z a := by
          rcases theta_chain hZ hL (2 * sz y + 1) hRy with done | ⟨y', path, _⟩
          · exact done
          · have := ss_bound (sz y) y (Nat.le_refl _) hy _ _ path
            exfalso
            omega
        -- step 5: the chain is literal
        have hne : a ≠ S := by
          intro e
          rw [e] at ha
          exact hZ.not_S ha
        have hr : Rigid a y := sspath_rigid hne hy path .base
        -- step 6: `x q = S S y`
        have hpfr := steps_pure ht hfr
        have hpxq : PureS (x ⬝ q) := .app hpfr.app_inv.1.app_inv.1.app_inv.2 hpfr.app_inv.2
        have eqy : q = y := by
          rcases Decidable.em (x ⬝ q = S ⬝ S ⬝ y) with e | ne'
          · exact (Term.app.inj e).2
          · obtain ⟨y'', _, e⟩ := lemma_L' hpxq hφ ne'
            exact absurd e (hr.not_appS hne y'')
        have hsub : ItemSub a (S ⬝ x ⬝ p ⬝ q) := by
          rw [eqy]
          exact .last _ hr.sub
        rcases lemma_ZI_ii hfr ht hsub with h1 | ⟨X', hX', hit⟩
        · exact ih a (by have := h1.psub.sz_lt; omega) ha
        · obtain ⟨c, L, eX⟩ := hit.apps
          have hXH : Steps X' (S ⬝ tL ⬝ tR) := by
            rcases InfNF.steps_cmp hX' hs with h | h
            · exact h
            · rw [InfNF.steps_from_hnf (.inr (.inr ⟨tL, tR, rfl⟩)) h]
              exact .refl _
          have hg : GoodHnf (S ⬝ tL ⬝ tR) :=
            .inr (.inr ⟨tL, tR, rfl, hZ.leafless.fold_ne hL, hZ.leafless.fold_ne hR⟩)
          have h1 := hr.sz_lt
          have h2 := sz_arg_lt p q
          have h3 := sz_arg_lt y tL
          rw [← eL] at h2
          rw [← eR] at h3
          rw [eqy] at h2
          rcases lemma_ZI_i hZ.leafless (hZ.k2 ha) (steps_pure ht hX') eX hXH hg with e | ⟨b, e⟩ |
            ⟨a', e⟩
          · injection e with e1 _
            cases e1
          · injection e with e1 _
            injection e1 with _ e2
            rw [e2] at h2
            omega
          · injection e with _ e2
            rw [e2] at h3
            omega

/-- **Theorem Θ.**  Let `Z` be a set of closed S-terms such that every member has, on its head
run, a two-item head normal form with both items in `Z`.  Then `Z` is empty: there is no Θ-term.

Uses Lemma TD, the SS-chain bound, Lemmas ZA, NH, ZI and, through `Rigid` and `lemma_L`, the
shape of SS-chains; `HeadRec.no_head_cycle` enters through the counted head runs of Lemma ZA.
Unlike the note's proof it does not use `HeadRec.no_ground_loop`: the subterm of step 6 is a
subterm of an *item* of `t`, hence a smaller member. -/
theorem theta {Z : Term → Prop} (hZ : ThetaSet Z) : ∀ t, ¬ Z t :=
  fun t h => theta_aux hZ (sz t) t (Nat.le_refl _) h

/-! ## Item-wise convertibility of head normal forms (S6 Lemma 4, proof) -/

/-- A closed S-term convertible to `S a` is `S a'` with `a' =β a`. -/
theorem hnf1_conv {t a : Term} (ht : PureS t) (ha : PureS a) (h : Convertible t (S ⬝ a)) :
    ∃ a', t = S ⬝ a' ∧ Convertible a' a := by
  obtain ⟨w, h1, h2⟩ := conv_iff_join.mp h
  obtain ⟨r', e, hr⟩ := hnf1_wsteps (.app .S ha) h2
  rw [e] at h1
  obtain ⟨T, hs, hi⟩ := wsteps_split h1
  obtain ⟨f, r'', e', hf, hr''⟩ := parIs_app hi
  rw [e', parIs_S hf] at hs
  exact ⟨r'', hnf1_literal ht hs, conv_iff_join.mpr ⟨r', hr'', hr⟩⟩

/-- A closed S-term convertible to `S a b` has, on its head run, a head normal form `S a' b'`
with `a' =β a` and `b' =β b`. -/
theorem hnf2_conv {t a b : Term} (_ht : PureS t) (ha : PureS a) (hb : PureS b)
    (h : Convertible t (S ⬝ a ⬝ b)) :
    ∃ a' b', Steps t (S ⬝ a' ⬝ b') ∧ Convertible a' a ∧ Convertible b' b := by
  obtain ⟨w, h1, h2⟩ := conv_iff_join.mp h
  obtain ⟨a₁, b₁, e, ha₁, hb₁⟩ := hnf2_wsteps (.app (.app .S ha) hb) h2
  rw [e] at h1
  obtain ⟨T, hs, hi⟩ := wsteps_split h1
  obtain ⟨g, b₂, e', hg, hb₂⟩ := parIs_app hi
  obtain ⟨f, a₂, e'', hf, ha₂⟩ := parIs_app hg
  rw [e', e'', parIs_S hf] at hs
  exact ⟨a₂, b₂, hs, conv_iff_join.mpr ⟨a₁, ha₂, ha₁⟩, conv_iff_join.mpr ⟨b₁, hb₂, hb₁⟩⟩

/-! ## Corollary Θ1 -/

/-- Contexts built from holes by `E ↦ S E′ E″` alone: every leaf is a hole. -/
inductive TwoCtx : Phi.Ctx → Prop
  | hole : TwoCtx .hole
  | node {E₁ E₂ : Phi.Ctx} : TwoCtx E₁ → TwoCtx E₂ → TwoCtx (.app (.app .s E₁) E₂)

/-- **Corollary Θ1.**  Let `E ≠ hole` be built from holes by `E ↦ S E′ E″` alone.  Then no closed
S-term `p` is convertible to `E[p]`. -/
theorem ncfp_two {p : Term} (hp : PureS p) {E : Phi.Ctx} (hE : TwoCtx E) (hne : E ≠ .hole) :
    ¬ Convertible p (E.plug p) := by
  intro hc
  have key : ∀ E' : Phi.Ctx, TwoCtx E' → E' ≠ .hole → ∀ t, PureS t →
      Convertible t (E'.plug p) →
      ∃ a b, Steps t (S ⬝ a ⬝ b) ∧ (PureS a ∧ ∃ E'', TwoCtx E'' ∧ Convertible a (E''.plug p)) ∧
        (PureS b ∧ ∃ E'', TwoCtx E'' ∧ Convertible b (E''.plug p)) := by
    intro E' hE' hne' t ht hct
    cases hE' with
    | hole => exact absurd rfl hne'
    | @node E₁ E₂ h1 h2 =>
      have hct' : Convertible t (S ⬝ E₁.plug p ⬝ E₂.plug p) := hct
      obtain ⟨a, b, hs, ca, cb⟩ :=
        hnf2_conv ht (Tower.plug_pure E₁ hp) (Tower.plug_pure E₂ hp) hct'
      have hpab := steps_pure ht hs
      exact ⟨a, b, hs, ⟨hpab.app_inv.1.app_inv.2, E₁, h1, ca⟩, ⟨hpab.app_inv.2, E₂, h2, cb⟩⟩
  have hZ : ThetaSet (fun t => PureS t ∧ ∃ E', TwoCtx E' ∧ Convertible t (E'.plug p)) := by
    rintro t ⟨ht, E', hE', hct⟩
    refine ⟨ht, ?_⟩
    cases hE' with
    | hole =>
      have hct0 : Convertible t p := hct
      exact key E hE hne t ht (hct0.trans hc)
    | node h1 h2 => exact key _ (.node h1 h2) (fun e => by cases e) t ht hct
  exact theta hZ p ⟨hp, .hole, .hole, Convertible.refl p⟩

/-- No closed S-term `p` is convertible to `S p p`. -/
theorem no_S_p_p {p : Term} (hp : PureS p) : ¬ Convertible p (S ⬝ p ⬝ p) :=
  ncfp_two hp (.node .hole .hole) (fun e => by cases e)

/-! ## Theorem Θ′ -/

/-- Facts (a), (b) of the proof of Theorem Θ′: a member `v` whose head run takes a step to the
head normal form `S a b` with `b` of the form `S c` has `v = v⁻ a`, or its run passes through the
frame `S (S S) p S` and `a = p S`. -/
theorem thetap_td {v a b c : Term} (hv : PureS v) (hs : Steps v (S ⬝ a ⬝ b))
    (hne : v ≠ S ⬝ a ⬝ b) (eb : b = S ⬝ c) :
    (∃ vm, v = vm ⬝ a) ∨ ∃ p, Steps v (S ⬝ (S ⬝ S) ⬝ p ⬝ S) ∧ a = p ⬝ S := by
  obtain ⟨y, e, _, hcase⟩ := lemma_TD hv (plus_of_steps_ne hs hne)
  have ey : y = S := by
    rw [eb] at e
    injection e with e1 _
    exact e1.symm
  rcases hcase with ⟨vm, e', _⟩ | ⟨x, p, q, hfr, _, ea, hφ⟩
  · exact .inl ⟨vm, e'⟩
  · rw [ey] at hφ
    have hpfr := steps_pure hv hfr
    have hpxq : PureS (x ⬝ q) := .app hpfr.app_inv.1.app_inv.1.app_inv.2 hpfr.app_inv.2
    rcases Decidable.em (x ⬝ q = S ⬝ S ⬝ S) with e' | ne'
    · injection e' with e1 e2
      rw [e1, e2] at hfr
      rw [e2] at ea
      exact .inr ⟨p, hfr, ea⟩
    · obtain ⟨y'', _, e'⟩ := lemma_L' hpxq hφ ne'
      cases e'

/-- **Theorem Θ′.**  Let `A` and `B` be sets of closed S-terms such that every member of `A` has,
on its head run, a two-item head normal form `S a b` with `a ∈ A` and `b ∈ B`, and every member
of `B` is `S c` with `c ∈ A`.  Then `A` is empty.  Uses Theorem 2 (`right_combs`, teeth `S S`). -/
theorem theta' {A B : Term → Prop}
    (hA : ∀ t, A t → PureS t ∧ ∃ a b, Steps t (S ⬝ a ⬝ b) ∧ A a ∧ B b)
    (hB : ∀ t, B t → ∃ c, t = S ⬝ c ∧ A c) : ∀ t, ¬ A t := by
  have notS : ¬ A S := by
    intro h
    obtain ⟨_, a, b, hs, _, _⟩ := hA S h
    cases steps_S hs
  have hC : Closed 2 (fun p => A (p ⬝ S)) := by
    intro p' hP
    obtain ⟨hp, a, b, hs, ha, hb⟩ := hA _ hP
    obtain ⟨c, eb, _⟩ := hB b hb
    refine ⟨hp.app_inv.1, ?_⟩
    rcases Decidable.em (p' ⬝ S = S ⬝ a ⬝ b) with e | ne
    · injection e with _ e2
      rw [← e2] at eb
      cases eb
    · rcases thetap_td hp hs ne eb with ⟨vm, e⟩ | ⟨p, hfr, ea⟩
      · injection e with _ e2
        rw [← e2] at ha
        exact absurd ha notS
      · have ha' : A (p ⬝ S) := by rw [← ea]; exact ha
        refine ⟨p, ha', .inr ⟨S ⬝ S, Nat.le_refl _, ?_⟩⟩
        rcases split hfr rfl hp with ⟨e', he, hs'⟩ | ⟨f, g, h1, h2⟩
        · injection he with e1 _
          rw [← e1] at hs'
          exact hs'
        · exfalso
          have hfg := steps_pure hp.app_inv.1 h1
          have hpF : PureS (f ⬝ S ⬝ (g ⬝ S)) :=
            .app (.app hfg.app_inv.1.app_inv.2 .S) (.app hfg.app_inv.2 .S)
          obtain ⟨u', G', e, hw⟩ := last_wrap h2 rfl hpF
          injection e with _ e2
          rw [← e2] at hw
          have h3 := hw.sz_le
          have h4 := sz_arg_lt g S
          omega
  have hnone := right_combs hC
  have key : ∀ (n : Nat) (t : Term), sz t ≤ n → A t → False := by
    intro n
    induction n with
    | zero =>
      intro t h _
      have := sz_pos t
      omega
    | succ n ih =>
      intro t hsz hAt
      obtain ⟨ht, a, b, hs, ha, hb⟩ := hA t hAt
      obtain ⟨c, eb, _⟩ := hB b hb
      rcases Decidable.em (t = S ⬝ a ⬝ b) with e | ne
      · have hlt : sz a < sz t := by
          rw [e]
          exact Nat.lt_trans (sz_arg_lt S a) (sz_fun_lt _ b)
        exact ih a (by omega) ha
      · rcases thetap_td ht hs ne eb with ⟨vm, e⟩ | ⟨p, _, ea⟩
        · have hlt : sz a < sz t := by
            rw [e]
            exact sz_arg_lt vm a
          exact ih a (by omega) ha
        · rw [ea] at ha
          exact hnone p ha
  intro t h
  exact key (sz t) t (Nat.le_refl _) h

/-- No closed S-term `p` is convertible to `S p (S p)`. -/
theorem no_S_p_Sp {p : Term} (hp : PureS p) : ¬ Convertible p (S ⬝ p ⬝ (S ⬝ p)) := by
  intro hc
  have hA : ∀ t, (PureS t ∧ Convertible t p) → PureS t ∧ ∃ a b, Steps t (S ⬝ a ⬝ b) ∧
      (PureS a ∧ Convertible a p) ∧ ∃ c, b = S ⬝ c ∧ PureS c ∧ Convertible c p := by
    rintro t ⟨ht, hct⟩
    obtain ⟨a, b, hs, ca, cb⟩ := hnf2_conv ht hp (.app .S hp) (hct.trans hc)
    have hpab := steps_pure ht hs
    obtain ⟨c, e, cc⟩ := hnf1_conv hpab.app_inv.2 hp cb
    have hpc : PureS c := by
      have := hpab.app_inv.2
      rw [e] at this
      exact this.app_inv.2
    exact ⟨ht, a, b, hs, ⟨hpab.app_inv.1.app_inv.2, ca⟩, c, e, hpc, cc⟩
  exact theta' (A := fun t => PureS t ∧ Convertible t p)
    (B := fun b => ∃ c, b = S ⬝ c ∧ PureS c ∧ Convertible c p) hA
    (fun _ ⟨c, e, hpc, cc⟩ => ⟨c, e, hpc, cc⟩) p ⟨hp, Convertible.refl p⟩

/-- No closed S-term `p` is convertible to `S S S p` (which reduces to `S p (S p)`). -/
theorem no_SSS_p {p : Term} (hp : PureS p) : ¬ Convertible p (S ⬝ S ⬝ S ⬝ p) :=
  fun hc => no_S_p_Sp hp (hc.trans (.fwd (.S S S p) (.refl _)))

/-! ## Theorem Θ″ -/

/-- **Theorem Θ″.**  Let `A` and `B` be sets of closed S-terms such that every member of `A` has,
on its head run, a two-item head normal form `S a b` with `a ∈ B` and `b ∈ A`, and every member
of `B` is `S c` with `c ∈ A`.  Then `A` is empty. -/
theorem theta'' {A B : Term → Prop}
    (hA : ∀ t, A t → PureS t ∧ ∃ a b, Steps t (S ⬝ a ⬝ b) ∧ B a ∧ A b)
    (hB : ∀ t, B t → ∃ c, t = S ⬝ c ∧ A c) : ∀ t, ¬ A t := by
  have hZ : Leafless (fun t => A t ∨ B t) := by
    intro t ht
    rcases ht with h | h
    · obtain ⟨hp, a, b, hs, ha, hb⟩ := hA t h
      exact ⟨hp, .inr ⟨a, b, hs, .inr ha, .inl hb⟩⟩
    · obtain ⟨c, e, hc⟩ := hB t h
      rw [e]
      exact ⟨.app .S (hA c hc).1, .inl ⟨c, .refl _, .inl hc⟩⟩
  have key : ∀ (n : Nat) (t : Term), sz t ≤ n → A t → False := by
    intro n
    induction n with
    | zero =>
      intro t h _
      have := sz_pos t
      omega
    | succ n ih =>
      intro t hsz hAt
      obtain ⟨ht, a, b, hs, ha, hb⟩ := hA t hAt
      obtain ⟨c, ea, hc⟩ := hB a ha
      have h1 : sz c < sz a := by rw [ea]; exact sz_arg_lt S c
      rcases Decidable.em (t = S ⬝ a ⬝ b) with e | ne
      · have hlt : sz a < sz t := by
          rw [e]
          exact Nat.lt_trans (sz_arg_lt S a) (sz_fun_lt _ b)
        exact ih c (by omega) hc
      · obtain ⟨y, eb, _, hcase⟩ := lemma_TD ht (plus_of_steps_ne hs ne)
        rcases hcase with ⟨tm, e, _⟩ | ⟨x, p, q, hfr, _, epq, _⟩
        · have hlt : sz a < sz t := by
            rw [e]
            exact sz_arg_lt tm a
          exact ih c (by omega) hc
        · rw [ea] at epq
          injection epq with _ e2
          rw [← e2] at hfr
          have hk : K2 (fun t => A t ∨ B t) c := by
            obtain ⟨_, a', b', hs', _, _⟩ := hA c hc
            exact ⟨.inl hc, a', b', hs'⟩
          have hFH : Steps (S ⬝ x ⬝ p ⬝ c) (S ⬝ a ⬝ b) := by
            rcases InfNF.steps_cmp hfr hs with h | h
            · exact h
            · rw [InfNF.steps_from_hnf (.inr (.inr ⟨a, b, rfl⟩)) h]
              exact .refl _
          have hg : GoodHnf (S ⬝ a ⬝ b) :=
            .inr (.inr ⟨a, b, rfl, hZ.fold_ne (.inr ha), hZ.fold_ne (.inl hb)⟩)
          have h2 := sz_arg_lt y a
          rw [← eb] at h2
          rcases lemma_ZI_i hZ hk (steps_pure ht hfr) (L := []) rfl hFH hg with e | ⟨b', e⟩ |
            ⟨a', e⟩
          · injection e with e1 _
            cases e1
          · injection e with e1 _
            injection e1 with _ e3
            rw [e3] at h1
            exact Nat.lt_irrefl _ h1
          · injection e with _ e3
            rw [e3] at h2
            omega
  intro t h
  exact key (sz t) t (Nat.le_refl _) h

/-- No closed S-term `p` is convertible to `S (S p) p`. -/
theorem no_S_Sp_p {p : Term} (hp : PureS p) : ¬ Convertible p (S ⬝ (S ⬝ p) ⬝ p) := by
  intro hc
  have hA : ∀ t, (PureS t ∧ Convertible t p) → PureS t ∧ ∃ a b, Steps t (S ⬝ a ⬝ b) ∧
      (∃ c, a = S ⬝ c ∧ PureS c ∧ Convertible c p) ∧ (PureS b ∧ Convertible b p) := by
    rintro t ⟨ht, hct⟩
    obtain ⟨a, b, hs, ca, cb⟩ := hnf2_conv ht (.app .S hp) hp (hct.trans hc)
    have hpab := steps_pure ht hs
    obtain ⟨c, e, cc⟩ := hnf1_conv hpab.app_inv.1.app_inv.2 hp ca
    have hpc : PureS c := by
      have := hpab.app_inv.1.app_inv.2
      rw [e] at this
      exact this.app_inv.2
    exact ⟨ht, a, b, hs, ⟨c, e, hpc, cc⟩, hpab.app_inv.2, cb⟩
  exact theta'' (A := fun t => PureS t ∧ Convertible t p)
    (B := fun a => ∃ c, a = S ⬝ c ∧ PureS c ∧ Convertible c p) hA
    (fun _ ⟨c, e, hpc, cc⟩ => ⟨c, e, hpc, cc⟩) p ⟨hp, Convertible.refl p⟩

end Ncfp
