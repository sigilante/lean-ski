import Ski.D2Sem
open Term

/-!
# Conversion invariance of the observable, and uniqueness of prefixes at every depth

Two supporting results of the S6 paper (*Prefix Regularity*), Section 2.  The name
`lemma3` keeps an earlier draft's numbering.

**The observable** (`HasObs`, the paper's Def. 3).  For a valuation `v : Term → M`, the observable
of a closed S-term `t` is `(m, v u₁, …, v uₘ)` if the head run of `t` reaches the head normal form
`S u₁ ⋯ uₘ` (`m ≤ 2`), and `(⊥, v f, v w)` if it reaches a stable frame `f w` (`f` without a head
normal form, i.e. `fold f = 36`: `stable_iff`).  The paper takes the *first* stable frame; `HasObs`
allows any stable stage, as `D2.Pre` does, and `obs_bot_first` shows that the two agree.

**Lemma 4** (`lemma3`, `obs_conv`).  If `t` and `t'` are convertible, they have the same
observable.  It is proved for every valuation that is invariant under weak reduction of closed
S-terms (`Inv`), which covers the fold into any S-model (`SModel.inv`, `lemma3_model`) and the
fold into the 373-element table `D` relative to its kernel checks (`lemma3_D`).  The paper's
further hypothesis, a homomorphism from `M` to the 38 blocks, is not used: frames and stability
are read off the term, not off its value.  `Convertible` is the equivalence closure of `WStep` on
all SKI terms; the lemma needs only its two ends to be closed S-terms.

**Prefixes** (`pre_unique`, `pre_total`, `pre_bot_first`).  `D2.Pre d t P` is a total functional relation in `t`
at every depth `d`, for closed S-terms `t`.  Existence is `D2.pre_exists`.

The proofs follow the paper: Church–Rosser and standardization (`Ski/Weak.lean`) for Lemma 4;
determinism of the head run and `InfNF.steps_bot_fun` for uniqueness.  That the head run reaches a
head normal form or a stable frame (`reach_frame`) is `TopTerm.reach_all`.

The relation `HasObs` is this module's own; the full observable of Theorem 9 is defined
elsewhere and is not connected here.
-/

namespace Conv
open HnfS HnfSound InfNF TopTerm D2

/-! ## Convertibility -/

/-- Convertibility: the reflexive, symmetric, transitive closure of weak reduction (a contraction
at any position), as a zigzag of steps. -/
inductive Convertible : Term → Term → Prop
  | refl (t : Term) : Convertible t t
  | fwd {t u v : Term} : WStep t u → Convertible u v → Convertible t v
  | bwd {t u v : Term} : WStep u t → Convertible u v → Convertible t v

theorem Convertible.trans {t u v : Term} (h₁ : Convertible t u) (h₂ : Convertible u v) :
    Convertible t v := by
  induction h₁ with
  | refl _ => exact h₂
  | fwd s _ ih => exact .fwd s (ih h₂)
  | bwd s _ ih => exact .bwd s (ih h₂)

theorem Convertible.symm {t u : Term} (h : Convertible t u) : Convertible u t := by
  induction h with
  | refl t => exact .refl t
  | fwd s _ ih => exact ih.trans (.bwd s (.refl _))
  | bwd s _ ih => exact ih.trans (.fwd s (.refl _))

theorem Convertible.of_wsteps {t u : Term} (h : WSteps t u) : Convertible t u := by
  induction h with
  | refl t => exact .refl t
  | step s _ ih => exact .fwd s ih

/-- `Convertible` is the least equivalence relation containing `WStep`. -/
theorem Convertible.least {R : Term → Term → Prop} (hr : ∀ t, R t t)
    (hs : ∀ {t u}, R t u → R u t) (ht : ∀ {t u v}, R t u → R u v → R t v)
    (hw : ∀ {t u}, WStep t u → R t u) {t u : Term} (h : Convertible t u) : R t u := by
  induction h with
  | refl t => exact hr t
  | fwd s _ ih => exact ht (hw s) ih
  | bwd s _ ih => exact ht (hs (hw s)) ih

/-- Church–Rosser: convertible terms have a common reduct, and conversely. -/
theorem conv_iff_join {t t' : Term} :
    Convertible t t' ↔ ∃ w, WSteps t w ∧ WSteps t' w := by
  constructor
  · intro h
    induction h with
    | refl t => exact ⟨t, .refl t, .refl t⟩
    | fwd s _ ih =>
      obtain ⟨w, h1, h2⟩ := ih
      exact ⟨w, .step s h1, h2⟩
    | bwd s _ ih =>
      obtain ⟨w, h1, h2⟩ := ih
      obtain ⟨w', h3, h4⟩ := church_rosser (WSteps.single s) h1
      exact ⟨w', h3, h2.trans h4⟩
  · rintro ⟨w, h1, h2⟩
    exact (Convertible.of_wsteps h1).trans (Convertible.of_wsteps h2).symm

/-! ## Frames -/

/-- A closed S-term has no head normal form iff its block is `⊥ = 36` (S1). -/
theorem stable_iff {f : Term} (hf : PureS f) : fold f = 36 ↔ ¬ HasHnf f := by
  constructor
  · exact no_hnf_of_bot hf
  · intro h
    cases Nat.decEq (fold f) 36 with
    | isTrue e => exact e
    | isFalse ne => exact absurd (HnfSound.sound f hf ne) h

/-- The head run of every closed S-term reaches a head normal form or a stable frame. -/
theorem reach_frame {t : Term} (ht : PureS t) :
    ∃ T, Steps t T ∧ (IsHnf T ∨ ∃ f w, T = f ⬝ w ∧ fold f = 36) := by
  have hr := reach_all ht
  induction hr with
  | hnf hu => exact ⟨_, .refl _, .inl hu⟩
  | @bot f w _ hb => exact ⟨_, .refl _, .inr ⟨f, w, rfl, hb⟩⟩
  | step s _ ih =>
    obtain ⟨T, hs, hT⟩ := ih (HnfS.wstep_pure s.weak ht).1
    exact ⟨T, .step s hs, hT⟩

/-- A stable frame is not a head normal form. -/
theorem hnf_not_bot {f w : Term} (hf : PureS f) (hb : fold f = 36) : ¬ IsHnf (f ⬝ w) := by
  intro h
  rcases h with e | ⟨x, e⟩ | ⟨x, y, e⟩
  · cases e
  · injection e with e1 _
    subst e1
    exact fold_hnf hf (.inl rfl) hb
  · injection e with e1 _
    subst e1
    exact fold_hnf hf (.inr (.inl ⟨x, rfl⟩)) hb

/-- Two head normal forms on one head run are equal. -/
theorem run_hnf_hnf {t X Y : Term} (hX : IsHnf X) (hY : IsHnf Y) (h : Steps t X)
    (h' : Steps t Y) : X = Y := by
  rcases steps_cmp h h' with hs | hs
  · exact (steps_from_hnf hX hs).symm
  · exact steps_from_hnf hY hs

/-- A head run does not hold both a head normal form and a stable frame. -/
theorem run_hnf_bot {t X f w : Term} (ht : PureS t) (hX : IsHnf X) (h : Steps t X)
    (h' : Steps t (f ⬝ w)) (hb : fold f = 36) : False := by
  have hf := (steps_pure ht h').app_inv.1
  rcases steps_cmp h h' with hs | hs
  · have e := steps_from_hnf hX hs
    subst e
    exact hnf_not_bot hf hb hX
  · obtain ⟨g, e, _, hg, hgb⟩ := steps_bot_fun hf hb hs
    subst e
    exact hnf_not_bot hg hgb hX

/-- Two stable stages of one head run have the same argument, and their function parts lie on
one head run. -/
theorem run_bot_bot {t f w f' w' : Term} (ht : PureS t) (h : Steps t (f ⬝ w))
    (hb : fold f = 36) (h' : Steps t (f' ⬝ w')) (hb' : fold f' = 36) :
    w = w' ∧ (Steps f f' ∨ Steps f' f) := by
  have hf := (steps_pure ht h).app_inv.1
  have hf' := (steps_pure ht h').app_inv.1
  rcases steps_cmp h h' with hs | hs
  · obtain ⟨g, e, hg, _, _⟩ := steps_bot_fun hf hb hs
    injection e with e1 e2
    subst e1 e2
    exact ⟨rfl, .inl hg⟩
  · obtain ⟨g, e, hg, _, _⟩ := steps_bot_fun hf' hb' hs
    injection e with e1 e2
    subst e1 e2
    exact ⟨rfl, .inr hg⟩

/-- `f w` is the first stable frame on the head run of `t`: the run reaches it, and every stable
stage of the run is at or after it. -/
def FirstStable (t f w : Term) : Prop :=
  Steps t (f ⬝ w) ∧ fold f = 36 ∧
    ∀ g x, Steps t (g ⬝ x) → fold g = 36 → Steps (f ⬝ w) (g ⬝ x)

/-- A run with a stable stage `f w` has a first stable frame `f₀ w`, and `f₀` head-reduces to
`f`. -/
theorem first_stable {t f w : Term} (ht : PureS t) (h : Steps t (f ⬝ w)) (hb : fold f = 36) :
    ∃ f₀, FirstStable t f₀ w ∧ Steps f₀ f := by
  generalize hu : f ⬝ w = u at h
  induction h with
  | refl t =>
    subst hu
    exact ⟨f, ⟨.refl _, hb, fun _ _ hs _ => hs⟩, .refl _⟩
  | @step t t₁ u s hs ih =>
    have key : (∃ g x, t = g ⬝ x ∧ fold g = 36) ∨ ¬ (∃ g x, t = g ⬝ x ∧ fold g = 36) := by
      cases t with
      | app g x =>
        cases Nat.decEq (fold g) 36 with
        | isTrue e => exact .inl ⟨g, x, rfl, e⟩
        | isFalse ne =>
          refine .inr ?_
          rintro ⟨g', x', e, hg⟩
          injection e with e1 _
          subst e1
          exact ne hg
      | S => exact .inr (fun ⟨_, _, e, _⟩ => by cases e)
      | K => exact .inr (fun ⟨_, _, e, _⟩ => by cases e)
      | I => exact .inr (fun ⟨_, _, e, _⟩ => by cases e)
    rcases key with ⟨g, x, rfl, hg⟩ | hn
    · subst hu
      obtain ⟨g', e, hgg, _, _⟩ := steps_bot_fun ht.app_inv.1 hg (.step s hs)
      injection e with e1 e2
      subst e1 e2
      exact ⟨g, ⟨.refl _, hg, fun _ _ hs' _ => hs'⟩, hgg⟩
    · obtain ⟨f₀, ⟨h1, h2, h3⟩, h4⟩ := ih (HnfS.wstep_pure s.weak ht).1 hu
      refine ⟨f₀, ⟨.step s h1, h2, ?_⟩, h4⟩
      intro g x hgx hg
      cases hgx with
      | refl => exact absurd ⟨g, x, rfl, hg⟩ hn
      | step s' rest =>
        have e := Step.det s' s
        subst e
        exact h3 g x rest hg

/-! ## The observable -/

/-- Values of the observable: the arity of the head normal form with the values of its items, or
`⊥` with the values of the two parts of a stable frame. -/
inductive Obs (M : Type) : Type
  | s0 : Obs M
  | s1 (a : M) : Obs M
  | s2 (a b : M) : Obs M
  | bot (f w : M) : Obs M

/-- A valuation that is invariant under weak reduction of closed S-terms. -/
def Inv {M : Type} (v : Term → M) : Prop := ∀ {t u : Term}, PureS t → WStep t u → v u = v t

theorem Inv.wsteps {M : Type} {v : Term → M} (hv : Inv v) {t u : Term} (ht : PureS t)
    (h : WSteps t u) : v u = v t := by
  induction h with
  | refl => rfl
  | step s _ ih => exact (ih (HnfS.wstep_pure s ht).1).trans (hv ht s)

/-- `HasObs v t o`: the observable of `t` over the valuation `v` is `o`. -/
inductive HasObs {M : Type} (v : Term → M) : Term → Obs M → Prop
  | s0 {t : Term} : Steps t S → HasObs v t .s0
  | s1 {t a : Term} : Steps t (S ⬝ a) → HasObs v t (.s1 (v a))
  | s2 {t a b : Term} : Steps t (S ⬝ a ⬝ b) → HasObs v t (.s2 (v a) (v b))
  | bot {t f w : Term} : Steps t (f ⬝ w) → fold f = 36 → HasObs v t (.bot (v f) (v w))

/-- Every closed S-term has an observable. -/
theorem obs_exists {M : Type} (v : Term → M) {t : Term} (ht : PureS t) : ∃ o, HasObs v t o := by
  obtain ⟨T, hs, hT⟩ := reach_frame ht
  rcases hT with (rfl | ⟨a, rfl⟩ | ⟨a, b, rfl⟩) | ⟨f, w, rfl, hb⟩
  · exact ⟨_, .s0 hs⟩
  · exact ⟨_, .s1 hs⟩
  · exact ⟨_, .s2 hs⟩
  · exact ⟨_, .bot hs hb⟩

/-- The observable is unique. -/
theorem obs_unique {M : Type} {v : Term → M} (hv : Inv v) {t : Term} {o o' : Obs M}
    (ht : PureS t) (h : HasObs v t o) (h' : HasObs v t o') : o = o' := by
  cases h with
  | s0 hs =>
    cases h' with
    | s0 _ => rfl
    | @s1 a' hs' => cases run_hnf_hnf (.inl rfl) (.inr (.inl ⟨a', rfl⟩)) hs hs'
    | @s2 a' b' hs' => cases run_hnf_hnf (.inl rfl) (.inr (.inr ⟨a', b', rfl⟩)) hs hs'
    | bot hs' hb' => exact (run_hnf_bot ht (.inl rfl) hs hs' hb').elim
  | @s1 a hs =>
    have hX : IsHnf (S ⬝ a) := .inr (.inl ⟨a, rfl⟩)
    cases h' with
    | s0 hs' => cases run_hnf_hnf hX (.inl rfl) hs hs'
    | @s1 a' hs' =>
      have e := run_hnf_hnf hX (.inr (.inl ⟨a', rfl⟩)) hs hs'
      cases e
      rfl
    | @s2 a' b' hs' => cases run_hnf_hnf hX (.inr (.inr ⟨a', b', rfl⟩)) hs hs'
    | bot hs' hb' => exact (run_hnf_bot ht hX hs hs' hb').elim
  | @s2 a b hs =>
    have hX : IsHnf (S ⬝ a ⬝ b) := .inr (.inr ⟨a, b, rfl⟩)
    cases h' with
    | s0 hs' => cases run_hnf_hnf hX (.inl rfl) hs hs'
    | @s1 a' hs' => cases run_hnf_hnf hX (.inr (.inl ⟨a', rfl⟩)) hs hs'
    | @s2 a' b' hs' =>
      have e := run_hnf_hnf hX (.inr (.inr ⟨a', b', rfl⟩)) hs hs'
      cases e
      rfl
    | bot hs' hb' => exact (run_hnf_bot ht hX hs hs' hb').elim
  | @bot f w hs hb =>
    cases h' with
    | s0 hs' => exact (run_hnf_bot ht (.inl rfl) hs' hs hb).elim
    | @s1 a' hs' => exact (run_hnf_bot ht (.inr (.inl ⟨a', rfl⟩)) hs' hs hb).elim
    | @s2 a' b' hs' => exact (run_hnf_bot ht (.inr (.inr ⟨a', b', rfl⟩)) hs' hs hb).elim
    | @bot f' w' hs' hb' =>
      have hf := (steps_pure ht hs).app_inv.1
      have hf' := (steps_pure ht hs').app_inv.1
      obtain ⟨e, hff⟩ := run_bot_bot ht hs hb hs' hb'
      subst e
      rcases hff with h1 | h1
      · rw [hv.wsteps hf h1.weak]
      · rw [hv.wsteps hf' h1.weak]

/-- The `⊥` case of `HasObs` is the paper's: the values are those of the first stable frame. -/
theorem obs_bot_first {M : Type} {v : Term → M} (hv : Inv v) {t : Term} {m n : M}
    (ht : PureS t) :
    HasObs v t (.bot m n) ↔ ∃ f w, FirstStable t f w ∧ v f = m ∧ v w = n := by
  constructor
  · intro h
    cases h with
    | @bot f w hs hb =>
      obtain ⟨f₀, hF, hff⟩ := first_stable ht hs hb
      exact ⟨f₀, w, hF, (hv.wsteps (steps_pure ht hF.1).app_inv.1 hff.weak).symm, rfl⟩
  · rintro ⟨f, w, ⟨hs, hb, _⟩, rfl, rfl⟩
    exact .bot hs hb

/-! ## Lemma 4 -/

theorem hnf1_wsteps {a u : Term} (hp : PureS (S ⬝ a)) (h : WSteps (S ⬝ a) u) :
    ∃ a', u = S ⬝ a' ∧ WSteps a a' := by
  obtain ⟨f', a', rfl, hf, ha, _⟩ := stable_wsteps hp (.inr (.inr (.inl ⟨a, rfl⟩))) h
  have e := wsteps_from_S hf
  subst e
  exact ⟨a', rfl, ha⟩

theorem hnf2_wsteps {a b u : Term} (hp : PureS (S ⬝ a ⬝ b)) (h : WSteps (S ⬝ a ⬝ b) u) :
    ∃ a' b', u = S ⬝ a' ⬝ b' ∧ WSteps a a' ∧ WSteps b b' := by
  obtain ⟨f', b', rfl, hf, hb, _⟩ := stable_wsteps hp (.inr (.inr (.inr ⟨a, b, rfl⟩))) h
  obtain ⟨a', rfl, ha⟩ := hnf1_wsteps hp.app_inv.1 hf
  exact ⟨a', b', rfl, ha, hb⟩

/-- Internal steps keep the head `S`. -/
theorem parIs_S {t : Term} (h : ParIs t S) : t = S := by
  generalize hu : S = u at h
  induction h with
  | refl => rfl
  | step h₁ _ ih =>
    subst hu
    have e := ih rfl
    subst e
    cases h₁
    rfl

/-- Internal steps keep an application: the function part by internal steps, the argument by
any steps. -/
theorem parIs_app {t f w : Term} (h : ParIs t (f ⬝ w)) :
    ∃ f' w', t = f' ⬝ w' ∧ ParIs f' f ∧ WSteps w' w := by
  generalize hu : f ⬝ w = u at h
  induction h generalizing f w with
  | refl => subst hu; exact ⟨f, w, rfl, .refl _, .refl _⟩
  | step h₁ _ ih =>
    obtain ⟨f₁, w₁, rfl, hf, hw⟩ := ih hu
    cases h₁ with
    | app hf' hw' => exact ⟨_, _, rfl, .step hf' hf, hw'.wsteps.trans hw⟩

/-- The observable of a reduct is an observable of the term (standardization: `t` head-reduces
to a frame that reaches the reduct's frame by internal steps). -/
theorem obs_back {M : Type} {v : Term → M} (hv : Inv v) {t u : Term} {o : Obs M}
    (ht : PureS t) (h : WSteps t u) (ho : HasObs v u o) : HasObs v t o := by
  cases ho with
  | s0 hs =>
    obtain ⟨T, h1, h2⟩ := wsteps_split (h.trans hs.weak)
    have e := parIs_S h2
    subst e
    exact .s0 h1
  | @s1 a hs =>
    obtain ⟨T, h1, h2⟩ := wsteps_split (h.trans hs.weak)
    obtain ⟨f', a', rfl, hf, ha⟩ := parIs_app h2
    have e := parIs_S hf
    subst e
    rw [hv.wsteps (steps_pure ht h1).app_inv.2 ha]
    exact .s1 h1
  | @s2 a b hs =>
    obtain ⟨T, h1, h2⟩ := wsteps_split (h.trans hs.weak)
    obtain ⟨g', b', rfl, hg, hb⟩ := parIs_app h2
    obtain ⟨f', a', rfl, hf, ha⟩ := parIs_app hg
    have e := parIs_S hf
    subst e
    have hp := steps_pure ht h1
    rw [hv.wsteps hp.app_inv.1.app_inv.2 ha, hv.wsteps hp.app_inv.2 hb]
    exact .s2 h1
  | @bot f w hs hb =>
    obtain ⟨T, h1, h2⟩ := wsteps_split (h.trans hs.weak)
    obtain ⟨f', w', rfl, hf, hw⟩ := parIs_app h2
    have hp := steps_pure ht h1
    rw [hv.wsteps hp.app_inv.1 hf.wsteps, hv.wsteps hp.app_inv.2 hw]
    exact .bot h1 ((HnfS.fold_wsteps hf.wsteps hp.app_inv.1).2.symm.trans hb)

/-- A reduct has the observable of the term (Church–Rosser, then `obs_back`). -/
theorem obs_fwd {M : Type} {v : Term → M} (hv : Inv v) {t u : Term} {o : Obs M}
    (ht : PureS t) (h : WSteps t u) (ho : HasObs v t o) : HasObs v u o := by
  have hu := (HnfS.fold_wsteps h ht).1
  cases ho with
  | s0 hs =>
    obtain ⟨T, h1, h2⟩ := church_rosser hs.weak h
    have e := wsteps_from_S h1
    subst e
    exact obs_back hv hu h2 (.s0 (.refl _))
  | @s1 a hs =>
    have hp := steps_pure ht hs
    obtain ⟨T, h1, h2⟩ := church_rosser hs.weak h
    obtain ⟨a', rfl, ha⟩ := hnf1_wsteps hp h1
    rw [← hv.wsteps hp.app_inv.2 ha]
    exact obs_back hv hu h2 (.s1 (.refl _))
  | @s2 a b hs =>
    have hp := steps_pure ht hs
    obtain ⟨T, h1, h2⟩ := church_rosser hs.weak h
    obtain ⟨a', b', rfl, ha, hb⟩ := hnf2_wsteps hp h1
    rw [← hv.wsteps hp.app_inv.1.app_inv.2 ha, ← hv.wsteps hp.app_inv.2 hb]
    exact obs_back hv hu h2 (.s2 (.refl _))
  | @bot f w hs hb =>
    have hp := steps_pure ht hs
    obtain ⟨T, h1, h2⟩ := church_rosser hs.weak h
    obtain ⟨f', w', rfl, hf, hw, _⟩ := stable_wsteps hp (.inl hb) h1
    rw [← hv.wsteps hp.app_inv.1 hf, ← hv.wsteps hp.app_inv.2 hw]
    exact obs_back hv hu h2 (.bot (.refl _) ((HnfS.fold_wsteps hf hp.app_inv.1).2.trans hb))

/-- The observable is invariant under weak reduction, in both directions. -/
theorem obs_wsteps {M : Type} {v : Term → M} (hv : Inv v) {t u : Term} {o : Obs M}
    (ht : PureS t) (h : WSteps t u) : HasObs v t o ↔ HasObs v u o :=
  ⟨obs_fwd hv ht h, obs_back hv ht h⟩

/-- **Lemma 4**, relational form: convertible closed S-terms have the same observables. -/
theorem obs_conv {M : Type} {v : Term → M} (hv : Inv v) {t t' : Term} {o : Obs M}
    (ht : PureS t) (ht' : PureS t') (h : Convertible t t') : HasObs v t o ↔ HasObs v t' o := by
  obtain ⟨w, h1, h2⟩ := conv_iff_join.mp h
  exact (obs_wsteps hv ht h1).trans (obs_wsteps hv ht' h2).symm

/-- **Lemma 4.**  If `t` and `t'` are convertible, then `O(t) = O(t')`. -/
theorem lemma3 {M : Type} {v : Term → M} (hv : Inv v) {t t' : Term} {o o' : Obs M}
    (ht : PureS t) (ht' : PureS t') (h : Convertible t t') (ho : HasObs v t o)
    (ho' : HasObs v t' o') : o = o' :=
  obs_unique hv ht' ((obs_conv hv ht ht' h).mp ho) ho'

/-! ## S-models -/

/-- An S-model: a set with a binary operation and an element `s` with `s a b c = a c (b c)`. -/
structure SModel (M : Type) where
  s : M
  ap : M → M → M
  law : ∀ a b c, ap (ap (ap s a) b) c = ap (ap a c) (ap b c)

/-- The fold of a term into an S-model (`K` and `I` are sent to `s`; only closed S-terms
matter). -/
def SModel.val {M : Type} (m : SModel M) : Term → M
  | .S => m.s
  | .app f x => m.ap (m.val f) (m.val x)
  | _ => m.s

theorem SModel.inv {M : Type} (m : SModel M) : Inv m.val := by
  intro t u ht h
  induction h with
  | S f g x =>
    simp only [SModel.val]
    exact (m.law _ _ _).symm
  | K x y => exact absurd ht.app_inv.1.app_inv.1 PureS.not_K
  | I x => exact absurd ht.app_inv.1 PureS.not_I
  | left x _ ih => simp only [SModel.val, ih ht.app_inv.1]
  | right f _ ih => simp only [SModel.val, ih ht.app_inv.2]

/-- **Lemma 4** for the fold into an S-model. -/
theorem lemma3_model {M : Type} (m : SModel M) {t t' : Term} {o o' : Obs M}
    (ht : PureS t) (ht' : PureS t') (h : Convertible t t') (ho : HasObs m.val t o)
    (ho' : HasObs m.val t' o') : o = o' :=
  lemma3 m.inv ht ht' h ho ho'

/-- **Lemma 4** for the fold into the 373-element table `D`, relative to its checks. -/
theorem lemma3_D (C : Checks) {t t' : Term} {o o' : Obs Nat}
    (ht : PureS t) (ht' : PureS t') (h : Convertible t t') (ho : HasObs foldD t o)
    (ho' : HasObs foldD t' o') : o = o' :=
  lemma3 (fun ht h => wstep_foldD C h ht) ht ht' h ho ho'

/-! ## Prefixes at every depth -/

/-- **Uniqueness of prefixes.**  `Pre d t` has at most one value, at every depth. -/
theorem pre_unique : ∀ (d : Nat) {t : Term} {P P' : PT}, PureS t → Pre d t P → Pre d t P' →
    P = P' := by
  intro d
  induction d using Nat.strongRecOn with
  | _ d ih =>
    intro t P P' ht h h'
    cases h with
    | zero => cases h'; rfl
    | leaf d₁ =>
      cases h' with
      | leaf => rfl
      | one hs' _ => cases steps_from_S hs'
      | two hs' _ _ => cases steps_from_S hs'
      | bot hs' _ _ _ => cases steps_from_S hs'
    | @one d₁ _ a Pa hs ha =>
      have hX : IsHnf (S ⬝ a) := .inr (.inl ⟨a, rfl⟩)
      cases h' with
      | leaf => cases steps_from_S hs
      | @one _ _ a' Pa' hs' ha' =>
        have e := run_hnf_hnf hX (.inr (.inl ⟨a', rfl⟩)) hs hs'
        cases e
        rw [ih d₁ (Nat.lt_succ_self d₁) (steps_pure ht hs).app_inv.2 ha ha']
      | @two _ _ a' b' _ _ hs' _ _ => cases run_hnf_hnf hX (.inr (.inr ⟨a', b', rfl⟩)) hs hs'
      | bot hs' hb' _ _ => exact (run_hnf_bot ht hX hs hs' hb').elim
    | @two d₁ _ a b Pa Pb hs ha hb =>
      have hX : IsHnf (S ⬝ a ⬝ b) := .inr (.inr ⟨a, b, rfl⟩)
      cases h' with
      | leaf => cases steps_from_S hs
      | @one _ _ a' _ hs' _ => cases run_hnf_hnf hX (.inr (.inl ⟨a', rfl⟩)) hs hs'
      | @two _ _ a' b' Pa' Pb' hs' ha' hb' =>
        have e := run_hnf_hnf hX (.inr (.inr ⟨a', b', rfl⟩)) hs hs'
        cases e
        have hp := steps_pure ht hs
        rw [ih (d₁ - 1) (Nat.lt_succ_of_le (Nat.sub_le d₁ 1)) hp.app_inv.1.app_inv.2 ha ha',
          ih d₁ (Nat.lt_succ_self d₁) hp.app_inv.2 hb hb']
      | bot hs' hb' _ _ => exact (run_hnf_bot ht hX hs hs' hb').elim
    | @bot d₁ _ f w Pf Pw hs hb hf hw =>
      cases h' with
      | leaf => cases steps_from_S hs
      | @one _ _ a' _ hs' _ => exact (run_hnf_bot ht (.inr (.inl ⟨a', rfl⟩)) hs' hs hb).elim
      | @two _ _ a' b' _ _ hs' _ _ =>
        exact (run_hnf_bot ht (.inr (.inr ⟨a', b', rfl⟩)) hs' hs hb).elim
      | @bot _ _ f' w' Pf' Pw' hs' hb' hf' hw' =>
        have hp := steps_pure ht hs
        have hp' := steps_pure ht hs'
        obtain ⟨e, hff⟩ := run_bot_bot ht hs hb hs' hb'
        subst e
        have lt := Nat.lt_succ_self d₁
        rcases hff with h1 | h1
        · rw [ih d₁ lt hp.app_inv.1 hf (pre_bwd hp.app_inv.1 h1 hf'),
            ih d₁ lt hp.app_inv.2 hw hw']
        · rw [ih d₁ lt hp'.app_inv.1 (pre_bwd hp'.app_inv.1 h1 hf) hf',
            ih d₁ lt hp.app_inv.2 hw hw']

/-- `π_d` is a total function on closed S-terms. -/
theorem pre_total (d : Nat) {t : Term} (ht : PureS t) :
    ∃ P, Pre d t P ∧ ∀ Q, Pre d t Q → Q = P := by
  obtain ⟨P, hP⟩ := pre_exists d ht
  exact ⟨P, hP, fun Q hQ => pre_unique d ht hQ hP⟩

/-- The `bot` rule of `Pre` may be read at the first stable frame, as in the paper: a stable stage
`f w` with prefixes `Pf`, `Pw` gives the first stable frame `f₀ w` with the same prefixes.  With
`pre_unique`, `π_{d+1}(t) = π_d(f₀) π_d(w)`. -/
theorem pre_bot_first {d : Nat} {t f w : Term} {Pf Pw : PT} (ht : PureS t)
    (hs : Steps t (f ⬝ w)) (hb : fold f = 36) (hf : Pre d f Pf) (hw : Pre d w Pw) :
    ∃ f₀, FirstStable t f₀ w ∧ Pre d f₀ Pf ∧ Pre (d + 1) t (.app Pf Pw) := by
  obtain ⟨f₀, hF, hff⟩ := first_stable ht hs hb
  exact ⟨f₀, hF, pre_bwd (steps_pure ht hF.1).app_inv.1 hff hf, .bot hs hb hf hw⟩

end Conv
