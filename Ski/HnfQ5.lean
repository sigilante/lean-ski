import Ski.HnfB0
open Term

/-!
# Question 5 of *Dance of the Starlings*, given the minimal pairs

* `pk_wsteps` (CI): `Pk k` is invariant under weak reduction of pure S-terms (Church–Rosser).
* `prod_sub` (B): every subterm of a productive term is productive.
* `q5_of_A`: **given** hypothesis (A), that every application `u v` of two non-rejected terms
  with a rejected class and a head normal form is not productive, a closed pure-S term is productive iff its class is
  not the rejecting class 37.  (A) is stated here as `MinimalPairs` (the 2,757 minimal pairs whose
  fold is not ⊥) and taken as a hypothesis; `HnfCert.minimalPairs` (`Ski/HnfCertFinal.lean`) proves
  it by a kernel-checked certificate, and `HnfCert.q5` is Question 5 outright.
-/

namespace HnfQ5
open HnfS HnfSound HnfProd HnfB0

/-! ## Reducts of head normal forms keep their shape -/

theorem wstep_S {w : Term} (h : WStep S w) : False := by cases h

theorem wstep_Sa {a w : Term} (h : WStep (S ⬝ a) w) : ∃ a', w = S ⬝ a' ∧ WStep a a' := by
  cases h with
  | left _ h => exact (wstep_S h).elim
  | right _ h => exact ⟨_, rfl, h⟩

theorem wstep_Sab {a b w : Term} (h : WStep (S ⬝ a ⬝ b) w) :
    (∃ a', w = S ⬝ a' ⬝ b ∧ WStep a a') ∨ (∃ b', w = S ⬝ a ⬝ b' ∧ WStep b b') := by
  cases h with
  | left _ h =>
    obtain ⟨a', rfl, h'⟩ := wstep_Sa h
    exact .inl ⟨a', rfl, h'⟩
  | right _ h => exact .inr ⟨_, rfl, h⟩

theorem wsteps_S {t w : Term} (h : WSteps t w) (ht : t = S) : w = S := by
  induction h with
  | refl => exact ht
  | step h1 _ ih => subst ht; exact (wstep_S h1).elim

theorem wsteps_Sa {t w : Term} (h : WSteps t w) :
    ∀ {a}, t = S ⬝ a → ∃ a', w = S ⬝ a' ∧ WSteps a a' := by
  induction h with
  | refl => intro a ht; exact ⟨a, ht, .refl a⟩
  | step h1 _ ih =>
    intro a ht; subst ht
    obtain ⟨a₁, rfl, h₁⟩ := wstep_Sa h1
    obtain ⟨a', hw, h'⟩ := ih rfl
    exact ⟨a', hw, .step h₁ h'⟩

theorem wsteps_Sab {t w : Term} (h : WSteps t w) :
    ∀ {a b}, t = S ⬝ a ⬝ b → ∃ a' b', w = S ⬝ a' ⬝ b' ∧ WSteps a a' ∧ WSteps b b' := by
  induction h with
  | refl => intro a b ht; exact ⟨a, b, ht, .refl a, .refl b⟩
  | step h1 _ ih =>
    intro a b ht; subst ht
    rcases wstep_Sab h1 with ⟨a₁, rfl, h₁⟩ | ⟨b₁, rfl, h₁⟩
    · obtain ⟨a', b', hw, ha, hb⟩ := ih rfl
      exact ⟨a', b', hw, .step h₁ ha, hb⟩
    · obtain ⟨a', b', hw, ha, hb⟩ := ih rfl
      exact ⟨a', b', hw, ha, .step h₁ hb⟩

/-- Two head normal forms with a common reduct have pairwise joinable items. -/
theorem items_join {u u' w : Term} (hu : IsHnf u) (hu' : IsHnf u') (h : WSteps u w)
    (h' : WSteps u' w) :
    ∀ a' ∈ spine u', ∃ a ∈ spine u, ∃ c, WSteps a c ∧ WSteps a' c := by
  rcases hu with rfl | ⟨x, rfl⟩ | ⟨x, y, rfl⟩ <;>
  rcases hu' with rfl | ⟨x', rfl⟩ | ⟨x', y', rfl⟩
  · intro a ha; simp [spine] at ha
  · have := wsteps_S h rfl; subst this
    obtain ⟨_, hw, _⟩ := wsteps_Sa h' rfl; cases hw
  · have := wsteps_S h rfl; subst this
    obtain ⟨_, _, hw, _⟩ := wsteps_Sab h' rfl; cases hw
  · intro a ha; simp [spine] at ha
  · obtain ⟨c, rfl, hc⟩ := wsteps_Sa h rfl
    obtain ⟨c', hw, hc'⟩ := wsteps_Sa h' rfl
    cases hw
    intro a ha
    simp only [spine, List.nil_append] at ha
    simp only [List.mem_singleton] at ha; subst ha
    exact ⟨x, by simp [spine], c, hc, hc'⟩
  · obtain ⟨c, rfl, _⟩ := wsteps_Sa h rfl
    obtain ⟨_, _, hw, _⟩ := wsteps_Sab h' rfl; cases hw
  · intro a ha; simp [spine] at ha
  · obtain ⟨_, _, rfl, _⟩ := wsteps_Sab h rfl
    obtain ⟨_, hw, _⟩ := wsteps_Sa h' rfl; cases hw
  · obtain ⟨c, d, rfl, hc, hd⟩ := wsteps_Sab h rfl
    obtain ⟨c', d', hw, hc', hd'⟩ := wsteps_Sab h' rfl
    cases hw
    intro a ha
    simp only [spine, List.nil_append, List.singleton_append, List.mem_cons,
      List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · exact ⟨x, by simp [spine], c, hc, hc'⟩
    · exact ⟨y, by simp [spine], d, hd, hd'⟩

/-! ## Conversion invariance -/

theorem pk_succ_iff {k : Nat} {t u : Term} (hc : HeadChain t u) (hl : (spine u).length ≤ 2) :
    Pk (k + 1) t ↔ ∀ a ∈ spine u, Pk k a := by
  constructor
  · intro ⟨u₀, hc₀, hl₀, hall⟩
    rw [headChain_uniq hc₀ hc hl₀ hl] at hall
    exact hall
  · intro h; exact ⟨u, hc, hl, h⟩

/-- A term with a frame-short head chain has fold `≠ 36`. -/
theorem fold_ne_of_chain {t u : Term} (ht : PureS t) (hc : HeadChain t u)
    (hl : (spine u).length ≤ 2) : fold t ≠ 36 := by
  have hw := headChain_wsteps hc ht
  have ⟨hu, hf⟩ := HnfS.fold_wsteps hw ht
  rw [← hf]; exact fold_hnf hu (isHnf_of_short hu hl)

/-- One direction of the induction step: transport `Pk (k+1)` from `t` to any `t'` sharing
a reduct with `t`'s head normal form, given the induction hypothesis at `k`. -/
theorem transport {k : Nat}
    (ih : ∀ {t t' : Term}, PureS t → WSteps t t' → (Pk k t ↔ Pk k t'))
    {t t' : Term} (ht : PureS t) (ht' : PureS t')
    (hj : ∀ {u u'}, HeadChain t u → HeadChain t' u' → ∃ w, WSteps u w ∧ WSteps u' w)
    (hb' : fold t' ≠ 36) (hP : Pk (k + 1) t) : Pk (k + 1) t' := by
  obtain ⟨u, hc, hl, hall⟩ := hP
  obtain ⟨u', hc', hl', _⟩ := sound_head t' ht' hb'
  have hu := (HnfS.fold_wsteps (headChain_wsteps hc ht) ht).1
  have hu' := (HnfS.fold_wsteps (headChain_wsteps hc' ht') ht').1
  obtain ⟨w, huw, hu'w⟩ := hj hc hc'
  refine (pk_succ_iff hc' hl').mpr fun a' ha' => ?_
  obtain ⟨a, ha, c, hac, ha'c⟩ :=
    items_join (isHnf_of_short hu hl) (isHnf_of_short hu' hl') huw hu'w a' ha'
  have pa := spine_pure hu a ha
  have pa' := spine_pure hu' a' ha'
  exact (ih pa' ha'c).mpr ((ih pa hac).mp (hall a ha))

/-- **CI.**  `Pk k` is invariant under weak reduction of pure S-terms. -/
theorem pk_wsteps : ∀ (k : Nat) {t t' : Term}, PureS t → WSteps t t' → (Pk k t ↔ Pk k t') := by
  intro k
  induction k with
  | zero => intro t t' _ _; exact ⟨fun _ => trivial, fun _ => trivial⟩
  | succ k ih =>
    intro t t' ht hw
    have ⟨ht', hf⟩ := HnfS.fold_wsteps hw ht
    constructor
    · intro hP
      obtain ⟨u, hc, hl, _⟩ := hP
      have hb : fold t ≠ 36 := fold_ne_of_chain ht hc hl
      refine transport ih ht ht' (fun hc hc' => ?_) (by rw [hf]; exact hb) ⟨u, hc, hl, ‹_›⟩
      exact church_rosser (headChain_wsteps hc ht) ((hw.trans (headChain_wsteps hc' ht')))
    · intro hP
      obtain ⟨u', hc', hl', _⟩ := hP
      have hb' : fold t' ≠ 36 := fold_ne_of_chain ht' hc' hl'
      refine transport ih ht' ht (fun hc' hc => ?_) (by rw [← hf]; exact hb') ⟨u', hc', hl', ‹_›⟩
      obtain ⟨w, h1, h2⟩ :=
        church_rosser (headChain_wsteps hc ht) (hw.trans (headChain_wsteps hc' ht'))
      exact ⟨w, h2, h1⟩

/-! ## Subterms of productive terms are productive -/

theorem _root_.HnfB0.Sub.trans {a b c : Term} (h₁ : Sub a b) (h₂ : Sub b c) : Sub a c := by
  induction h₂ with
  | refl => exact h₁
  | left x _ ih => exact .left x ih
  | right f _ ih => exact .right f ih

theorem _root_.HnfB0.Sub.pure {s t : Term} (h : Sub s t) (ht : PureS t) : PureS s := by
  induction h with
  | refl => exact ht
  | left _ _ ih => exact ih ht.app_inv.1
  | right _ _ ih => exact ih ht.app_inv.2

theorem sub_of_spine {a u : Term} (h : a ∈ spine u) : Sub a u := by
  induction u with
  | app f x ihf _ =>
    simp only [spine, List.mem_append, List.mem_singleton] at h
    rcases h with h | rfl
    · exact .left x (ihf h)
    · exact .right f (.refl _)
  | _ => simp [spine] at h

/-- Reducing a subterm reduces the term. -/
theorem sub_wsteps {m m' t : Term} (h : Sub m t) (hw : WSteps m m') :
    ∃ t', WSteps t t' ∧ Sub m' t' := by
  induction h with
  | refl => exact ⟨m', hw, .refl _⟩
  | left x _ ih =>
    obtain ⟨f', hf, hs⟩ := ih
    exact ⟨f' ⬝ x, hf.left x, .left x hs⟩
  | right f _ ih =>
    obtain ⟨x', hx, hs⟩ := ih
    exact ⟨f ⬝ x', hx.right f, .right f hs⟩

/-- **B.**  Every subterm of a productive closed pure-S term is productive. -/
theorem prod_sub : ∀ (k : Nat) {m t : Term}, PureS t → Sub m t → (∀ K, Pk K t) → Pk k m := by
  intro k
  induction k with
  | zero => intro _ _ _ _ _; trivial
  | succ k ih =>
    intro m t ht hs hP
    have hm := hs.pure ht
    if hb : fold m = 36 then
      obtain ⟨n, hn⟩ := botAt_of_sub hs ht hb
      exact (not_Pk n ht hn (hP (n + 1))).elim
    else
      obtain ⟨u, hc, hl, _⟩ := sound_head m hm hb
      refine ⟨u, hc, hl, fun a ha => ?_⟩
      obtain ⟨t', htt', hsu⟩ := sub_wsteps hs (headChain_wsteps hc hm)
      have ht' := (HnfS.fold_wsteps htt' ht).1
      exact ih ht' ((sub_of_spine ha).trans hsu) fun K => (pk_wsteps K ht htt').mp (hP K)

/-! ## Question 5, given the minimal pairs -/

/-- Hypothesis (A): the minimal rejected applications that have a head normal form are not
productive.  (Those without one, fold `36`, are not productive by `HnfB0.B0`; the premise
`fold (u ⬝ v) ≠ 36` keeps them out of the hypothesis: 2,757 of the 4,899 (class, block) pairs.) -/
def MinimalPairs : Prop :=
  ∀ u v, PureS u → PureS v → cls u ≠ 37 → cls v ≠ 37 → cls (u ⬝ v) = 37 →
    fold (u ⬝ v) ≠ 36 → ¬ ∀ k, Pk k (u ⬝ v)

/-- The hard half, given (A): a rejected term is not productive. -/
theorem hard_of_A (hA : MinimalPairs) : ∀ {t : Term}, PureS t → cls t = 37 → ¬ ∀ k, Pk k t := by
  intro t ht
  induction ht with
  | S => intro h; exact absurd h (by decide)
  | @app f x hf hx ihf ihx =>
    intro h hP
    if h1 : cls f = 37 then
      exact ihf h1 fun k => prod_sub k (.app hf hx) (.left x (.refl f)) hP
    else if h2 : cls x = 37 then
      exact ihx h2 fun k => prod_sub k (.app hf hx) (.right f (.refl x)) hP
    else if hb : fold (f ⬝ x) = 36 then
      obtain ⟨k, hk⟩ := B0 (.app hf hx) (.refl _) hb
      exact hk (hP k)
    else
      exact hA f x hf hx h1 h2 h hb hP

/-- **Question 5 of *Dance of the Starlings*, given (A).**  A closed pure-S term is productive
(its Böhm tree is defined to every depth) iff its class is not the rejecting class 37. -/
theorem q5_of_A (hA : MinimalPairs) {t : Term} (ht : PureS t) :
    (∀ k, Pk k t) ↔ cls t ≠ 37 :=
  ⟨fun hP h => hard_of_A hA ht h hP, fun h => easy ht h⟩

end HnfQ5
