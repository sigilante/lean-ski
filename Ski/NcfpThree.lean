import Ski.NcfpScheme
open Term

/-!
# NCFP: the three-hole shapes of depth 2 with one closed part

Source: `notes/NCFP-proof.md`, §15.4 (the four instances of Theorem T by hand).  Setting as in
`Ski/Ncfp.lean`.

What is proved, for closed `p` and closed normalizing `n`: `p` is convertible to none of
`S (S p p) (S n p)`, `S (S p p) (S p n)`, `S (S n p) (S p p)`, `S (S p n) (S p p)`
(`no_S_Spp_Snp`, `no_S_Spp_Spn`, `no_S_Snp_Spp`, `no_S_Spn_Spp`), each from a theorem about three
sets (`thm_T3a` … `thm_T3d`).

The route is not the note's general Theorem T: in each scheme every non-literal member is shown
to have a first head-normal-form item of leaf count at most `M + 2`, by the cases of Lemma W
specialised to the scheme (Lemma LL, Lemma SR, Corollary LL1, and for `S (S n p) (S p p)`
Lemma D\*), and then Theorem X applies.  The pair graph, Lemma W, tameness and Theorem T are not
stated.
-/

namespace Ncfp
open HnfS HeadRec Conv

/-- A non-literal `y u` with `u ≠ S` and head normal form `S h₁ h₂`: `h₂ = y' h₁`, and `h₁` is
`u` or larger than `u`. -/
theorem nonlit_form {y u h₁ h₂ : Term} (hp : PureS (y ⬝ u)) (hu : u ≠ S)
    (hs : Steps (y ⬝ u) (S ⬝ h₁ ⬝ h₂)) (hne : y ⬝ u ≠ S ⬝ h₁ ⬝ h₂) :
    ∃ y', h₂ = y' ⬝ h₁ ∧ (h₁ = u ∨ sz u < sz h₁) := by
  rcases lemma_LL hp hu (plus_of_steps_ne hs hne) with ⟨y', e1, e2, _⟩ | ⟨p, q, _, e1, e2, hw⟩
  · exact ⟨y', by rw [e2, e1], .inl e1⟩
  · have h1 := hw.sz_le
    have h2 := sz_arg_lt p q
    rw [← e1] at h2
    exact ⟨q, by rw [e2, e1], .inr (by omega)⟩

theorem big_ne_S {M : Nat} {t : Term} (h : M + 2 < sz t) : t ≠ S := by
  intro e
  rw [e] at h
  have e1 : sz S = 1 := rfl
  omega

/-- The last step of the four proofs: Theorem X for the union of three sets of kind two. -/
theorem three_X {M : Nat} {U : Term → Prop}
    (hU : ∀ t, U t → PureS t ∧ ∃ c d, Steps t (S ⬝ c ⬝ d) ∧ (U c ∨ sz c ≤ M) ∧ (U d ∨ sz d ≤ M) ∧
      (U c ∨ U d) ∧ (t ≠ S ⬝ c ⬝ d → sz c ≤ M + 2)) : ∀ t, ¬ U t := by
  refine thm_X (M := M + 2) (Z := U) ?_
  intro t ht
  obtain ⟨hp, c, d, hs, h1, h2, h3, h4⟩ := hU t ht
  refine ⟨hp, .inr ⟨c, d, hs, ?_, ?_, h3, h4⟩⟩
  · rcases h1 with h | h
    · exact .inl h
    · exact .inr (by omega)
  · rcases h2 with h | h
    · exact .inl h
    · exact .inr (by omega)

/-! ## `S (S p p) (S n p)`: A: [B, C], B: [A, A], C: [σ, A] -/

theorem thm_T3a {M : Nat} {A B C : Term → Prop}
    (hA : ∀ t, A t → PureS t ∧ ∃ a b, Steps t (S ⬝ a ⬝ b) ∧ B a ∧ C b)
    (hB : ∀ t, B t → PureS t ∧ ∃ a b, Steps t (S ⬝ a ⬝ b) ∧ A a ∧ A b)
    (hC : ∀ t, C t → PureS t ∧ ∃ a b, Steps t (S ⬝ a ⬝ b) ∧ (Normalizing a ∧ sz a ≤ M) ∧ A b) :
    ∀ t, ¬ A t := by
  have hU : ∀ v, (A v ∨ B v ∨ C v) → PureS v ∧ ∃ a b, Steps v (S ⬝ a ⬝ b) ∧
      ((A a ∨ B a ∨ C a) ∨ (A b ∨ B b ∨ C b)) := by
    rintro v (h | h | h)
    · obtain ⟨hp, a, b, hs, ha, _⟩ := hA v h
      exact ⟨hp, a, b, hs, .inl (.inr (.inl ha))⟩
    · obtain ⟨hp, a, b, hs, ha, _⟩ := hB v h
      exact ⟨hp, a, b, hs, .inl (.inl ha)⟩
    · obtain ⟨hp, a, b, hs, _, hb⟩ := hC v h
      exact ⟨hp, a, b, hs, .inr (.inl hb)⟩
  have dAC : ∀ t, A t → C t → False := by
    intro t h1 h2
    obtain ⟨_, a, b, hs, ha, _⟩ := hA t h1
    obtain ⟨_, a', b', hs', ha', _⟩ := hC t h2
    have e := run_hnf_hnf (.inr (.inr ⟨a, b, rfl⟩)) (.inr (.inr ⟨a', b', rfl⟩)) hs hs'
    injection e with e1 _
    injection e1 with _ e2
    rw [← e2] at ha'
    exact not_normalizing hU (.inr (.inl ha)) ha'.1
  have dAB : ∀ t, A t → B t → False := by
    intro t h1 h2
    obtain ⟨_, a, b, hs, _, hb⟩ := hA t h1
    obtain ⟨_, a', b', hs', _, hb'⟩ := hB t h2
    have e := run_hnf_hnf (.inr (.inr ⟨a, b, rfl⟩)) (.inr (.inr ⟨a', b', rfl⟩)) hs hs'
    injection e with _ e2
    rw [← e2] at hb'
    exact dAC b hb' hb
  -- a member of `C` with a large last item in `B`
  have deadC : ∀ y x, B x → M + 2 < sz x → C (y ⬝ x) → False := by
    intro y x hx hbig hw
    obtain ⟨hp, c, d, hs, hc, hd⟩ := hC _ hw
    rcases (lemma_SR hp hs).2 (big_ne_S hbig) with e | ⟨h, _⟩
    · injection e with _ e2
      rw [← e2] at hd
      exact dAB x hd hx
    · have := hc.2
      omega
  refine fun t h => three_X (M := M) (U := fun t => A t ∨ B t ∨ C t) ?_ t (.inl h)
  rintro t (h | h | h)
  · obtain ⟨hp, a, b, hs, ha, hb⟩ := hA t h
    refine ⟨hp, a, b, hs, .inl (.inr (.inl ha)), .inl (.inr (.inr hb)), .inl (.inr (.inl ha)), ?_⟩
    intro ne
    obtain ⟨y, _, eb⟩ := lemma_L' hp hs ne
    rw [eb] at hb
    rcases Nat.lt_or_ge (M + 2) (sz a) with hbig | hle
    · exact (deadC y a ha hbig hb).elim
    · exact hle
  · obtain ⟨hp, a, b, hs, ha, hb⟩ := hB t h
    refine ⟨hp, a, b, hs, .inl (.inl ha), .inl (.inl hb), .inl (.inl ha), ?_⟩
    intro ne
    obtain ⟨y, _, eb⟩ := lemma_L' hp hs ne
    rw [eb] at hb
    rcases Nat.lt_or_ge (M + 2) (sz a) with hbig | hle
    · exfalso
      obtain ⟨hpw, h₁, h₂, hsw, hB₁, hC₂⟩ := hA _ hb
      rcases Decidable.em (y ⬝ a = S ⬝ h₁ ⬝ h₂) with e | ne'
      · injection e with _ e2
        rw [← e2] at hC₂
        exact dAC a ha hC₂
      · obtain ⟨y', e2, hsz⟩ := nonlit_form hpw (big_ne_S hbig) hsw ne'
        rw [e2] at hC₂
        have hbig₁ : M + 2 < sz h₁ := by
          rcases hsz with e | h
          · rw [e]; exact hbig
          · omega
        exact deadC y' h₁ hB₁ hbig₁ hC₂
    · exact hle
  · obtain ⟨hp, a, b, hs, ha, hb⟩ := hC t h
    exact ⟨hp, a, b, hs, .inr ha.2, .inl (.inl hb), .inr (.inl hb), fun _ => by have := ha.2; omega⟩

/-! ## `S (S p p) (S p n)`: A: [B, C], B: [A, A], C: [A, σ] -/

theorem thm_T3b {M : Nat} {A B C : Term → Prop}
    (hA : ∀ t, A t → PureS t ∧ ∃ a b, Steps t (S ⬝ a ⬝ b) ∧ B a ∧ C b)
    (hB : ∀ t, B t → PureS t ∧ ∃ a b, Steps t (S ⬝ a ⬝ b) ∧ A a ∧ A b)
    (hC : ∀ t, C t → PureS t ∧ ∃ a b, Steps t (S ⬝ a ⬝ b) ∧ A a ∧ (Normalizing b ∧ sz b ≤ M)) :
    ∀ t, ¬ A t := by
  have hU : ∀ v, (A v ∨ B v ∨ C v) → PureS v ∧ ∃ a b, Steps v (S ⬝ a ⬝ b) ∧
      ((A a ∨ B a ∨ C a) ∨ (A b ∨ B b ∨ C b)) := by
    rintro v (h | h | h)
    · obtain ⟨hp, a, b, hs, ha, _⟩ := hA v h
      exact ⟨hp, a, b, hs, .inl (.inr (.inl ha))⟩
    · obtain ⟨hp, a, b, hs, ha, _⟩ := hB v h
      exact ⟨hp, a, b, hs, .inl (.inl ha)⟩
    · obtain ⟨hp, a, b, hs, ha, _⟩ := hC v h
      exact ⟨hp, a, b, hs, .inl (.inl ha)⟩
  have dAC : ∀ t, A t → C t → False := by
    intro t h1 h2
    obtain ⟨_, a, b, hs, _, hb⟩ := hA t h1
    obtain ⟨_, a', b', hs', _, hb'⟩ := hC t h2
    have e := run_hnf_hnf (.inr (.inr ⟨a, b, rfl⟩)) (.inr (.inr ⟨a', b', rfl⟩)) hs hs'
    injection e with _ e2
    rw [← e2] at hb'
    exact not_normalizing hU (.inr (.inr hb)) hb'.1
  -- a member of `C` has a small last item
  have lastC : ∀ y x, C (y ⬝ x) → sz x ≤ M := by
    intro y x hw
    obtain ⟨hp, c, d, hs, _, hd⟩ := hC _ hw
    exact Nat.le_trans (lemma_SR hp hs).1 hd.2
  refine fun t h => three_X (M := M) (U := fun t => A t ∨ B t ∨ C t) ?_ t (.inl h)
  rintro t (h | h | h)
  · obtain ⟨hp, a, b, hs, ha, hb⟩ := hA t h
    refine ⟨hp, a, b, hs, .inl (.inr (.inl ha)), .inl (.inr (.inr hb)), .inl (.inr (.inl ha)), ?_⟩
    intro ne
    obtain ⟨y, _, eb⟩ := lemma_L' hp hs ne
    rw [eb] at hb
    have := lastC y a hb
    omega
  · obtain ⟨hp, a, b, hs, ha, hb⟩ := hB t h
    refine ⟨hp, a, b, hs, .inl (.inl ha), .inl (.inl hb), .inl (.inl ha), ?_⟩
    intro ne
    obtain ⟨y, _, eb⟩ := lemma_L' hp hs ne
    rw [eb] at hb
    rcases Nat.lt_or_ge (M + 2) (sz a) with hbig | hle
    · exfalso
      obtain ⟨hpw, h₁, h₂, hsw, _, hC₂⟩ := hA _ hb
      rcases Decidable.em (y ⬝ a = S ⬝ h₁ ⬝ h₂) with e | ne'
      · injection e with _ e2
        rw [← e2] at hC₂
        exact dAC a ha hC₂
      · obtain ⟨y', e2, hsz⟩ := nonlit_form hpw (big_ne_S hbig) hsw ne'
        rw [e2] at hC₂
        have := lastC y' h₁ hC₂
        rcases hsz with e | h
        · rw [e] at this; omega
        · omega
    · exact hle
  · obtain ⟨hp, a, b, hs, ha, hb⟩ := hC t h
    refine ⟨hp, a, b, hs, .inl (.inl ha), .inr hb.2, .inl (.inl ha), ?_⟩
    intro ne
    obtain ⟨y, _, eb⟩ := lemma_L' hp hs ne
    have h1 := sz_arg_lt y a
    rw [← eb] at h1
    have := hb.2
    omega

/-! ## `S (S p n) (S p p)`: A: [B, C], B: [A, σ], C: [A, A] -/

theorem thm_T3d {M : Nat} {A B C : Term → Prop}
    (hA : ∀ t, A t → PureS t ∧ ∃ a b, Steps t (S ⬝ a ⬝ b) ∧ B a ∧ C b)
    (hB : ∀ t, B t → PureS t ∧ ∃ a b, Steps t (S ⬝ a ⬝ b) ∧ A a ∧ (Normalizing b ∧ sz b ≤ M))
    (hC : ∀ t, C t → PureS t ∧ ∃ a b, Steps t (S ⬝ a ⬝ b) ∧ A a ∧ A b) :
    ∀ t, ¬ A t := by
  have hU : ∀ v, (A v ∨ B v ∨ C v) → PureS v ∧ ∃ a b, Steps v (S ⬝ a ⬝ b) ∧
      ((A a ∨ B a ∨ C a) ∨ (A b ∨ B b ∨ C b)) := by
    rintro v (h | h | h)
    · obtain ⟨hp, a, b, hs, ha, _⟩ := hA v h
      exact ⟨hp, a, b, hs, .inl (.inr (.inl ha))⟩
    · obtain ⟨hp, a, b, hs, ha, _⟩ := hB v h
      exact ⟨hp, a, b, hs, .inl (.inl ha)⟩
    · obtain ⟨hp, a, b, hs, ha, _⟩ := hC v h
      exact ⟨hp, a, b, hs, .inl (.inl ha)⟩
  have dAB : ∀ t, A t → B t → False := by
    intro t h1 h2
    obtain ⟨_, a, b, hs, _, hb⟩ := hA t h1
    obtain ⟨_, a', b', hs', _, hb'⟩ := hB t h2
    have e := run_hnf_hnf (.inr (.inr ⟨a, b, rfl⟩)) (.inr (.inr ⟨a', b', rfl⟩)) hs hs'
    injection e with _ e2
    rw [← e2] at hb'
    exact not_normalizing hU (.inr (.inr hb)) hb'.1
  have dAC : ∀ t, A t → C t → False := by
    intro t h1 h2
    obtain ⟨_, a, b, hs, ha, _⟩ := hA t h1
    obtain ⟨_, a', b', hs', ha', _⟩ := hC t h2
    have e := run_hnf_hnf (.inr (.inr ⟨a, b, rfl⟩)) (.inr (.inr ⟨a', b', rfl⟩)) hs hs'
    injection e with e1 _
    injection e1 with _ e2
    rw [← e2] at ha'
    exact dAB a ha' ha
  -- a member of `A` with a large last item in `A`
  have deadAA : ∀ y z, A z → M + 2 < sz z → A (y ⬝ z) → False := by
    intro y z hz hbig hw
    obtain ⟨hp, h₁, h₂, hs, hB₁, hC₂⟩ := hA _ hw
    rcases Decidable.em (y ⬝ z = S ⬝ h₁ ⬝ h₂) with e | ne
    · injection e with _ e2
      rw [← e2] at hC₂
      exact dAC z hz hC₂
    · rcases lemma_LL hp (big_ne_S hbig) (plus_of_steps_ne hs ne) with ⟨y', e1, _, _⟩ |
        ⟨p, q, _, e1, _, hw'⟩
      · rw [e1] at hB₁
        exact dAB z hz hB₁
      · rw [e1] at hB₁
        obtain ⟨hpq, c, d, hs', _, hd⟩ := hB _ hB₁
        have h1 := (lemma_SR hpq hs').1
        have h2 := hw'.sz_le
        have := hd.2
        omega
  refine fun t h => three_X (M := M) (U := fun t => A t ∨ B t ∨ C t) ?_ t (.inl h)
  rintro t (h | h | h)
  · obtain ⟨hp, a, b, hs, ha, hb⟩ := hA t h
    refine ⟨hp, a, b, hs, .inl (.inr (.inl ha)), .inl (.inr (.inr hb)), .inl (.inr (.inl ha)), ?_⟩
    intro ne
    obtain ⟨y, _, eb⟩ := lemma_L' hp hs ne
    rw [eb] at hb
    rcases Nat.lt_or_ge (M + 2) (sz a) with hbig | hle
    · exfalso
      obtain ⟨hpw, h₁, h₂, hsw, hA₁, hA₂⟩ := hC _ hb
      rcases Decidable.em (y ⬝ a = S ⬝ h₁ ⬝ h₂) with e | ne'
      · injection e with _ e2
        rw [← e2] at hA₂
        exact dAB a hA₂ ha
      · obtain ⟨y', e2, hsz⟩ := nonlit_form hpw (big_ne_S hbig) hsw ne'
        rw [e2] at hA₂
        rcases hsz with e | h
        · rw [e] at hA₁
          exact dAB a hA₁ ha
        · exact deadAA y' h₁ hA₁ (by omega) hA₂
    · exact hle
  · obtain ⟨hp, a, b, hs, ha, hb⟩ := hB t h
    refine ⟨hp, a, b, hs, .inl (.inl ha), .inr hb.2, .inl (.inl ha), ?_⟩
    intro ne
    obtain ⟨y, _, eb⟩ := lemma_L' hp hs ne
    have h1 := sz_arg_lt y a
    rw [← eb] at h1
    have := hb.2
    omega
  · obtain ⟨hp, a, b, hs, ha, hb⟩ := hC t h
    refine ⟨hp, a, b, hs, .inl (.inl ha), .inl (.inl hb), .inl (.inl ha), ?_⟩
    intro ne
    obtain ⟨y, _, eb⟩ := lemma_L' hp hs ne
    rw [eb] at hb
    rcases Nat.lt_or_ge (M + 2) (sz a) with hbig | hle
    · exact (deadAA y a ha hbig hb).elim
    · exact hle

/-! ## `S (S n p) (S p p)`: A: [B, C], B: [σ, A], C: [A, A] -/

theorem thm_T3c {M : Nat} {A B C : Term → Prop}
    (hA : ∀ t, A t → PureS t ∧ ∃ a b, Steps t (S ⬝ a ⬝ b) ∧ B a ∧ C b)
    (hB : ∀ t, B t → PureS t ∧ ∃ a b, Steps t (S ⬝ a ⬝ b) ∧ (Normalizing a ∧ sz a ≤ M) ∧ A b)
    (hC : ∀ t, C t → PureS t ∧ ∃ a b, Steps t (S ⬝ a ⬝ b) ∧ A a ∧ A b) :
    ∀ t, ¬ A t := by
  have hU : ∀ v, (A v ∨ B v ∨ C v) → PureS v ∧ ∃ a b, Steps v (S ⬝ a ⬝ b) ∧
      ((A a ∨ B a ∨ C a) ∨ (A b ∨ B b ∨ C b)) := by
    rintro v (h | h | h)
    · obtain ⟨hp, a, b, hs, ha, _⟩ := hA v h
      exact ⟨hp, a, b, hs, .inl (.inr (.inl ha))⟩
    · obtain ⟨hp, a, b, hs, _, hb⟩ := hB v h
      exact ⟨hp, a, b, hs, .inr (.inl hb)⟩
    · obtain ⟨hp, a, b, hs, ha, _⟩ := hC v h
      exact ⟨hp, a, b, hs, .inl (.inl ha)⟩
  have nnA : ∀ t, A t → ¬ Normalizing t := fun t h => not_normalizing hU (.inl h)
  have nnB : ∀ t, B t → ¬ Normalizing t := fun t h => not_normalizing hU (.inr (.inl h))
  have dAB : ∀ t, A t → B t → False := by
    intro t h1 h2
    obtain ⟨_, a, b, hs, ha, _⟩ := hA t h1
    obtain ⟨_, a', b', hs', ha', _⟩ := hB t h2
    have e := run_hnf_hnf (.inr (.inr ⟨a, b, rfl⟩)) (.inr (.inr ⟨a', b', rfl⟩)) hs hs'
    injection e with e1 _
    injection e1 with _ e2
    rw [← e2] at ha'
    exact nnB a ha ha'.1
  have dAC : ∀ t, A t → C t → False := by
    intro t h1 h2
    obtain ⟨_, a, b, hs, ha, _⟩ := hA t h1
    obtain ⟨_, a', b', hs', ha', _⟩ := hC t h2
    have e := run_hnf_hnf (.inr (.inr ⟨a, b, rfl⟩)) (.inr (.inr ⟨a', b', rfl⟩)) hs hs'
    injection e with e1 _
    injection e1 with _ e2
    rw [← e2] at ha'
    exact dAB a ha' ha
  have e1S : sz S = 1 := rfl
  -- a member `p' q'` of `B` whose last item is large has `p' = S c`, `c` small
  have headB : ∀ p' q', B (p' ⬝ q') → M + 2 < sz q' →
      ∃ c, p' = S ⬝ c ∧ Normalizing c ∧ sz c ≤ M := by
    intro p' q' hw hbig
    obtain ⟨hp, c, d, hs, hc, _⟩ := hB _ hw
    obtain ⟨e, _⟩ := cor_LL1 hp (big_ne_S hbig) hs (by have := hc.2; omega)
    exact ⟨c, e, hc.1, hc.2⟩
  -- states (A, A, B) and (A, A, λ) are dead
  have dead3 : ∀ F x, A x → M + 2 < sz x → A (F ⬝ x) →
      (B F ∨ ∃ g p, F = g ⬝ p ∧ M + 2 < sz p) → False := by
    intro F x hx hbig hw hF
    obtain ⟨hp, h₁, h₂, hs, hB₁, hC₂⟩ := hA _ hw
    rcases Decidable.em (F ⬝ x = S ⬝ h₁ ⬝ h₂) with e | ne
    · injection e with _ e2
      rw [← e2] at hC₂
      exact dAC x hx hC₂
    · obtain ⟨b₁, aR, hsF, _, hcase⟩ := lemma_Dstar hp (by omega) (plus_of_steps_ne hs ne)
      rcases hcase with ⟨_, e1, _⟩ | ⟨eb, e1, _⟩ | ⟨p', q', _, hw', ⟨g', eq'⟩, e1, _⟩
      · rw [e1] at hB₁
        exact dAB x hx hB₁
      · rw [e1] at hB₁
        obtain ⟨c, eaR, hcn, hcM⟩ := headB aR x hB₁ hbig
        rw [eb] at hsF
        rcases hF with hBF | ⟨g, p, eF, hpbig⟩
        · obtain ⟨_, a', b', hs', _, hb'⟩ := hB F hBF
          have e := run_hnf_hnf (.inr (.inr ⟨a', b', rfl⟩)) (.inr (.inr ⟨S ⬝ S, aR, rfl⟩)) hs' hsF
          injection e with _ e2
          rw [e2, eaR] at hb'
          exact nnA _ hb' (normalizing_S1 hcn)
        · rw [eF] at hsF
          have hpF := hp.app_inv.1
          rw [eF] at hpF
          have e2S : sz (S ⬝ S) = 2 := rfl
          obtain ⟨_, e⟩ := cor_LL1 hpF (big_ne_S hpbig) hsF (by omega)
          rw [eaR] at e
          have e3 : sz (S ⬝ c) = 1 + sz c := rfl
          rw [← e] at hpbig
          omega
      · rw [e1] at hB₁
        have h1 := hw'.sz_le
        have h2 : sz p' < sz q' := by rw [eq']; exact sz_arg_lt g' p'
        obtain ⟨c, ep, _, hcM⟩ := headB p' q' hB₁ (by omega)
        have e3 : sz (S ⬝ c) = 1 + sz c := rfl
        rw [ep] at h1
        omega
  refine fun t h => three_X (M := M) (U := fun t => A t ∨ B t ∨ C t) ?_ t (.inl h)
  rintro t (h | h | h)
  · -- a non-literal member of `A`: state (C, B, ∗)
    obtain ⟨hp, a, b, hs, ha, hb⟩ := hA t h
    refine ⟨hp, a, b, hs, .inl (.inr (.inl ha)), .inl (.inr (.inr hb)), .inl (.inr (.inl ha)), ?_⟩
    intro ne
    obtain ⟨y, _, eb⟩ := lemma_L' hp hs ne
    rw [eb] at hb
    rcases Nat.lt_or_ge (M + 2) (sz a) with hbig | hle
    · exfalso
      obtain ⟨hpw, h₁, h₂, hsw, hA₁, hA₂⟩ := hC _ hb
      rcases Decidable.em (y ⬝ a = S ⬝ h₁ ⬝ h₂) with e | ne'
      · injection e with _ e2
        rw [← e2] at hA₂
        exact dAB a hA₂ ha
      · obtain ⟨b₁, aR, _, _, hcase⟩ := lemma_Dstar hpw (by omega) (plus_of_steps_ne hsw ne')
        rcases hcase with ⟨_, e1, _⟩ | ⟨_, e1, e2⟩ | ⟨p', q', _, hw', ⟨g', eq'⟩, e1, e2⟩
        · rw [e1] at hA₁
          exact dAB a hA₁ ha
        · rw [e1] at hA₁
          rw [e2] at hA₂
          have h1 := sz_arg_lt aR a
          exact dead3 a (aR ⬝ a) hA₁ (by omega) hA₂ (.inl ha)
        · rw [e1] at hA₁
          rw [e2] at hA₂
          have h1 := hw'.sz_le
          have h2 := sz_arg_lt p' q'
          have h3 : sz p' < sz q' := by rw [eq']; exact sz_arg_lt g' p'
          exact dead3 q' (p' ⬝ q') hA₁ (by omega) hA₂ (.inr ⟨g', p', eq', by omega⟩)
    · exact hle
  · obtain ⟨hp, a, b, hs, ha, hb⟩ := hB t h
    exact ⟨hp, a, b, hs, .inr ha.2, .inl (.inl hb), .inr (.inl hb), fun _ => by have := ha.2; omega⟩
  · -- a non-literal member of `C`: state (A, A, ∗)
    obtain ⟨hp, a, b, hs, ha, hb⟩ := hC t h
    refine ⟨hp, a, b, hs, .inl (.inl ha), .inl (.inl hb), .inl (.inl ha), ?_⟩
    intro ne
    obtain ⟨y, _, eb⟩ := lemma_L' hp hs ne
    rw [eb] at hb
    rcases Nat.lt_or_ge (M + 2) (sz a) with hbig | hle
    · exfalso
      obtain ⟨hpw, h₁, h₂, hsw, hB₁, hC₂⟩ := hA _ hb
      rcases Decidable.em (y ⬝ a = S ⬝ h₁ ⬝ h₂) with e | ne'
      · injection e with _ e2
        rw [← e2] at hC₂
        exact dAC a ha hC₂
      · obtain ⟨b₁, aR, _, _, hcase⟩ := lemma_Dstar hpw (by omega) (plus_of_steps_ne hsw ne')
        rcases hcase with ⟨_, e1, _⟩ | ⟨_, e1, e2⟩ | ⟨p', q', _, hw', ⟨g', eq'⟩, e1, _⟩
        · rw [e1] at hB₁
          exact dAB a ha hB₁
        · -- state (C, B, A): `a (aR a) ∈ C`, `aR a ∈ B`, function part `a ∈ A`
          rw [e1] at hB₁
          rw [e2] at hC₂
          have hxbig : M + 2 < sz (aR ⬝ a) := by have := sz_arg_lt aR a; omega
          obtain ⟨hpw₂, k₁, k₂, hsw₂, hA₁, hA₂⟩ := hC _ hC₂
          rcases Decidable.em (a ⬝ (aR ⬝ a) = S ⬝ k₁ ⬝ k₂) with e | ne₂
          · injection e with _ e3
            rw [← e3] at hA₂
            exact dAB _ hA₂ hB₁
          · obtain ⟨b₁', aR', hsa, _, hcase₂⟩ :=
              lemma_Dstar hpw₂ (by omega) (plus_of_steps_ne hsw₂ ne₂)
            obtain ⟨_, a', b', hs', ha', _⟩ := hA a ha
            have e := run_hnf_hnf (.inr (.inr ⟨a', b', rfl⟩)) (.inr (.inr ⟨b₁', aR', rfl⟩)) hs' hsa
            injection e with e3 _
            injection e3 with _ e4
            rw [e4] at ha'
            rcases hcase₂ with ⟨eb', _, _⟩ | ⟨eb', _, _⟩ | ⟨p', q', _, hw', ⟨g', eq'⟩, e5, e6⟩
            · rw [eb'] at ha'
              exact nnB _ ha' ⟨S, .refl _, normal_S⟩
            · rw [eb'] at ha'
              exact nnB _ ha' (normalizing_S1 ⟨S, .refl _, normal_S⟩)
            · rw [e5] at hA₁
              rw [e6] at hA₂
              have h1 := hw'.sz_le
              have h2 := sz_arg_lt p' q'
              have h3 : sz p' < sz q' := by rw [eq']; exact sz_arg_lt g' p'
              exact dead3 q' (p' ⬝ q') hA₁ (by omega) hA₂ (.inr ⟨g', p', eq', by omega⟩)
        · rw [e1] at hB₁
          have h1 := hw'.sz_le
          have h2 : sz p' < sz q' := by rw [eq']; exact sz_arg_lt g' p'
          obtain ⟨c, ep, _, hcM⟩ := headB p' q' hB₁ (by omega)
          have e3 : sz (S ⬝ c) = 1 + sz c := rfl
          rw [ep] at h1
          omega
    · exact hle

/-! ## The four equations -/

/-- `p` is not convertible to `S (S p p) (S n p)`, for closed `p` and closed normalizing `n`. -/
theorem no_S_Spp_Snp {p n : Term} (hp : PureS p) (hn : PureS n) (hnn : Normalizing n) :
    ¬ Convertible p (S ⬝ (S ⬝ p ⬝ p) ⬝ (S ⬝ n ⬝ p)) := by
  intro hc
  obtain ⟨nf, hnnf, hnf⟩ := hnn
  refine thm_T3a (M := sz nf) (A := fun t => PureS t ∧ Convertible t p)
    (B := fun t => PureS t ∧ Convertible t (S ⬝ p ⬝ p))
    (C := fun t => PureS t ∧ Convertible t (S ⬝ n ⬝ p)) ?_ ?_ ?_ p ⟨hp, Convertible.refl p⟩
  · rintro t ⟨ht, hct⟩
    obtain ⟨a, b, hs, ca, cb⟩ :=
      hnf2_conv ht (.app (.app .S hp) hp) (.app (.app .S hn) hp) (hct.trans hc)
    have hpab := steps_pure ht hs
    exact ⟨ht, a, b, hs, ⟨hpab.app_inv.1.app_inv.2, ca⟩, ⟨hpab.app_inv.2, cb⟩⟩
  · rintro t ⟨ht, hct⟩
    obtain ⟨a, b, hs, ca, cb⟩ := hnf2_conv ht hp hp hct
    have hpab := steps_pure ht hs
    exact ⟨ht, a, b, hs, ⟨hpab.app_inv.1.app_inv.2, ca⟩, ⟨hpab.app_inv.2, cb⟩⟩
  · rintro t ⟨ht, hct⟩
    obtain ⟨m, a, hs, hpa, ca, hm, hsz⟩ := hnf2_conv_left ht hp hn hnnf hnf hct
    exact ⟨ht, m, a, hs, ⟨hm, hsz⟩, hpa, ca⟩

/-- `p` is not convertible to `S (S p p) (S p n)`, for closed `p` and closed normalizing `n`. -/
theorem no_S_Spp_Spn {p n : Term} (hp : PureS p) (hn : PureS n) (hnn : Normalizing n) :
    ¬ Convertible p (S ⬝ (S ⬝ p ⬝ p) ⬝ (S ⬝ p ⬝ n)) := by
  intro hc
  obtain ⟨nf, hnnf, hnf⟩ := hnn
  refine thm_T3b (M := sz nf) (A := fun t => PureS t ∧ Convertible t p)
    (B := fun t => PureS t ∧ Convertible t (S ⬝ p ⬝ p))
    (C := fun t => PureS t ∧ Convertible t (S ⬝ p ⬝ n)) ?_ ?_ ?_ p ⟨hp, Convertible.refl p⟩
  · rintro t ⟨ht, hct⟩
    obtain ⟨a, b, hs, ca, cb⟩ :=
      hnf2_conv ht (.app (.app .S hp) hp) (.app (.app .S hp) hn) (hct.trans hc)
    have hpab := steps_pure ht hs
    exact ⟨ht, a, b, hs, ⟨hpab.app_inv.1.app_inv.2, ca⟩, ⟨hpab.app_inv.2, cb⟩⟩
  · rintro t ⟨ht, hct⟩
    obtain ⟨a, b, hs, ca, cb⟩ := hnf2_conv ht hp hp hct
    have hpab := steps_pure ht hs
    exact ⟨ht, a, b, hs, ⟨hpab.app_inv.1.app_inv.2, ca⟩, ⟨hpab.app_inv.2, cb⟩⟩
  · rintro t ⟨ht, hct⟩
    obtain ⟨a, m, hs, hpa, ca, hm, hsz⟩ := hnf2_conv_right ht hp hn hnnf hnf hct
    exact ⟨ht, a, m, hs, ⟨hpa, ca⟩, hm, hsz⟩

/-- `p` is not convertible to `S (S n p) (S p p)`, for closed `p` and closed normalizing `n`. -/
theorem no_S_Snp_Spp {p n : Term} (hp : PureS p) (hn : PureS n) (hnn : Normalizing n) :
    ¬ Convertible p (S ⬝ (S ⬝ n ⬝ p) ⬝ (S ⬝ p ⬝ p)) := by
  intro hc
  obtain ⟨nf, hnnf, hnf⟩ := hnn
  refine thm_T3c (M := sz nf) (A := fun t => PureS t ∧ Convertible t p)
    (B := fun t => PureS t ∧ Convertible t (S ⬝ n ⬝ p))
    (C := fun t => PureS t ∧ Convertible t (S ⬝ p ⬝ p)) ?_ ?_ ?_ p ⟨hp, Convertible.refl p⟩
  · rintro t ⟨ht, hct⟩
    obtain ⟨a, b, hs, ca, cb⟩ :=
      hnf2_conv ht (.app (.app .S hn) hp) (.app (.app .S hp) hp) (hct.trans hc)
    have hpab := steps_pure ht hs
    exact ⟨ht, a, b, hs, ⟨hpab.app_inv.1.app_inv.2, ca⟩, ⟨hpab.app_inv.2, cb⟩⟩
  · rintro t ⟨ht, hct⟩
    obtain ⟨m, a, hs, hpa, ca, hm, hsz⟩ := hnf2_conv_left ht hp hn hnnf hnf hct
    exact ⟨ht, m, a, hs, ⟨hm, hsz⟩, hpa, ca⟩
  · rintro t ⟨ht, hct⟩
    obtain ⟨a, b, hs, ca, cb⟩ := hnf2_conv ht hp hp hct
    have hpab := steps_pure ht hs
    exact ⟨ht, a, b, hs, ⟨hpab.app_inv.1.app_inv.2, ca⟩, ⟨hpab.app_inv.2, cb⟩⟩

/-- `p` is not convertible to `S (S p n) (S p p)`, for closed `p` and closed normalizing `n`. -/
theorem no_S_Spn_Spp {p n : Term} (hp : PureS p) (hn : PureS n) (hnn : Normalizing n) :
    ¬ Convertible p (S ⬝ (S ⬝ p ⬝ n) ⬝ (S ⬝ p ⬝ p)) := by
  intro hc
  obtain ⟨nf, hnnf, hnf⟩ := hnn
  refine thm_T3d (M := sz nf) (A := fun t => PureS t ∧ Convertible t p)
    (B := fun t => PureS t ∧ Convertible t (S ⬝ p ⬝ n))
    (C := fun t => PureS t ∧ Convertible t (S ⬝ p ⬝ p)) ?_ ?_ ?_ p ⟨hp, Convertible.refl p⟩
  · rintro t ⟨ht, hct⟩
    obtain ⟨a, b, hs, ca, cb⟩ :=
      hnf2_conv ht (.app (.app .S hp) hn) (.app (.app .S hp) hp) (hct.trans hc)
    have hpab := steps_pure ht hs
    exact ⟨ht, a, b, hs, ⟨hpab.app_inv.1.app_inv.2, ca⟩, ⟨hpab.app_inv.2, cb⟩⟩
  · rintro t ⟨ht, hct⟩
    obtain ⟨a, m, hs, hpa, ca, hm, hsz⟩ := hnf2_conv_right ht hp hn hnnf hnf hct
    exact ⟨ht, a, m, hs, ⟨hpa, ca⟩, hm, hsz⟩
  · rintro t ⟨ht, hct⟩
    obtain ⟨a, b, hs, ca, cb⟩ := hnf2_conv ht hp hp hct
    have hpab := steps_pure ht hs
    exact ⟨ht, a, b, hs, ⟨hpab.app_inv.1.app_inv.2, ca⟩, ⟨hpab.app_inv.2, cb⟩⟩

end Ncfp
