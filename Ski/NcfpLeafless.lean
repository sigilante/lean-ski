import Ski.NcfpTheta
open Term

/-!
# NCFP: leafless sets with finitely many conversion classes

Source: `notes/NCFP-proof.md`, §12.2.  Setting and notation as in `Ski/Ncfp.lean` and
`Ski/NcfpTheta.lean`.

What is proved:

* `fact_LI` (Fact LI): along a head run the last item only gets wrapped, and it is untouched iff
  the run is a head run of the function part.
* `lemma_PR` (Lemma PR, parts 1, 3, 4, 5) and `pr_members` (part 2), for a `Z`-primitive member of
  a leafless set.
* `thm_L` (Theorem L): a leafless set that meets only finitely many conversion classes (every
  member is convertible to a term of a given list) is empty.  `thm_L_bounded` is the form the
  proof uses: a bound on the spine lengths `K` of the members is enough.
* `ncfp_holes` (Corollary L1): NCFP for every context `E ≠ hole` built from holes by `E ↦ S E′` and
  `E ↦ S E′ E″`.  It contains `ncfp_two`.

What is not proved: the conjecture that no leafless set exists; Corollary L2; Conj. HN.

Constructivity.  The conclusions are negations, and the proofs use excluded middle only in the
form `em_false` (to prove `False` one may split on any proposition), which needs no axiom: once to
find a `Z`-primitive member below a member, and once per representative to bound the spine
lengths.  The paper's "for all `i ≥ i₁`" is a downward induction on the size of the item `q`.
-/

namespace Ncfp
open HnfS HeadRec Conv

/-- To prove `False` one may split on any proposition (no axiom). -/
theorem em_false {A : Prop} (h : A ∨ ¬ A → False) : False :=
  h (.inr fun a => h (.inl a))

/-! ## Fact LI -/

/-- **Fact LI** (last items).  Along a head run from `e u` to `e' u'` the last item `u'` is a
wrapping `dₙ (⋯ (d₁ u))` of `u`; and either it is `u` itself and the run is a head run of `e`
(no frame with exactly three items was contracted), or it is larger than `u`. -/
theorem fact_LI {e u e' u' : Term} (hp : PureS (e ⬝ u)) (h : Steps (e ⬝ u) (e' ⬝ u')) :
    Wrap u u' ∧ ((u' = u ∧ Steps e e') ∨ sz u < sz u') := by
  obtain ⟨e₂, u₂, eq, hw⟩ := last_wrap h rfl hp
  injection eq with _ e2
  rw [← e2] at hw
  refine ⟨hw, ?_⟩
  rcases split h rfl hp with ⟨e'', he, hs⟩ | ⟨f, g, h1, h2⟩
  · injection he with e1 e3
    rw [← e1] at hs
    exact .inl ⟨e3, hs⟩
  · have hfg := steps_pure hp.app_inv.1 h1
    have hu := hp.app_inv.2
    have hp' : PureS (f ⬝ u ⬝ (g ⬝ u)) :=
      .app (.app hfg.app_inv.1.app_inv.2 hu) (.app hfg.app_inv.2 hu)
    obtain ⟨e₃, G', eq', hw'⟩ := last_wrap h2 rfl hp'
    injection eq' with _ e4
    rw [← e4] at hw'
    exact .inr (Nat.lt_of_lt_of_le (sz_arg_lt g u) hw'.sz_le)

/-! ## Spines -/

/-- `Spine k v`: the head normal form of `v` has two items, so has that of its second item, and
so on `k` times, and the `k`-th iterated second item has a one-item head normal form. -/
inductive Spine : Nat → Term → Prop
  | zero {v c : Term} : Steps v (S ⬝ c) → Spine 0 v
  | succ {k : Nat} {v a b : Term} : Steps v (S ⬝ a ⬝ b) → Spine k b → Spine (k + 1) v

theorem spine_fun {k : Nat} {v : Term} (h : Spine k v) : ∀ {k' : Nat}, Spine k' v → k = k' := by
  induction h with
  | @zero v c hs =>
    intro k' h'
    cases h' with
    | zero _ => rfl
    | @succ _ _ a b hs' _ =>
      have e := run_hnf_hnf (.inr (.inl ⟨c, rfl⟩)) (.inr (.inr ⟨a, b, rfl⟩)) hs hs'
      injection e with e1 _
      cases e1
  | @succ k v a b hs _ ih =>
    intro k' h'
    cases h' with
    | @zero _ c hs' =>
      have e := run_hnf_hnf (.inr (.inl ⟨c, rfl⟩)) (.inr (.inr ⟨a, b, rfl⟩)) hs' hs
      injection e with e1 _
      cases e1
    | @succ k₂ _ a' b' hs' hb' =>
      have e := run_hnf_hnf (.inr (.inr ⟨a, b, rfl⟩)) (.inr (.inr ⟨a', b', rfl⟩)) hs hs'
      injection e with _ e2
      rw [← e2] at hb'
      rw [ih hb']

/-- The spine length is a conversion invariant of closed S-terms (S6 Lemma 4, proof). -/
theorem spine_conv {k : Nat} {t : Term} (h : Spine k t) : ∀ {t' : Term}, PureS t → PureS t' →
    Convertible t t' → Spine k t' := by
  induction h with
  | @zero v c hs =>
    intro t' ht ht' hc
    have hpc := (steps_pure ht hs).app_inv.2
    obtain ⟨c', e, _⟩ := hnf1_conv ht' hpc (hc.symm.trans (Convertible.of_wsteps hs.weak))
    rw [e]
    exact .zero (.refl _)
  | @succ k v a b hs _ ih =>
    intro t' ht ht' hc
    have hpab := steps_pure ht hs
    obtain ⟨a', b', hs', _, cb⟩ := hnf2_conv ht' hpab.app_inv.1.app_inv.2 hpab.app_inv.2
      (hc.symm.trans (Convertible.of_wsteps hs.weak))
    exact .succ hs' (ih hpab.app_inv.2 (steps_pure ht' hs').app_inv.2 cb.symm)

/-! ## Lemma PR -/

theorem Leafless.not_S {Z : Term → Prop} (hZ : Leafless Z) : ¬ Z S := by
  intro h
  rcases (hZ S h).2 with ⟨a, hs, _⟩ | ⟨a, b, hs, _, _⟩
  · cases steps_S hs
  · cases steps_S hs

/-- `Sj j u = S (S (⋯ (S u)))` with `j` nested `S`. -/
def Sj : Nat → Term → Term
  | 0, u => u
  | j + 1, u => S ⬝ Sj j u

theorem sz_Sj_ge (j : Nat) (u : Term) : sz u ≤ sz (Sj j u) := by
  induction j with
  | zero => exact Nat.le_refl _
  | succ j ih => exact Nat.le_trans ih (Nat.le_of_lt (sz_arg_lt S _))

theorem IsItem.itemsub {m X c : Term} (h : IsItem m X) (hs : HeadRec.Sub c m) : ItemSub c X := by
  induction h with
  | last c₀ => exact .last c₀ hs
  | init o _ ih => exact .init o ih

/-- **Lemma PR (2).**  Let `t` be a `Z`-primitive member of a leafless set, with head normal form
`S tL tR`.  Every member of `Z` that is a subterm of an item of a frame of the head run of `t` is
`S^j tL` or `S^j tR` for some `j ≥ 0`. -/
theorem pr_members {Z : Term → Prop} (hZ : Leafless Z) {t tL tR : Term} (ht : PureS t)
    (hprim : ∀ m, PSub m t → ¬ Z m) (hs : Steps t (S ⬝ tL ⬝ tR)) (hL : Z tL) (hR : Z tR) :
    ∀ (n : Nat) (m : Term), sz m ≤ n → Z m → ∀ X, Steps t X → ItemSub m X →
      ∃ j, m = Sj j tL ∨ m = Sj j tR := by
  intro n
  induction n with
  | zero =>
    intro m h
    have := sz_pos m
    exfalso
    omega
  | succ n ih =>
    intro m hsz hm X hX hi
    rcases lemma_ZI_ii hX ht hi with h1 | ⟨X', hX', hit⟩
    · exact absurd hm (hprim m h1.psub)
    · obtain ⟨c, L, eX⟩ := hit.apps
      have hXH : Steps X' (S ⬝ tL ⬝ tR) := by
        rcases InfNF.steps_cmp hX' hs with h | h
        · exact h
        · rw [InfNF.steps_from_hnf (.inr (.inr ⟨tL, tR, rfl⟩)) h]
          exact .refl _
      have hg : GoodHnf (S ⬝ tL ⬝ tR) :=
        .inr (.inr ⟨tL, tR, rfl, hZ.fold_ne hL, hZ.fold_ne hR⟩)
      obtain ⟨hpm, hk⟩ := hZ m hm
      rcases hk with ⟨c₁, hs1, hc1⟩ | ⟨a, b, hs2, _, _⟩
      · have e := hnf1_literal hpm hs1
        have hsub : HeadRec.Sub c₁ m := by rw [e]; exact .right S .refl
        have hlt : sz c₁ < sz m := by rw [e]; exact sz_arg_lt S c₁
        obtain ⟨j, hj⟩ := ih c₁ (by omega) hc1 X' hX' (hit.itemsub hsub)
        rcases hj with h | h
        · exact ⟨j + 1, .inl (e.trans (congrArg (S ⬝ ·) h))⟩
        · exact ⟨j + 1, .inr (e.trans (congrArg (S ⬝ ·) h))⟩
      · rcases lemma_ZI_i hZ ⟨hm, a, b, hs2⟩ (steps_pure ht hX') eX hXH hg with e | ⟨b', e⟩ |
          ⟨a', e⟩
        · injection e with e1 _
          cases e1
        · injection e with e1 _
          injection e1 with _ e2
          exact ⟨0, .inl e2.symm⟩
        · injection e with _ e2
          exact ⟨0, .inr e2.symm⟩

/-- Lemma PR (1): a `Z`-primitive member is of kind 2, its head run takes a step, and case (B)
of Lemma TD holds. -/
theorem pr_one {Z : Term → Prop} (hZ : Leafless Z) {t : Term} (ht : Z t)
    (hprim : ∀ m, PSub m t → ¬ Z m) :
    ∃ tL tR y x p q, Steps t (S ⬝ tL ⬝ tR) ∧ Z tL ∧ Z tR ∧ tR = y ⬝ tL ∧
      Steps t (S ⬝ S ⬝ y ⬝ tL) ∧ Steps t (S ⬝ x ⬝ p ⬝ q) ∧ x ≠ S ∧ tL = p ⬝ q ∧
      Steps (x ⬝ q) (S ⬝ S ⬝ y) := by
  obtain ⟨hp, hk⟩ := hZ t ht
  rcases hk with ⟨c, hs, hc⟩ | ⟨tL, tR, hs, hL, hR⟩
  · have e := hnf1_literal hp hs
    exact absurd hc (hprim c (by rw [e]; exact .right S .refl))
  · rcases Decidable.em (t = S ⬝ tL ⬝ tR) with e | ne
    · exact absurd hL (hprim tL (by rw [e]; exact .left tR (.right S .refl)))
    · obtain ⟨y, eR, hlast, hcase⟩ := lemma_TD hp (plus_of_steps_ne hs ne)
      rcases hcase with ⟨tm, e, _⟩ | ⟨x, p, q, hfr, hx, eL, hφ⟩
      · exact absurd hL (hprim tL (by rw [e]; exact .right tm .refl))
      · exact ⟨tL, tR, y, x, p, q, hs, hL, hR, eR, hlast, hfr, hx, eL, hφ⟩

/-- The chain of steps 3 and 4 of Theorem Θ, for a leafless set: from `y₀ z ∈ Z` with `z` a
member of kind 2, the SS-chain `y₀, y₁, …` with `yₖ z ∈ Z` ends in `S a` with `a ∈ Z`, or in `S`
(and then its length is the spine length of `y₀ z`), or has `i` links so far. -/
theorem leafless_chain {Z : Term → Prop} (hZ : Leafless Z) {y₀ z : Term} (hz : K2 Z z) :
    ∀ i : Nat, Z (y₀ ⬝ z) →
      (∃ K a, SSPath K y₀ (S ⬝ a) ∧ Z a) ∨ (∃ K, SSPath K y₀ S ∧ Spine K (y₀ ⬝ z)) ∨
      ∃ y, SSPath i y₀ y ∧ Z (y ⬝ z) ∧ ∀ j, Spine j (y ⬝ z) → Spine (j + i) (y₀ ⬝ z) := by
  intro i h0
  induction i with
  | zero => exact .inr (.inr ⟨y₀, .zero _, h0, fun _ h => h⟩)
  | succ i ih =>
    rcases ih with done | done | ⟨y, path, hv, hsp⟩
    · exact .inl done
    · exact .inr (.inl done)
    · obtain ⟨hp, hk⟩ := hZ _ hv
      rcases hk with ⟨c, hs, _⟩ | ⟨a, b, hs, ha, hb⟩
      · have e := hnf1_literal hp hs
        injection e with e1 _
        have h1 := hsp 0 (.zero hs)
        rw [Nat.zero_add] at h1
        rw [e1] at path
        exact .inr (.inl ⟨i, path, h1⟩)
      · rcases Decidable.em (y ⬝ z = S ⬝ a ⬝ b) with e | ne
        · injection e with e1 _
          rw [e1] at path
          exact .inl ⟨i, a, path, ha⟩
        · obtain ⟨y', hlast, eb⟩ := lemma_L' hp hs ne
          rcases split hlast rfl hp with ⟨e', he, hs'⟩ | ⟨f, g, h1, h2⟩
          · injection he with e1 e2
            rw [← e1] at hs'
            have hb' : Z (y' ⬝ z) := by rw [eb, e2] at hb; exact hb
            refine .inr (.inr ⟨y', path.snoc hs', hb', fun j hj => ?_⟩)
            have hs2 : Steps (y ⬝ z) (S ⬝ z ⬝ (y' ⬝ z)) := by rw [eb, e2] at hs; exact hs
            have h3 := hsp (j + 1) (.succ hs2 hj)
            rw [show j + (i + 1) = j + 1 + i by omega]
            exact h3
          · exfalso
            have hfg := steps_pure hp.app_inv.1 h1
            have hpz := hp.app_inv.2
            have hpF : PureS (f ⬝ z ⬝ (g ⬝ z)) :=
              .app (.app hfg.app_inv.1.app_inv.2 hpz) (.app hfg.app_inv.2 hpz)
            have hg : GoodHnf (S ⬝ a ⬝ b) :=
              .inr (.inr ⟨a, b, rfl, hZ.fold_ne ha, hZ.fold_ne hb⟩)
            have hXH : Steps (S ⬝ S ⬝ y' ⬝ a) (S ⬝ a ⬝ b) := by
              rw [eb]
              exact .single (.S S y' a)
            obtain ⟨c', L', eX, hl⟩ := track_run hZ hz h2 hpF _ hXH hg f [g ⬝ z] rfl
            rcases frame3_item eX.symm hl with e1 | e1
            · have hpa := (steps_pure hp hs).app_inv.1.app_inv.2
              have h36 : fold (z ⬝ a) = 36 :=
                lemma_ZA_one hZ hz hpa (L := []) (fun _ hx => by cases hx)
              rw [eb, ← e1] at hb
              exact hZ.fold_ne hb h36
            · have hzS := hz.1
              rw [e1] at hzS
              exact hZ.not_S hzS

/-- **Lemma PR** (parts 1, 3, 4, 5; part 2 is `pr_members`).  Let `t` be a `Z`-primitive member
of a leafless set `Z`: a member no proper subterm of which is in `Z`.  Then `t` has a head normal
form `S tL tR` reached in one or more steps through a three-item frame `S x p q` with `x ≠ S`,
`tL = p q`, `tR = y tL`, `x q ↠h S S y`; `tL` is of kind 2 and `Z`-primitive; there is `K` with an
SS-chain of `K` links from `y` to `S`, so `sz y = 2K + 1`, and `t` has spine length `K + 1`; and
`q = S` with `sz x ≤ 2K + 2`, or `q = y` and `x = S S`. -/
theorem lemma_PR {Z : Term → Prop} (hZ : Leafless Z) {t : Term} (ht : Z t)
    (hprim : ∀ m, PSub m t → ¬ Z m) :
    ∃ tL tR y x p q K, Steps t (S ⬝ tL ⬝ tR) ∧ tR = y ⬝ tL ∧
      Steps t (S ⬝ x ⬝ p ⬝ q) ∧ x ≠ S ∧ tL = p ⬝ q ∧ Steps (x ⬝ q) (S ⬝ S ⬝ y) ∧
      K2 Z tL ∧ (∀ m, PSub m tL → ¬ Z m) ∧
      SSPath K y S ∧ sz y = 2 * K + 1 ∧ Spine (K + 1) t ∧
      ((q = S ∧ sz x ≤ 2 * K + 2) ∨ (q = y ∧ x = S ⬝ S)) := by
  obtain ⟨tL, tR, y, x, p, q, hs, hL, hR, eR, hlast, hfr, hx, eL, hφ⟩ := pr_one hZ ht hprim
  have hpt := (hZ t ht).1
  have h0 := sz_arg_lt y tL
  rw [← eR] at h0
  -- part 2, as a size bound
  have mem : ∀ m, Z m → ∀ X, Steps t X → ItemSub m X → sz tL ≤ sz m := by
    intro m hm X hX hi
    obtain ⟨j, hj⟩ := pr_members hZ hpt hprim hs hL hR (sz m) m (Nat.le_refl _) hm X hX hi
    rcases hj with e | e
    · rw [e]; exact sz_Sj_ge j tL
    · rw [e]; exact Nat.le_trans (Nat.le_of_lt h0) (sz_Sj_ge j tR)
  have hpq := sz_arg_lt p q
  rw [← eL] at hpq
  -- part 3
  have hk2 : K2 Z tL := by
    refine ⟨hL, ?_⟩
    obtain ⟨hpL, hk⟩ := hZ tL hL
    rcases hk with ⟨c, hs1, hc⟩ | ⟨a, b, hs2, _, _⟩
    · exfalso
      have e := hnf1_literal hpL hs1
      rw [eL] at e
      injection e with _ e2
      rw [← e2] at hc
      have := mem q hc _ hfr (.last _ .refl)
      omega
    · exact ⟨a, b, hs2⟩
  have hprimL : ∀ m, PSub m tL → ¬ Z m := by
    intro m hm hZm
    have hlt := hm.sz_lt
    rw [eL] at hm
    have hi : ItemSub m (S ⬝ x ⬝ p ⬝ q) := by
      cases hm with
      | left _ h => exact .init q (.last _ h)
      | right _ h => exact .last _ h
    have := mem m hZm _ hfr hi
    omega
  -- part 4
  have hy : PureS y := (steps_pure hpt hlast).app_inv.1.app_inv.2
  have hRy : Z (y ⬝ tL) := by rw [← eR]; exact hR
  have hpfr := steps_pure hpt hfr
  have hpxq : PureS (x ⬝ q) := .app hpfr.app_inv.1.app_inv.1.app_inv.2 hpfr.app_inv.2
  obtain ⟨K, path, hsp⟩ : ∃ K, SSPath K y S ∧ Spine K (y ⬝ tL) := by
    rcases leafless_chain hZ hk2 (2 * sz y + 1) hRy with ⟨K, a, path, ha⟩ | done | ⟨y', path, _, _⟩
    · exfalso
      have hne : a ≠ S := by
        intro e
        rw [e] at ha
        exact hZ.not_S ha
      have hr : Rigid a y := sspath_rigid hne hy path .base
      have eqy : q = y := by
        rcases Decidable.em (x ⬝ q = S ⬝ S ⬝ y) with e | ne'
        · exact (Term.app.inj e).2
        · obtain ⟨y'', _, e⟩ := lemma_L' hpxq hφ ne'
          exact absurd e (hr.not_appS hne y'')
      have hsub : ItemSub a (S ⬝ x ⬝ p ⬝ q) := by
        rw [eqy]
        exact .last _ hr.sub
      have h1 := mem a ha _ hfr hsub
      have h2 := hr.sz_lt
      rw [eqy] at hpq
      omega
    · exact done
    · have := ss_bound (sz y) y (Nat.le_refl _) hy _ _ path
      exfalso
      omega
  have hszy : sz y = 2 * K + 1 := by
    have h := cor_SS1 path hy
    have e : sz S = 1 := rfl
    omega
  have hspt : Spine (K + 1) t := by
    rw [← eR] at hsp
    exact .succ hs hsp
  -- part 5
  have h5 : (q = S ∧ sz x ≤ 2 * K + 2) ∨ (q = y ∧ x = S ⬝ S) := by
    obtain ⟨c, k, e1, e2⟩ := lemma_SS (sz (x ⬝ q)) (x ⬝ q) y (Nat.le_refl _) hpxq hφ
    cases k with
    | zero =>
      have e1' : x ⬝ q = S ⬝ S ⬝ c := e1
      have e2' : y = c := e2
      injection e1' with e3 e4
      exact .inr ⟨e4.trans e2'.symm, e3⟩
    | succ k =>
      have e1' : x ⬝ q = appS k (S ⬝ S ⬝ c) ⬝ S := e1
      injection e1' with _ e4
      have h1 := lemma_SS_sz hpxq hφ
      have h2 : sz (x ⬝ q) = sz x + sz q := rfl
      rw [e4] at h1 h2
      have e : sz S = 1 := rfl
      exact .inl ⟨e4, by omega⟩
  exact ⟨tL, tR, y, x, p, q, K, hs, eR, hfr, hx, eL, hφ, hk2, hprimL, path, hszy, hspt, h5⟩

/-! ## Theorem L -/

/-- **Theorem L**, the form the proof uses: a leafless set whose members have bounded spine
length is empty.  Uses Lemma PR, Fact LI and Theorem 2 (`right_combs`). -/
theorem thm_L_bounded {Z : Term → Prop} (hZ : Leafless Z) (Kb : Nat)
    (hK : ∀ t, Z t → ∀ k, Spine k t → k ≤ Kb) : ∀ t, ¬ Z t := by
  -- one step of the chain `tⁱ⁺¹ = (tⁱ)_L`, from a primitive member `p q`
  have stepP : ∀ p q, Z (p ⬝ q) → (∀ m, PSub m (p ⬝ q) → ¬ Z m) →
      ∃ x' p' q', sz x' ≤ 2 * Kb + 2 ∧ sz q' ≤ 2 * Kb + 1 ∧ sz q ≤ sz q' ∧
        Z (p' ⬝ q') ∧ (∀ m, PSub m (p' ⬝ q') → ¬ Z m) ∧
        ((q' = q ∧ Steps p (S ⬝ x' ⬝ p')) ∨ sz q < sz q') := by
    intro p q hZt hprim
    obtain ⟨tL, tR, y, x', p', q', K, _, _, hfr, _, eL, _, hk2, hprimL, _, hszy, hspt, h5⟩ :=
      lemma_PR hZ hZt hprim
    have hKb := hK _ hZt _ hspt
    obtain ⟨hw, hcase⟩ := fact_LI (hZ _ hZt).1 hfr
    have hx' : sz x' ≤ 2 * Kb + 2 := by
      rcases h5 with ⟨_, h⟩ | ⟨_, e⟩
      · omega
      · rw [e]
        have e' : sz (S ⬝ S) = 2 := rfl
        omega
    have hq' : sz q' ≤ 2 * Kb + 1 := by
      rcases h5 with ⟨e, _⟩ | ⟨e, _⟩
      · rw [e]
        have e' : sz S = 1 := rfl
        omega
      · rw [e]
        omega
    rw [eL] at hk2 hprimL
    exact ⟨x', p', q', hx', hq', hw.sz_le, hk2.1, hprimL, hcase⟩
  -- no primitive member `p q` with `sz q = s`, by downward induction on `s`
  have level : ∀ (d s : Nat), 2 * Kb + 2 ≤ s + d → ∀ p,
      ¬ ∃ q, sz q = s ∧ Z (p ⬝ q) ∧ ∀ m, PSub m (p ⬝ q) → ¬ Z m := by
    intro d
    induction d with
    | zero =>
      intro s hs p hP
      obtain ⟨q, hq, hZt, hprim⟩ := hP
      obtain ⟨x', p', q', _, h2, h3, _, _, _⟩ := stepP p q hZt hprim
      omega
    | succ d ih =>
      intro s hs
      have hC : Closed (2 * Kb + 2)
          (fun p => ∃ q, sz q = s ∧ Z (p ⬝ q) ∧ ∀ m, PSub m (p ⬝ q) → ¬ Z m) := by
        intro p hP
        obtain ⟨q, hq, hZt, hprim⟩ := hP
        refine ⟨(hZ _ hZt).1.app_inv.1, ?_⟩
        obtain ⟨x', p', q', h1, _, _, hZ', hprim', hcase⟩ := stepP p q hZt hprim
        rcases hcase with ⟨e, hsp⟩ | lt
        · exact ⟨p', ⟨q', by rw [e]; exact hq, hZ', hprim'⟩, .inr ⟨x', h1, hsp⟩⟩
        · exact absurd ⟨q', rfl, hZ', hprim'⟩ (ih (sz q') (by omega) p')
      exact right_combs hC
  -- a member has a primitive member below it
  have key : ∀ (n : Nat) (t : Term), sz t ≤ n → Z t → False := by
    intro n
    induction n with
    | zero =>
      intro t h _
      have := sz_pos t
      omega
    | succ n ih =>
      intro t hsz hZt
      apply em_false (A := ∃ m, PSub m t ∧ Z m)
      intro hem
      rcases hem with ⟨m, hm, hZm⟩ | hno
      · have := hm.sz_lt
        exact ih m (by omega) hZm
      · have hprim : ∀ m, PSub m t → ¬ Z m := fun m hm hZm => hno ⟨m, hm, hZm⟩
        obtain ⟨tL, tR, y, x, p, q, K, _, _, _, _, eL, _, hk2, hprimL, _, _, _, _⟩ :=
          lemma_PR hZ hZt hprim
        rw [eL] at hk2 hprimL
        exact level (2 * Kb + 2) (sz q) (by omega) p ⟨q, rfl, hk2.1, hprimL⟩
  intro t h
  exact key (sz t) t (Nat.le_refl _) h

/-- The spine lengths of the members of a leafless set that meets finitely many conversion
classes are bounded (under a double negation: the bound is not computed). -/
theorem spine_bound {Z : Term → Prop} (hZ : Leafless Z) : ∀ l : List Term,
    ¬¬ ∃ Kb, ∀ t, Z t → (∃ r, r ∈ l ∧ Convertible t r) → ∀ k, Spine k t → k ≤ Kb := by
  intro l
  induction l with
  | nil =>
    intro hn
    exact hn ⟨0, fun _ _ ⟨_, hr, _⟩ => by cases hr⟩
  | cons r l ih =>
    intro hn
    apply ih
    intro ⟨Kb, hKb⟩
    apply em_false (A := ∃ t k, Z t ∧ Convertible t r ∧ Spine k t)
    intro hem
    rcases hem with ⟨t₀, k₀, hZ₀, hc₀, hsp₀⟩ | hno
    · refine hn ⟨Kb + k₀, fun t hZt ⟨r', hr', hc⟩ k hsp => ?_⟩
      rcases List.mem_cons.mp hr' with e | hmem
      · rw [e] at hc
        have h1 := spine_conv hsp (hZ t hZt).1 (hZ t₀ hZ₀).1 (hc.trans hc₀.symm)
        have h2 := spine_fun h1 hsp₀
        omega
      · have := hKb t hZt ⟨r', hmem, hc⟩ k hsp
        omega
    · refine hn ⟨Kb, fun t hZt ⟨r', hr', hc⟩ k hsp => ?_⟩
      rcases List.mem_cons.mp hr' with e | hmem
      · rw [e] at hc
        exact absurd ⟨t, k, hZt, hc, hsp⟩ hno
      · exact hKb t hZt ⟨r', hmem, hc⟩ k hsp

/-- **Theorem L.**  Let `Z` be a leafless set (every member is a closed S-term with a head normal
form of one or two items, all in `Z`) that meets only finitely many conversion classes: every
member is convertible to a term of the list `l`.  Then `Z` is empty. -/
theorem thm_L {Z : Term → Prop} (hZ : Leafless Z) (l : List Term)
    (hfin : ∀ t, Z t → ∃ r, r ∈ l ∧ Convertible t r) : ∀ t, ¬ Z t := by
  intro t ht
  exact spine_bound hZ l (fun ⟨Kb, hKb⟩ =>
    thm_L_bounded hZ Kb (fun t' ht' k hsp => hKb t' ht' (hfin t' ht') k hsp) t ht)

/-! ## Corollary L1 -/

/-- Contexts built from holes by `E ↦ S E′` and `E ↦ S E′ E″`: every leaf is a hole. -/
inductive HCtx : Phi.Ctx → Prop
  | hole : HCtx .hole
  | one {E : Phi.Ctx} : HCtx E → HCtx (.app .s E)
  | two {E₁ E₂ : Phi.Ctx} : HCtx E₁ → HCtx E₂ → HCtx (.app (.app .s E₁) E₂)

/-- `SubC E' E`: `E'` is a subcontext of `E`. -/
inductive SubC (E' : Phi.Ctx) : Phi.Ctx → Prop
  | refl : SubC E' E'
  | left {c : Phi.Ctx} (d : Phi.Ctx) : SubC E' c → SubC E' (.app c d)
  | right (c : Phi.Ctx) {d : Phi.Ctx} : SubC E' d → SubC E' (.app c d)

theorem SubC.trans {a b c : Phi.Ctx} (h1 : SubC a b) (h2 : SubC b c) : SubC a c := by
  induction h2 with
  | refl => exact h1
  | left d _ ih => exact .left d ih
  | right c _ ih => exact .right c ih

/-- The list of the subcontexts of a context. -/
def subs : Phi.Ctx → List Phi.Ctx
  | .hole => [.hole]
  | .s => [.s]
  | .app c d => .app c d :: (subs c ++ subs d)

theorem subs_self : ∀ E : Phi.Ctx, E ∈ subs E
  | .hole => List.Mem.head _
  | .s => List.Mem.head _
  | .app _ _ => List.Mem.head _

theorem SubC.mem {E' E : Phi.Ctx} (h : SubC E' E) : E' ∈ subs E := by
  induction h with
  | refl => exact subs_self E'
  | left d _ ih => exact List.Mem.tail _ (List.mem_append_left _ ih)
  | right c _ ih => exact List.Mem.tail _ (List.mem_append_right _ ih)

theorem HCtx.hole_sub {E : Phi.Ctx} (h : HCtx E) : SubC .hole E := by
  induction h with
  | hole => exact .refl
  | one _ ih => exact .right _ ih
  | two _ _ _ ih₂ => exact .right _ ih₂

/-- **Corollary L1.**  Let `E ≠ hole` be built from holes by `E ↦ S E′` and `E ↦ S E′ E″` (any
number of holes, no closed part).  Then no closed S-term `p` is convertible to `E[p]`. -/
theorem ncfp_holes {p : Term} (hp : PureS p) {E : Phi.Ctx} (hE : HCtx E) (hne : E ≠ .hole) :
    ¬ Convertible p (E.plug p) := by
  intro hc
  have key : ∀ E' : Phi.Ctx, SubC E' E → HCtx E' → E' ≠ .hole → ∀ t, PureS t →
      Convertible t (E'.plug p) →
      (∃ a, Steps t (S ⬝ a) ∧
        (PureS a ∧ ∃ E'', SubC E'' E ∧ HCtx E'' ∧ Convertible a (E''.plug p))) ∨
      ∃ a b, Steps t (S ⬝ a ⬝ b) ∧
        (PureS a ∧ ∃ E'', SubC E'' E ∧ HCtx E'' ∧ Convertible a (E''.plug p)) ∧
        (PureS b ∧ ∃ E'', SubC E'' E ∧ HCtx E'' ∧ Convertible b (E''.plug p)) := by
    intro E' hsub hE' hne' t ht hct
    cases hE' with
    | hole => exact absurd rfl hne'
    | @one E₁ h1 =>
      have hct' : Convertible t (S ⬝ E₁.plug p) := hct
      obtain ⟨a, e, ca⟩ := hnf1_conv ht (Tower.plug_pure E₁ hp) hct'
      have hpa : PureS a := by
        rw [e] at ht
        exact ht.app_inv.2
      refine .inl ⟨a, by rw [e]; exact .refl _, hpa, E₁, (SubC.right _ .refl).trans hsub, h1, ca⟩
    | @two E₁ E₂ h1 h2 =>
      have hct' : Convertible t (S ⬝ E₁.plug p ⬝ E₂.plug p) := hct
      obtain ⟨a, b, hs, ca, cb⟩ :=
        hnf2_conv ht (Tower.plug_pure E₁ hp) (Tower.plug_pure E₂ hp) hct'
      have hpab := steps_pure ht hs
      exact .inr ⟨a, b, hs,
        ⟨hpab.app_inv.1.app_inv.2, E₁, (SubC.left _ (SubC.right _ .refl)).trans hsub, h1, ca⟩,
        ⟨hpab.app_inv.2, E₂, (SubC.right _ .refl).trans hsub, h2, cb⟩⟩
  have hZ : Leafless (fun t => PureS t ∧ ∃ E', SubC E' E ∧ HCtx E' ∧
      Convertible t (E'.plug p)) := by
    rintro t ⟨ht, E', hsub, hE', hct⟩
    refine ⟨ht, ?_⟩
    cases hE' with
    | hole =>
      have hct0 : Convertible t p := hct
      exact key E .refl hE hne t ht (hct0.trans hc)
    | one h1 => exact key _ hsub (.one h1) (fun e => by cases e) t ht hct
    | two h1 h2 => exact key _ hsub (.two h1 h2) (fun e => by cases e) t ht hct
  exact thm_L hZ ((subs E).map (fun E' => E'.plug p))
    (fun _ ⟨_, E', hsub, _, hct⟩ => ⟨E'.plug p, List.mem_map.mpr ⟨E', hsub.mem, rfl⟩, hct⟩)
    p ⟨hp, .hole, hE.hole_sub, .hole, Convertible.refl p⟩

end Ncfp
