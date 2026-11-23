import Ski.NcfpN
open Term

/-!
# NCFP: the four two-hole shapes with one closed part

Source: `notes/NCFP-proof.md`, §14.  Setting and notation as in `Ski/Ncfp.lean`.

What is proved:

* `right_combs'` (Theorem 2′): right combs whose teeth are bounded at the non-literal steps only.
  The lemmas `nonlit_exists'`, `run_inner'`, `run'`, `small_desc'` are those of Theorem 2 in
  `Ski/Ncfp.lean` with the weaker hypothesis; `right_combs` is the special case.
* `thm_N3` (Theorem N3) with `claim_D'_frames`, `claim_D'`, `claim_E'`; `no_S_Snp_p`: no closed
  `p` is convertible to `S (S n p) p`, `n` closed and normalizing.  It contains `no_S_SSp_p`.
* `thm_N4` (Theorem N4); `no_S_Spn_p`: no closed `p` is convertible to `S (S p n) p`.
* `thm_N5` (Theorem N5); `no_S_p_Spn`: no closed `p` is convertible to `S p (S p n)`.

With `no_S_p_Snp` (`Ski/NcfpN.lean`) these are the four shapes "`S` with two items, one of them
`p`, the other `S` with `p` and one closed normalizing part".

What is not proved: Lemma (Cons) of the note (cited there, unused); Conj. HN; NCFP.  The note
takes `M ≥ 1`; here Theorem N3 has no such hypothesis and uses the threshold `M + 2` instead.
-/

namespace Ncfp
open HnfS HeadRec Conv

/-! ## Theorem 2′ -/

/-- `Next' B t t'`: the head run of `t` ends in the head normal form `S t'`, or in `S a t'` where
`sz a ≤ B` if the run takes a step (no bound on the tooth of a literal `t = S a t'`). -/
def Next' (B : Nat) (t t' : Term) : Prop :=
  Steps t (S ⬝ t') ∨ ∃ a, (t ≠ S ⬝ a ⬝ t' → sz a ≤ B) ∧ Steps t (S ⬝ a ⬝ t')

theorem Next'.desc {B : Nat} {t t' : Term} (h : Next' B t t') : Desc t t' := by
  rcases h with h1 | ⟨a, _, h2⟩
  · exact ⟨_, h1.weak, .right _ .refl⟩
  · exact ⟨_, h2.weak, .right _ .refl⟩

/-- `P` is a set of closed S-terms each of which has a next term in `P` (`Next'`). -/
def Closed' (B : Nat) (P : Term → Prop) : Prop :=
  ∀ t, P t → PureS t ∧ ∃ t', P t' ∧ Next' B t t'

/-- From every term of the comb one reaches a term whose head run is not literal. -/
theorem nonlit_exists' {B : Nat} {P : Term → Prop} (hC : Closed' B P) :
    ∀ (n : Nat) (t : Term), sz t ≤ n → P t →
      ∃ t₁ y a, P t₁ ∧ (t₁ = t ∨ Desc t t₁) ∧ sz a ≤ B ∧ Steps t₁ (S ⬝ S ⬝ y ⬝ a) ∧
        P (y ⬝ a) := by
  intro n
  induction n with
  | zero =>
    intro t h
    have := sz_pos t
    exfalso
    omega
  | succ n ih =>
    intro t hsz hP
    obtain ⟨ht, t', hP', hN⟩ := hC t hP
    have down : t = S ⬝ t' ∨ (∃ a, t = S ⬝ a ⬝ t') →
        ∃ t₁ y a, P t₁ ∧ (t₁ = t ∨ Desc t t₁) ∧ sz a ≤ B ∧ Steps t₁ (S ⬝ S ⬝ y ⬝ a) ∧
          P (y ⬝ a) := by
      intro hlit
      have hlt : sz t' < sz t := by
        rcases hlit with e | ⟨a, e⟩
        · rw [e]; exact sz_arg_lt _ _
        · rw [e]; exact sz_arg_lt _ _
      obtain ⟨t₁, y, a, h1, h2, h3, h4, h5⟩ := ih t' (by omega) hP'
      refine ⟨t₁, y, a, h1, .inr ?_, h3, h4, h5⟩
      rcases h2 with e | d
      · rw [e]; exact hN.desc
      · exact hN.desc.trans d
    rcases hN with h1 | ⟨a, ha, h2⟩
    · exact down (.inl (hnf1_literal ht h1))
    · rcases Decidable.em (t = S ⬝ a ⬝ t') with e | ne
      · exact down (.inr ⟨a, e⟩)
      · obtain ⟨y, hs, e⟩ := lemma_L' ht h2 ne
        rw [e] at hP'
        exact ⟨t, y, a, hP, .inl rfl, ha ne, hs, hP'⟩

/-- Inside a run of non-literal terms with last item `a`: after `i` further terms, a term of the
comb of leaf count at most `B` has appeared below `t₁`, or the run has produced an SS-chain of
`i` links from `y₀`.  `grow` handles the case that the last item grows. -/
theorem run_inner' {B : Nat} {P : Term → Prop} (hC : Closed' B P) {t₁ y₀ a : Term}
    (ha : sz a ≤ B) (hD₀ : Desc t₁ (y₀ ⬝ a)) (hP₀ : P (y₀ ⬝ a))
    (grow : ∀ t y' a', P t → Desc t₁ t → sz a < sz a' → sz a' ≤ B →
      Steps t (S ⬝ S ⬝ y' ⬝ a') → P (y' ⬝ a') → ∃ t₃, P t₃ ∧ Desc t₁ t₃ ∧ sz t₃ ≤ B) :
    ∀ i : Nat, (∃ t₃, P t₃ ∧ Desc t₁ t₃ ∧ sz t₃ ≤ B) ∨
      ∃ y, SSPath i y₀ y ∧ P (y ⬝ a) ∧ Desc t₁ (y ⬝ a) := by
  intro i
  induction i with
  | zero => exact .inr ⟨y₀, .zero _, hP₀, hD₀⟩
  | succ i ih =>
    rcases ih with ev | ⟨y, path, hPy, hDy⟩
    · exact .inl ev
    · obtain ⟨hpure, t', hP', hN⟩ := hC _ hPy
      have hDt' : Desc t₁ t' := hDy.trans hN.desc
      rcases hN with h1 | ⟨a', ha', h2⟩
      · have e := hnf1_literal hpure h1
        injection e with _ e2
        rw [e2] at ha
        exact .inl ⟨t', hP', hDt', ha⟩
      · rcases Decidable.em (y ⬝ a = S ⬝ a' ⬝ t') with e | ne
        · injection e with _ e2
          rw [e2] at ha
          exact .inl ⟨t', hP', hDt', ha⟩
        · obtain ⟨y', hs, e⟩ := lemma_L' hpure h2 ne
          rw [e] at hP' hDt'
          rcases link hpure hs with ⟨ea, hy⟩ | lt
          · rw [ea] at hP' hDt'
            exact .inr ⟨y', path.snoc hy, hP', hDt'⟩
          · exact .inl (grow (y ⬝ a) y' a' hPy hDy lt (ha' ne) hs hP')

/-- From a term of the comb whose head run is not literal (last frame `S S y a`), a term of the
comb of leaf count at most `B` appears below it.  Induction on `B - sz a`; the inner bound is
`ss_bound`. -/
theorem run' {B : Nat} {P : Term → Prop} (hC : Closed' B P) :
    ∀ (d : Nat) (t₁ y a : Term), B - sz a ≤ d → sz a ≤ B → P t₁ → Steps t₁ (S ⬝ S ⬝ y ⬝ a) →
      P (y ⬝ a) → ∃ t₃, P t₃ ∧ Desc t₁ t₃ ∧ sz t₃ ≤ B := by
  have fin : ∀ (t₁ y a : Term), sz a ≤ B → P t₁ → Steps t₁ (S ⬝ S ⬝ y ⬝ a) → P (y ⬝ a) →
      (∀ t y' a', P t → Desc t₁ t → sz a < sz a' → sz a' ≤ B →
        Steps t (S ⬝ S ⬝ y' ⬝ a') → P (y' ⬝ a') → ∃ t₃, P t₃ ∧ Desc t₁ t₃ ∧ sz t₃ ≤ B) →
      ∃ t₃, P t₃ ∧ Desc t₁ t₃ ∧ sz t₃ ≤ B := by
    intro t₁ y a ha hP₁ hs hPy grow
    have hD₀ : Desc t₁ (y ⬝ a) :=
      ⟨S ⬝ a ⬝ (y ⬝ a), (hs.trans (.single (.S S y a))).weak, .right _ .refl⟩
    have hy : PureS y := (steps_pure (hC t₁ hP₁).1 hs).app_inv.1.app_inv.2
    rcases run_inner' hC ha hD₀ hPy grow (2 * sz y + 1) with ev | ⟨y', path, _, _⟩
    · exact ev
    · have := ss_bound (sz y) y (Nat.le_refl _) hy _ _ path
      exfalso
      omega
  intro d
  induction d with
  | zero =>
    intro t₁ y a hd ha hP₁ hs hPy
    exact fin t₁ y a ha hP₁ hs hPy (fun _ _ a' _ _ lt ha' _ _ => by exfalso; omega)
  | succ d ih =>
    intro t₁ y a hd ha hP₁ hs hPy
    refine fin t₁ y a ha hP₁ hs hPy (fun t y' a' hPt hDt lt ha' hs' hP' => ?_)
    obtain ⟨t₃, h1, h2, h3⟩ := ih t y' a' (by omega) ha' hPt hs' hP'
    exact ⟨t₃, h1, hDt.trans h2, h3⟩

/-- Below every term of the comb there is a term of the comb of leaf count at most `B`. -/
theorem small_desc' {B : Nat} {P : Term → Prop} (hC : Closed' B P) {t : Term} (hP : P t) :
    ∃ t₃, P t₃ ∧ Desc t t₃ ∧ sz t₃ ≤ B := by
  obtain ⟨t₁, y, a, hP₁, hr, ha, hs, hPy⟩ := nonlit_exists' hC (sz t) t (Nat.le_refl _) hP
  obtain ⟨t₃, h1, h2, h3⟩ := run' hC (B - sz a) t₁ y a (Nat.le_refl _) ha hP₁ hs hPy
  rcases hr with e | d
  · rw [e] at h2
    exact ⟨t₃, h1, h2, h3⟩
  · exact ⟨t₃, h1, d.trans h2, h3⟩

/-- **Theorem 2′** (right combs with teeth bounded at non-literal steps), choice-free form.  Let
`P` be a set of closed S-terms such that every `t` in `P` has, on its head run, the head normal
form `S t'` or `S a t'` with `t'` in `P`, and `sz a ≤ B` whenever the run takes a step.  Then `P`
is empty.  Uses `HeadRec.no_ground_loop`. -/
theorem right_combs' {B : Nat} {P : Term → Prop} (hC : Closed' B P) : ∀ t, ¬ P t :=
  desc_finite (fun t hP => (hC t hP).1) (fun _ hP => small_desc' hC hP)

/-! ## Non-normalization -/

/-- A set of closed S-terms each of which has a two-item head normal form with an item in the set
has no normalizing member. -/
theorem not_norm_gen {U : Term → Prop}
    (hU : ∀ v, U v → PureS v ∧ ∃ a b, Steps v (S ⬝ a ⬝ b) ∧ (U a ∨ U b)) :
    ∀ (k : Nat) (v n : Term), sz n ≤ k → U v → WSteps v n → Normal n → False := by
  intro k
  induction k with
  | zero =>
    intro v n h _ _ _
    have := sz_pos n
    omega
  | succ k ih =>
    intro v n hsz hv hvn nf
    obtain ⟨hp, a, b, hs, hab⟩ := hU v hv
    have hH := wsteps_to_normal hs.weak hvn nf
    obtain ⟨a', b', e, haa, hbb⟩ := hnf2_wsteps (steps_pure hp hs) hH
    rw [e] at nf hsz
    have h1 : sz a' < sz (S ⬝ a' ⬝ b') := Nat.lt_trans (sz_arg_lt S a') (sz_fun_lt _ b')
    have h2 : sz b' < sz (S ⬝ a' ⬝ b') := sz_arg_lt _ b'
    rcases hab with h | h
    · exact ih a a' (by omega) h haa nf.app_inv.1.app_inv.2
    · exact ih b b' (by omega) h hbb nf.app_inv.2

theorem not_normalizing {U : Term → Prop}
    (hU : ∀ v, U v → PureS v ∧ ∃ a b, Steps v (S ⬝ a ⬝ b) ∧ (U a ∨ U b)) {v : Term} (hv : U v) :
    ¬ Normalizing v :=
  fun ⟨n, hvn, nf⟩ => not_norm_gen hU (sz n) v n (Nat.le_refl _) hv hvn nf

/-! ## Theorem N5 -/

/-- **Theorem N5.**  Let `A` and `C` be sets of closed S-terms such that every member of `A` has,
on its head run, a two-item head normal form `S a b` with `a ∈ A`, `b ∈ C`, and every member of
`C` has a two-item head normal form `S a' n` with `a' ∈ A` and `n` normalizing of leaf count at
most `M`.  Then `A` is empty.  Uses `HeadRec.no_ground_loop` (through the pigeonhole). -/
theorem thm_N5 {M : Nat} {A C : Term → Prop}
    (hA : ∀ t, A t → PureS t ∧ ∃ a b, Steps t (S ⬝ a ⬝ b) ∧ A a ∧ C b)
    (hC : ∀ t, C t → PureS t ∧ ∃ a n, Steps t (S ⬝ a ⬝ n) ∧ A a ∧ Normalizing n ∧ sz n ≤ M) :
    ∀ t, ¬ A t := by
  have hU : ∀ v, (A v ∨ C v) → PureS v ∧ ∃ a b, Steps v (S ⬝ a ⬝ b) ∧ ((A a ∨ C a) ∨ (A b ∨ C b)) := by
    rintro v (h | h)
    · obtain ⟨hp, a, b, hs, ha, _⟩ := hA v h
      exact ⟨hp, a, b, hs, .inl (.inl ha)⟩
    · obtain ⟨hp, a, n, hs, ha, _, _⟩ := hC v h
      exact ⟨hp, a, n, hs, .inl (.inl ha)⟩
  have notAS : ¬ A S := by
    intro h
    obtain ⟨_, a, b, hs, _, _⟩ := hA S h
    cases steps_S hs
  have small : ∀ (k : Nat) (t : Term), sz t ≤ k → A t → ∃ t₃, A t₃ ∧ Desc t t₃ ∧ sz t₃ ≤ M := by
    intro k
    induction k with
    | zero =>
      intro t h _
      have := sz_pos t
      exfalso
      omega
    | succ k ih =>
      intro t hsz hAt
      obtain ⟨ht, a, b, hs, ha, hb⟩ := hA t hAt
      have hD : Desc t a := ⟨_, hs.weak, .left _ (.right S .refl)⟩
      rcases Decidable.em (t = S ⬝ a ⬝ b) with e | ne
      · have hlt : sz a < sz t := by
          rw [e]
          exact Nat.lt_trans (sz_arg_lt S a) (sz_fun_lt _ b)
        obtain ⟨t₃, h1, h2, h3⟩ := ih a (by omega) ha
        exact ⟨t₃, h1, hD.trans h2, h3⟩
      · obtain ⟨y, _, eb⟩ := lemma_L' ht hs ne
        obtain ⟨hpb, a', n, hsb, _, hn, hnM⟩ := hC b hb
        rw [eb] at hpb hsb
        have haS : a ≠ S := by
          intro e
          rw [e] at ha
          exact notAS ha
        refine ⟨a, ha, hD, ?_⟩
        rcases Decidable.em (y ⬝ a = S ⬝ a' ⬝ n) with e | ne'
        · exfalso
          injection e with _ e2
          rw [← e2] at hn
          exact not_normalizing hU (.inl ha) hn
        · rcases lemma_LL hpb haS (plus_of_steps_ne hsb ne') with ⟨y', _, eR, _⟩ |
            ⟨p, q, _, _, eR, hw⟩
          · have h1 := sz_arg_lt y' a
            rw [← eR] at h1
            omega
          · have h1 := hw.sz_le
            have h2 := sz_arg_lt q (p ⬝ q)
            have h3 := sz_arg_lt p q
            rw [← eR] at h2
            have e : sz (q ⬝ (p ⬝ q)) = sz q + sz (p ⬝ q) := rfl
            have := sz_pos (p ⬝ q)
            have h4 := sz_fun_lt q (p ⬝ q)
            rw [← eR] at h4
            omega
  exact desc_finite (fun t h => (hA t h).1) (fun t h => small (sz t) t (Nat.le_refl _) h)

/-- Conversion to `S a n` with `n` closed and normalizing: the head normal form has a second item
that normalizes, of leaf count at most that of the normal form of `n`. -/
theorem hnf2_conv_right {t a n nf : Term} (ht : PureS t) (ha : PureS a) (hn : PureS n)
    (hnnf : WSteps n nf) (hnf : Normal nf) (h : Convertible t (S ⬝ a ⬝ n)) :
    ∃ a' m, Steps t (S ⬝ a' ⬝ m) ∧ PureS a' ∧ Convertible a' a ∧ Normalizing m ∧ sz m ≤ sz nf := by
  obtain ⟨a', m, hs, ca, cm⟩ := hnf2_conv ht ha hn h
  have hpab := steps_pure ht hs
  obtain ⟨c, h1, h2⟩ := conv_iff_join.mp cm
  have hmnf : WSteps m nf := h1.trans (wsteps_to_normal h2 hnnf hnf)
  exact ⟨a', m, hs, hpab.app_inv.1.app_inv.2, ca, ⟨nf, hmnf, hnf⟩, sz_wsteps hpab.app_inv.2 hmnf⟩

/-- Conversion to `S n a` with `n` closed and normalizing: the head normal form has a first item
that normalizes, of leaf count at most that of the normal form of `n`. -/
theorem hnf2_conv_left {t a n nf : Term} (ht : PureS t) (ha : PureS a) (hn : PureS n)
    (hnnf : WSteps n nf) (hnf : Normal nf) (h : Convertible t (S ⬝ n ⬝ a)) :
    ∃ m a', Steps t (S ⬝ m ⬝ a') ∧ PureS a' ∧ Convertible a' a ∧ Normalizing m ∧ sz m ≤ sz nf := by
  obtain ⟨m, a', hs, cm, ca⟩ := hnf2_conv ht hn ha h
  have hpab := steps_pure ht hs
  obtain ⟨c, h1, h2⟩ := conv_iff_join.mp cm
  have hmnf : WSteps m nf := h1.trans (wsteps_to_normal h2 hnnf hnf)
  exact ⟨m, a', hs, hpab.app_inv.2, ca, ⟨nf, hmnf, hnf⟩,
    sz_wsteps hpab.app_inv.1.app_inv.2 hmnf⟩

/-- No closed S-term `p` is convertible to `S p (S p n)`, for every closed normalizing `n`. -/
theorem no_S_p_Spn {p n : Term} (hp : PureS p) (hn : PureS n) (hnn : Normalizing n) :
    ¬ Convertible p (S ⬝ p ⬝ (S ⬝ p ⬝ n)) := by
  intro hc
  obtain ⟨nf, hnnf, hnf⟩ := hnn
  have hA : ∀ t, (PureS t ∧ Convertible t p) → PureS t ∧ ∃ a b, Steps t (S ⬝ a ⬝ b) ∧
      (PureS a ∧ Convertible a p) ∧ (PureS b ∧ Convertible b (S ⬝ p ⬝ n)) := by
    rintro t ⟨ht, hct⟩
    obtain ⟨a, b, hs, ca, cb⟩ := hnf2_conv ht hp (.app (.app .S hp) hn) (hct.trans hc)
    have hpab := steps_pure ht hs
    exact ⟨ht, a, b, hs, ⟨hpab.app_inv.1.app_inv.2, ca⟩, ⟨hpab.app_inv.2, cb⟩⟩
  have hC : ∀ t, (PureS t ∧ Convertible t (S ⬝ p ⬝ n)) → PureS t ∧ ∃ a m, Steps t (S ⬝ a ⬝ m) ∧
      (PureS a ∧ Convertible a p) ∧ Normalizing m ∧ sz m ≤ sz nf := by
    rintro t ⟨ht, hct⟩
    obtain ⟨a, m, hs, hpa, ca, hm, hsz⟩ := hnf2_conv_right ht hp hn hnnf hnf hct
    exact ⟨ht, a, m, hs, ⟨hpa, ca⟩, hm, hsz⟩
  exact thm_N5 (M := sz nf) (A := fun t => PureS t ∧ Convertible t p)
    (C := fun t => PureS t ∧ Convertible t (S ⬝ p ⬝ n)) hA hC p ⟨hp, Convertible.refl p⟩

/-! ## Theorem N4 -/

/-- **Theorem N4.**  Let `A` and `C` be sets of closed S-terms such that every member of `A` has,
on its head run, a two-item head normal form `S a b` with `a ∈ C`, `b ∈ A`, and every member of
`C` has a two-item head normal form `S a' n` with `a' ∈ A` and `n` normalizing of leaf count at
most `M`.  Then `A` is empty.  Uses Theorem 2′ (`right_combs'`). -/
theorem thm_N4 {M : Nat} {A C : Term → Prop}
    (hA : ∀ t, A t → PureS t ∧ ∃ a b, Steps t (S ⬝ a ⬝ b) ∧ C a ∧ A b)
    (hC : ∀ t, C t → PureS t ∧ ∃ a n, Steps t (S ⬝ a ⬝ n) ∧ A a ∧ Normalizing n ∧ sz n ≤ M) :
    ∀ t, ¬ A t := by
  have hU : ∀ v, (A v ∨ C v) → PureS v ∧ ∃ a b, Steps v (S ⬝ a ⬝ b) ∧ ((A a ∨ C a) ∨ (A b ∨ C b)) := by
    rintro v (h | h)
    · obtain ⟨hp, a, b, hs, _, hb⟩ := hA v h
      exact ⟨hp, a, b, hs, .inr (.inl hb)⟩
    · obtain ⟨hp, a, n, hs, ha, _, _⟩ := hC v h
      exact ⟨hp, a, n, hs, .inl (.inl ha)⟩
  have disj : ∀ t, A t → C t → False := by
    intro t h1 h2
    obtain ⟨_, a, b, hs, _, hb⟩ := hA t h1
    obtain ⟨_, a', n, hs', _, hn, _⟩ := hC t h2
    have e := run_hnf_hnf (.inr (.inr ⟨a, b, rfl⟩)) (.inr (.inr ⟨a', n, rfl⟩)) hs hs'
    injection e with _ e2
    rw [← e2] at hn
    exact not_normalizing hU (.inl hb) hn
  have notCS : ¬ C S := by
    intro h
    obtain ⟨_, a, n, hs, _, _, _⟩ := hC S h
    cases steps_S hs
  -- no member of `A` has a last item in `C` of leaf count above `M`
  have claim : ∀ (k : Nat) (y z : Term), sz y ≤ k → C z → M < sz z → A (y ⬝ z) → False := by
    intro k
    induction k with
    | zero =>
      intro y z h _ _ _
      have := sz_pos y
      omega
    | succ k ih =>
      intro y z hsz hz hbig hyz
      obtain ⟨hp, rL, rR, hs, hCL, hAR⟩ := hA _ hyz
      have hzS : z ≠ S := by
        intro e
        rw [e] at hz
        exact notCS hz
      rcases Decidable.em (y ⬝ z = S ⬝ rL ⬝ rR) with e | ne
      · injection e with _ e2
        rw [← e2] at hAR
        exact disj z hAR hz
      · rcases lemma_LL hp hzS (plus_of_steps_ne hs ne) with ⟨y', _, eR, hsy⟩ |
          ⟨p, q, _, eL, _, hw⟩
        · have h1 := lemma_SS_sz hp.app_inv.1 hsy
          rw [eR] at hAR
          exact ih y' z (by omega) hz hbig hAR
        · have hqz := hw.sz_le
          have hqS : q ≠ S := by
            intro e
            rw [e] at hw
            exact hzS (wrap_S hw)
          rw [eL] at hCL
          obtain ⟨hppq, a'', n, hs2, _, _, hnM⟩ := hC _ hCL
          rcases Decidable.em (p ⬝ q = S ⬝ a'' ⬝ n) with e | ne'
          · injection e with _ e2
            rw [e2] at hqz
            omega
          · rcases lemma_LL hppq hqS (plus_of_steps_ne hs2 ne') with ⟨y'', _, eR', _⟩ |
              ⟨p', q', _, _, eR', hw'⟩
            · have h1 := sz_arg_lt y'' q
              rw [← eR'] at h1
              omega
            · have h1 := hw'.sz_le
              have h2 := sz_fun_lt q' (p' ⬝ q')
              rw [← eR'] at h2
              omega
  have hCl : Closed' M A := by
    intro t hAt
    obtain ⟨ht, a, b, hs, ha, hb⟩ := hA t hAt
    refine ⟨ht, b, hb, .inr ⟨a, fun ne => ?_, hs⟩⟩
    obtain ⟨y, _, eb⟩ := lemma_L' ht hs ne
    rw [eb] at hb
    rcases Nat.lt_or_ge M (sz a) with h | h
    · exact (claim (sz y) y a (Nat.le_refl _) ha h hb).elim
    · exact h
  exact right_combs' hCl

/-- No closed S-term `p` is convertible to `S (S p n) p`, for every closed normalizing `n`. -/
theorem no_S_Spn_p {p n : Term} (hp : PureS p) (hn : PureS n) (hnn : Normalizing n) :
    ¬ Convertible p (S ⬝ (S ⬝ p ⬝ n) ⬝ p) := by
  intro hc
  obtain ⟨nf, hnnf, hnf⟩ := hnn
  have hA : ∀ t, (PureS t ∧ Convertible t p) → PureS t ∧ ∃ a b, Steps t (S ⬝ a ⬝ b) ∧
      (PureS a ∧ Convertible a (S ⬝ p ⬝ n)) ∧ (PureS b ∧ Convertible b p) := by
    rintro t ⟨ht, hct⟩
    obtain ⟨a, b, hs, ca, cb⟩ := hnf2_conv ht (.app (.app .S hp) hn) hp (hct.trans hc)
    have hpab := steps_pure ht hs
    exact ⟨ht, a, b, hs, ⟨hpab.app_inv.1.app_inv.2, ca⟩, ⟨hpab.app_inv.2, cb⟩⟩
  have hC : ∀ t, (PureS t ∧ Convertible t (S ⬝ p ⬝ n)) → PureS t ∧ ∃ a m, Steps t (S ⬝ a ⬝ m) ∧
      (PureS a ∧ Convertible a p) ∧ Normalizing m ∧ sz m ≤ sz nf := by
    rintro t ⟨ht, hct⟩
    obtain ⟨a, m, hs, hpa, ca, hm, hsz⟩ := hnf2_conv_right ht hp hn hnnf hnf hct
    exact ⟨ht, a, m, hs, ⟨hpa, ca⟩, hm, hsz⟩
  exact thm_N4 (M := sz nf) (A := fun t => PureS t ∧ Convertible t p)
    (C := fun t => PureS t ∧ Convertible t (S ⬝ p ⬝ n)) hA hC p ⟨hp, Convertible.refl p⟩

/-! ## Theorem N3 -/

/-- The frame bookkeeping of Claim D′.  Let a head run start at `f m gm` (the frame after a
three-item frame `S f g m`, with `gm = g m`), with `m` and `gm` of leaf count above `M + 2`, and
reach a three-item frame `S (S S) p q`.  Then `sz p > M + 2`: at each three-item frame on the way
the last item is large, and at the last one Corollary LL1 gives `p = m'` for its large last-but-one
item. -/
theorem claim_D'_frames {M : Nat} : ∀ (n k : Nat) (f m gm p q : Term), k ≤ n →
    PureS (f ⬝ m ⬝ gm) → M + 2 < sz m → M + 2 < sz gm →
    StepsK k (f ⬝ m ⬝ gm) (S ⬝ (S ⬝ S) ⬝ p ⬝ q) → M + 2 < sz p := by
  have body : ∀ (k : Nat) (f m gm p q : Term), PureS (f ⬝ m ⬝ gm) → M + 2 < sz m →
      M + 2 < sz gm → StepsK k (f ⬝ m ⬝ gm) (S ⬝ (S ⬝ S) ⬝ p ⬝ q) →
      M + 2 < sz p ∨ ∃ k' f' g', k' < k ∧ PureS (f' ⬝ gm ⬝ (g' ⬝ gm)) ∧
        StepsK k' (f' ⬝ gm ⬝ (g' ⬝ gm)) (S ⬝ (S ⬝ S) ⬝ p ⬝ q) := by
    intro k f m gm p q hp hm hgm hrun
    have e1S : sz S = 1 := rfl
    rcases split (stepsK_steps hrun) rfl hp with ⟨e', he, hs'⟩ | ⟨f', g', h1, h2⟩
    · injection he with e1 _
      rw [← e1] at hs'
      have hmS : m ≠ S := by
        intro e
        rw [e] at hm
        omega
      have e2 : sz (S ⬝ S) = 2 := rfl
      obtain ⟨_, e⟩ := cor_LL1 hp.app_inv.1 hmS hs' (by omega)
      rw [e]
      exact .inl hm
    · have hplus : Plus (f ⬝ m ⬝ gm) (f' ⬝ gm ⬝ (g' ⬝ gm)) :=
        steps_step_plus (Steps.left gm h1) (.S f' g' gm)
      obtain ⟨k', hlt, hk'⟩ := stepsK_plus hp hrun hplus h2
      exact .inr ⟨k', f', g', hlt, steps_pure hp hplus.steps, hk'⟩
  intro n
  induction n with
  | zero =>
    intro k f m gm p q hk hp hm hgm hrun
    rcases body k f m gm p q hp hm hgm hrun with h | ⟨k', _, _, hlt, _, _⟩
    · exact h
    · exfalso
      omega
  | succ n ih =>
    intro k f m gm p q hk hp hm hgm hrun
    rcases body k f m gm p q hp hm hgm hrun with h | ⟨k', f', g', hlt, hp', hk'⟩
    · exact h
    · have h1 := sz_arg_lt g' gm
      exact ih k' f' gm (g' ⬝ gm) p q (by omega) hp' hgm (by omega) hk'

/-- **Theorem N3.**  Let `A` and `B` be sets of closed S-terms such that every member of `A` has,
on its head run, a two-item head normal form `S a b` with `a ∈ B`, `b ∈ A`, and every member of
`B` has a two-item head normal form `S n a'` with `n` normalizing of leaf count at most `M` and
`a' ∈ A`.  Then `A` is empty.  Uses Theorem 2′ (`right_combs'`), with Claims D′ and E′ proved
inside. -/
theorem thm_N3 {M : Nat} {A B : Term → Prop}
    (hA : ∀ t, A t → PureS t ∧ ∃ a b, Steps t (S ⬝ a ⬝ b) ∧ B a ∧ A b)
    (hB : ∀ t, B t → PureS t ∧ ∃ n a, Steps t (S ⬝ n ⬝ a) ∧ Normalizing n ∧ sz n ≤ M ∧ A a) :
    ∀ t, ¬ A t := by
  have hU : ∀ v, (A v ∨ B v) → PureS v ∧ ∃ a b, Steps v (S ⬝ a ⬝ b) ∧ ((A a ∨ B a) ∨ (A b ∨ B b)) := by
    rintro v (h | h)
    · obtain ⟨hp, a, b, hs, _, hb⟩ := hA v h
      exact ⟨hp, a, b, hs, .inr (.inl hb)⟩
    · obtain ⟨hp, n, a, hs, _, _, ha⟩ := hB v h
      exact ⟨hp, n, a, hs, .inr (.inl ha)⟩
  have notBnorm : ∀ v, B v → Normalizing v → False :=
    fun v h hn => not_normalizing hU (.inr h) hn
  have disj : ∀ t, A t → B t → False := by
    intro t h1 h2
    obtain ⟨_, a, b, hs, ha, _⟩ := hA t h1
    obtain ⟨_, n, a', hs', hn, _, _⟩ := hB t h2
    have e := run_hnf_hnf (.inr (.inr ⟨a, b, rfl⟩)) (.inr (.inr ⟨n, a', rfl⟩)) hs hs'
    injection e with e1 _
    injection e1 with _ e2
    rw [← e2] at hn
    exact notBnorm a ha hn
  have notBS : ¬ B S := fun h => notBnorm S h ⟨S, .refl _, normal_S⟩
  have notBSS : ¬ B (S ⬝ S) := fun h => notBnorm _ h (normalizing_S1 ⟨S, .refl _, normal_S⟩)
  -- Claim D′
  have claimD : ∀ a β, A a → B β → M + 2 < sz β → A (a ⬝ β) → False := by
    intro a β ha hβ hbig hX
    obtain ⟨hp, xL, xR, hs, hBL, hAR⟩ := hA _ hX
    have hβS : β ≠ S := by
      intro e
      rw [e] at hβ
      exact notBS hβ
    obtain ⟨hpa, b₁, aR, hsa, hb₁, _⟩ := hA a ha
    rcases Decidable.em (a ⬝ β = S ⬝ xL ⬝ xR) with e | ne
    · injection e with _ e2
      rw [← e2] at hAR
      exact disj β hAR hβ
    · rcases lemma_LL hp hβS (plus_of_steps_ne hs ne) with ⟨y', _, _, hsa'⟩ |
        ⟨p, q, hfr, eL, _, hw⟩
      · have e := run_hnf_hnf (.inr (.inr ⟨b₁, aR, rfl⟩)) (.inr (.inr ⟨S, y', rfl⟩)) hsa hsa'
        injection e with e1 _
        injection e1 with _ e2
        rw [e2] at hb₁
        exact notBS hb₁
      · have hqβ := hw.sz_le
        have hqS : q ≠ S := by
          intro e
          rw [e] at hw
          exact hβS (wrap_S hw)
        rw [eL] at hBL
        obtain ⟨hppq, n, a'', hs2, _, hnM, _⟩ := hB _ hBL
        obtain ⟨ep, _⟩ := cor_LL1 hppq hqS hs2 (by omega)
        have hpsz : sz p ≤ M + 1 := by
          rw [ep]
          have e : sz (S ⬝ n) = 1 + sz n := rfl
          omega
        rcases split hfr rfl hp with ⟨e', he, hsa'⟩ | ⟨f, g, h1, h2⟩
        · injection he with e1 _
          rw [← e1] at hsa'
          have e := run_hnf_hnf (.inr (.inr ⟨b₁, aR, rfl⟩)) (.inr (.inr ⟨S ⬝ S, p, rfl⟩)) hsa hsa'
          injection e with e1 _
          injection e1 with _ e2
          rw [e2] at hb₁
          exact notBSS hb₁
        · have hfg := steps_pure hpa h1
          have hpβ := hp.app_inv.2
          have hpF : PureS (f ⬝ β ⬝ (g ⬝ β)) :=
            .app (.app hfg.app_inv.1.app_inv.2 hpβ) (.app hfg.app_inv.2 hpβ)
          obtain ⟨k, hk⟩ := stepsK_of_steps h2
          have h3 := sz_arg_lt g β
          have := claim_D'_frames (M := M) k k f β (g ⬝ β) p q (Nat.le_refl _) hpF hbig (by omega) hk
          omega
  -- Claim E′
  have claimE : ∀ (k : Nat) (y z : Term), sz y ≤ k → B z → M + 2 < sz z → A (y ⬝ z) → False := by
    intro k
    induction k with
    | zero =>
      intro y z h _ _ _
      have := sz_pos y
      omega
    | succ k ih =>
      intro y z hsz hz hbig hyz
      obtain ⟨hp, rL, rR, hs, hBL, hAR⟩ := hA _ hyz
      have hzS : z ≠ S := by
        intro e
        rw [e] at hz
        exact notBS hz
      rcases Decidable.em (y ⬝ z = S ⬝ rL ⬝ rR) with e | ne
      · injection e with _ e2
        rw [← e2] at hAR
        exact disj z hAR hz
      · rcases lemma_LL hp hzS (plus_of_steps_ne hs ne) with ⟨y', _, eR, hsy⟩ |
          ⟨p, q, _, eL, eR, hw⟩
        · have h1 := lemma_SS_sz hp.app_inv.1 hsy
          rw [eR] at hAR
          exact ih y' z (by omega) hz hbig hAR
        · have hqz := hw.sz_le
          have hqS : q ≠ S := by
            intro e
            rw [e] at hw
            exact hzS (wrap_S hw)
          rw [eL] at hBL
          obtain ⟨hppq, n, a'', hs2, _, hnM, ha''⟩ := hB _ hBL
          obtain ⟨_, ea⟩ := cor_LL1 hppq hqS hs2 (by omega)
          rw [ea] at ha''
          rw [eR] at hAR
          have h1 := sz_arg_lt p q
          exact claimD q (p ⬝ q) ha'' hBL (by omega) hAR
  have hCl : Closed' (M + 2) A := by
    intro t hAt
    obtain ⟨ht, a, b, hs, ha, hb⟩ := hA t hAt
    refine ⟨ht, b, hb, .inr ⟨a, fun ne => ?_, hs⟩⟩
    obtain ⟨y, _, eb⟩ := lemma_L' ht hs ne
    rw [eb] at hb
    rcases Nat.lt_or_ge (M + 2) (sz a) with h | h
    · exact (claimE (sz y) y a (Nat.le_refl _) ha h hb).elim
    · exact h
  exact right_combs' hCl

/-- No closed S-term `p` is convertible to `S (S n p) p`, for every closed normalizing `n`. -/
theorem no_S_Snp_p {p n : Term} (hp : PureS p) (hn : PureS n) (hnn : Normalizing n) :
    ¬ Convertible p (S ⬝ (S ⬝ n ⬝ p) ⬝ p) := by
  intro hc
  obtain ⟨nf, hnnf, hnf⟩ := hnn
  have hA : ∀ t, (PureS t ∧ Convertible t p) → PureS t ∧ ∃ a b, Steps t (S ⬝ a ⬝ b) ∧
      (PureS a ∧ Convertible a (S ⬝ n ⬝ p)) ∧ (PureS b ∧ Convertible b p) := by
    rintro t ⟨ht, hct⟩
    obtain ⟨a, b, hs, ca, cb⟩ := hnf2_conv ht (.app (.app .S hn) hp) hp (hct.trans hc)
    have hpab := steps_pure ht hs
    exact ⟨ht, a, b, hs, ⟨hpab.app_inv.1.app_inv.2, ca⟩, ⟨hpab.app_inv.2, cb⟩⟩
  have hB : ∀ t, (PureS t ∧ Convertible t (S ⬝ n ⬝ p)) → PureS t ∧ ∃ m a, Steps t (S ⬝ m ⬝ a) ∧
      Normalizing m ∧ sz m ≤ sz nf ∧ (PureS a ∧ Convertible a p) := by
    rintro t ⟨ht, hct⟩
    obtain ⟨m, a, hs, hpa, ca, hm, hsz⟩ := hnf2_conv_left ht hp hn hnnf hnf hct
    exact ⟨ht, m, a, hs, hm, hsz, hpa, ca⟩
  exact thm_N3 (M := sz nf) (A := fun t => PureS t ∧ Convertible t p)
    (B := fun t => PureS t ∧ Convertible t (S ⬝ n ⬝ p)) hA hB p ⟨hp, Convertible.refl p⟩

end Ncfp
