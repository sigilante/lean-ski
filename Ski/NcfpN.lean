import Ski.NcfpLeafless
open Term

/-!
# NCFP: two holes with a closed part, first cases

Source: `notes/NCFP-proof.md`, §13.  Setting and notation as in `Ski/Ncfp.lean`.

What is proved:

* `lemma_LL` (Lemma LL: what a last item other than `S` forces) and `cor_LL1` (Corollary LL1).
* `progress_bot`: a set of closed S-terms each of which head-reduces in one or more steps to a
  member is a set of hnf-less terms.
* `thm_N1` (Theorem N1) with `claim_D` (the uniform head-run cycle) and `claim_E`; `no_S_SSp_p`:
  no closed `p` is convertible to `S (S S p) p`.
* `thm_N2` (Theorem N2); `no_S_p_Snp`: no closed `p` is convertible to `S p (S n p)` for a closed
  normalizing `n`.

What is not proved: `p =β S (S n p) p` for `n ≠ S` and the other shapes of §14; Conj. HN; NCFP.

Constructivity: sets are predicates, "least member" is induction on the leaf count, and the
"eventually" steps of Theorem N2 are a downward induction on the size of the last item together
with `finite_descent_nn` (the pigeonhole under a double negation).  No axiom beyond `propext` and
`Quot.sound`.
-/

namespace Ncfp
open HnfS HeadRec Conv

/-! ## Lemma LL, Corollary LL1 -/

theorem wrap_S {u : Term} (h : Wrap u S) : u = S := by
  cases h with
  | refl => rfl

/-- **Lemma LL** (last item).  Let the head run of the closed S-term `v⁻ u` take one or more steps
to the two-item head normal form `S hL hR`, and let the last item `u` be other than `S`.  Then
(A) `hL = u`, `hR = y' u` and `v⁻ ↠h S S y'`, or
(B) the run passes through `S (S S) p q`, `hL = p q`, `hR = q (p q)`, and `q` is a wrapping
`dₙ (⋯ (d₁ u))` of `u`.
(Exclusivity of the two cases is not stated.) -/
theorem lemma_LL {vm u hL hR : Term} (hp : PureS (vm ⬝ u)) (hu : u ≠ S)
    (h : Plus (vm ⬝ u) (S ⬝ hL ⬝ hR)) :
    (∃ y', hL = u ∧ hR = y' ⬝ u ∧ Steps vm (S ⬝ S ⬝ y')) ∨
    (∃ p q, Steps (vm ⬝ u) (S ⬝ (S ⬝ S) ⬝ p ⬝ q) ∧ hL = p ⬝ q ∧ hR = q ⬝ (p ⬝ q) ∧ Wrap u q) := by
  obtain ⟨y, eR, _, hcase⟩ := lemma_TD hp h
  rcases hcase with ⟨tm, e, hs⟩ | ⟨x, p, q, hfr, _, eL, hφ⟩
  · injection e with e1 e2
    rw [← e1] at hs
    exact .inl ⟨y, e2.symm, by rw [eR, e2], hs⟩
  · obtain ⟨hw, _⟩ := fact_LI hp hfr
    have hpfr := steps_pure hp hfr
    have hpxq : PureS (x ⬝ q) := .app hpfr.app_inv.1.app_inv.1.app_inv.2 hpfr.app_inv.2
    obtain ⟨c, k, e1, e2⟩ := lemma_SS (sz (x ⬝ q)) (x ⬝ q) y (Nat.le_refl _) hpxq hφ
    cases k with
    | zero =>
      have e1' : x ⬝ q = S ⬝ S ⬝ c := e1
      have e2' : y = c := e2
      injection e1' with e3 e4
      rw [e3] at hfr
      have ey : y = q := e2'.trans e4.symm
      exact .inr ⟨p, q, hfr, eL, by rw [eR, eL, ey], hw⟩
    | succ k =>
      have e1' : x ⬝ q = appS k (S ⬝ S ⬝ c) ⬝ S := e1
      injection e1' with _ e4
      rw [e4] at hw
      exact absurd (wrap_S hw) hu

/-- **Corollary LL1.**  If the closed S-term `w z` has, on its head run, a two-item head normal
form `S a b` with `a` smaller than `z`, and `z ≠ S`, then `w z` is literal: `w = S a` and
`b = z`. -/
theorem cor_LL1 {w z a b : Term} (hp : PureS (w ⬝ z)) (hz : z ≠ S)
    (hs : Steps (w ⬝ z) (S ⬝ a ⬝ b)) (hlt : sz a < sz z) : w = S ⬝ a ∧ b = z := by
  rcases Decidable.em (w ⬝ z = S ⬝ a ⬝ b) with e | ne
  · injection e with e1 e2
    exact ⟨e1, e2.symm⟩
  · exfalso
    rcases lemma_LL hp hz (plus_of_steps_ne hs ne) with ⟨y', e, _, _⟩ | ⟨p, q, _, e, _, hw⟩
    · rw [e] at hlt
      exact Nat.lt_irrefl _ hlt
    · have h1 := hw.sz_le
      have h2 := sz_arg_lt p q
      rw [← e] at h2
      omega

/-! ## Divergence by progress -/

/-- A set of closed S-terms each of which head-reduces in one or more steps to a member consists
of hnf-less terms (the head run of a member is infinite). -/
theorem progress_bot {W : Term → Prop} (hpure : ∀ X, W X → PureS X)
    (hstep : ∀ X, W X → ∃ X', W X' ∧ Plus X X') : ∀ X, W X → fold X = 36 := by
  have next : ∀ (k : Nat) (X H : Term), W X → StepsK k X H → IsHnf H →
      ∃ k' X', k' < k ∧ W X' ∧ StepsK k' X' H := by
    intro k X H hW hrun hH
    obtain ⟨X', hW', hplus⟩ := hstep X hW
    have hX'H : Steps X' H := by
      rcases InfNF.steps_cmp hplus.steps (stepsK_steps hrun) with h | h
      · exact h
      · rw [InfNF.steps_from_hnf hH h]
        exact .refl _
    obtain ⟨k', hlt, hk'⟩ := stepsK_plus (hpure X hW) hrun hplus hX'H
    exact ⟨k', X', hlt, hW', hk'⟩
  have none : ∀ (n k : Nat) (X H : Term), k ≤ n → W X → StepsK k X H → IsHnf H → False := by
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
  intro X hW
  have hp := hpure X hW
  rcases Nat.decEq (fold X) 36 with hne | heq
  · exfalso
    obtain ⟨T, hs, hT⟩ := reach_frame hp
    rcases hT with hh | ⟨f, w, e, hf⟩
    · obtain ⟨k, hk⟩ := stepsK_of_steps hs
      exact none k k X T (Nat.le_refl _) hW hk hh
    · rw [e] at hs
      exact hne ((InfNF.steps_fold hp hs).symm.trans
        (Full.fold_frame (steps_pure hp hs).app_inv.2 hf))
  · exact heq

/-! ## Theorem N1 -/

/-- **Claim D** of Theorem N1 (the uniform head-run cycle).  Let every member of `A` have a
two-item head normal form `S b₁ a_R` with `b₁ ∈ B`, `a_R ∈ A`, and every member of `B` the head
normal form `S S a'` with `a' ∈ A`.  Then for `a ∈ A`, `z ∈ B` and closed `w⃗`, the term `a z w⃗`
is hnf-less: it head-reduces in one or more steps to `a_R z u₂ (a' u₁ u₂) w⃗`, of the same
form. -/
theorem claim_D {A B : Term → Prop}
    (hA : ∀ t, A t → PureS t ∧ ∃ a b, Steps t (S ⬝ a ⬝ b) ∧ B a ∧ A b)
    (hB : ∀ t, B t → PureS t ∧ ∃ a, Steps t (S ⬝ S ⬝ a) ∧ A a)
    {a z : Term} (ha : A a) (hz : B z) (L : List Term) (hL : ∀ x ∈ L, PureS x) :
    fold (apps (a ⬝ z) L) = 36 := by
  refine progress_bot
    (W := fun X => ∃ a z L, A a ∧ B z ∧ (∀ x ∈ L, PureS x) ∧ X = apps (a ⬝ z) L) ?_ ?_ _
    ⟨a, z, L, ha, hz, hL, rfl⟩
  · rintro X ⟨a, z, L, ha, hz, hL, e⟩
    rw [e]
    exact pure_apps_of (.app (hA a ha).1 (hB z hz).1) L hL
  · rintro X ⟨a, z, L, ha, hz, hL, e⟩
    rw [e]
    obtain ⟨hpa, b₁, aR, hsa, hb₁, haR⟩ := hA a ha
    obtain ⟨hpb, a₁, hsb, _⟩ := hB b₁ hb₁
    obtain ⟨hpz, a', hsz, _⟩ := hB z hz
    have hpaR := (steps_pure hpa hsa).app_inv.2
    have hpa₁ := (steps_pure hpb hsb).app_inv.2
    have hpa' := (steps_pure hpz hsz).app_inv.2
    have hu₁ : PureS (aR ⬝ z) := .app hpaR hpz
    have hu₂ : PureS (a₁ ⬝ z ⬝ (aR ⬝ z)) := .app (.app hpa₁ hpz) hu₁
    have s1 : Steps (apps (a ⬝ z) L) (apps (S ⬝ b₁ ⬝ aR ⬝ z) L) :=
      steps_apps L (Steps.left z hsa)
    have s2 : Step (apps (S ⬝ b₁ ⬝ aR ⬝ z) L) (apps (b₁ ⬝ z ⬝ (aR ⬝ z)) L) :=
      step_apps L (.S b₁ aR z)
    have s3 : Steps (apps (b₁ ⬝ z ⬝ (aR ⬝ z)) L) (apps (S ⬝ S ⬝ a₁ ⬝ z ⬝ (aR ⬝ z)) L) :=
      steps_apps L (Steps.left (aR ⬝ z) (Steps.left z hsb))
    have s4 : Step (apps (S ⬝ S ⬝ a₁ ⬝ z ⬝ (aR ⬝ z)) L)
        (apps (S ⬝ z ⬝ (a₁ ⬝ z) ⬝ (aR ⬝ z)) L) :=
      step_apps L (Step.left (aR ⬝ z) (.S S a₁ z))
    have s5 : Step (apps (S ⬝ z ⬝ (a₁ ⬝ z) ⬝ (aR ⬝ z)) L)
        (apps (z ⬝ (aR ⬝ z) ⬝ (a₁ ⬝ z ⬝ (aR ⬝ z))) L) :=
      step_apps L (.S z (a₁ ⬝ z) (aR ⬝ z))
    have s6 : Steps (apps (z ⬝ (aR ⬝ z) ⬝ (a₁ ⬝ z ⬝ (aR ⬝ z))) L)
        (apps (S ⬝ S ⬝ a' ⬝ (aR ⬝ z) ⬝ (a₁ ⬝ z ⬝ (aR ⬝ z))) L) :=
      steps_apps L (Steps.left _ (Steps.left _ hsz))
    have s7 : Step (apps (S ⬝ S ⬝ a' ⬝ (aR ⬝ z) ⬝ (a₁ ⬝ z ⬝ (aR ⬝ z))) L)
        (apps (S ⬝ (aR ⬝ z) ⬝ (a' ⬝ (aR ⬝ z)) ⬝ (a₁ ⬝ z ⬝ (aR ⬝ z))) L) :=
      step_apps L (Step.left _ (.S S a' (aR ⬝ z)))
    have s8 : Step (apps (S ⬝ (aR ⬝ z) ⬝ (a' ⬝ (aR ⬝ z)) ⬝ (a₁ ⬝ z ⬝ (aR ⬝ z))) L)
        (apps (aR ⬝ z ⬝ (a₁ ⬝ z ⬝ (aR ⬝ z)) ⬝ (a' ⬝ (aR ⬝ z) ⬝ (a₁ ⬝ z ⬝ (aR ⬝ z)))) L) :=
      step_apps L (.S (aR ⬝ z) (a' ⬝ (aR ⬝ z)) (a₁ ⬝ z ⬝ (aR ⬝ z)))
    have hplus := steps_step_plus
      (s1.trans (.step s2 (s3.trans (.step s4 (.step s5 (s6.trans (.single s7))))))) s8
    refine ⟨_, ⟨aR, z, (a₁ ⬝ z ⬝ (aR ⬝ z)) :: (a' ⬝ (aR ⬝ z) ⬝ (a₁ ⬝ z ⬝ (aR ⬝ z))) :: L,
      haR, hz, ?_, rfl⟩, hplus⟩
    intro x hx
    rcases List.mem_cons.mp hx with e1 | hx'
    · rw [e1]; exact hu₂
    · rcases List.mem_cons.mp hx' with e2 | hx''
      · rw [e2]; exact .app (.app hpa' hu₁) hu₂
      · exact hL x hx''

/-- **Claim E** of Theorem N1: no member of `A` has a member of `B` as its last item. -/
theorem claim_E {A B : Term → Prop}
    (hA : ∀ t, A t → PureS t ∧ ∃ a b, Steps t (S ⬝ a ⬝ b) ∧ B a ∧ A b)
    (hB : ∀ t, B t → PureS t ∧ ∃ a, Steps t (S ⬝ S ⬝ a) ∧ A a) :
    ∀ (n : Nat) (y z : Term), sz y ≤ n → B z → A (y ⬝ z) → False := by
  have notBS : ¬ B S := by
    intro h
    obtain ⟨_, a, hs, _⟩ := hB S h
    cases steps_S hs
  have disj : ∀ t, A t → B t → False := by
    intro t h1 h2
    obtain ⟨_, a, b, hs, ha, _⟩ := hA t h1
    obtain ⟨_, a', hs', _⟩ := hB t h2
    have e := run_hnf_hnf (.inr (.inr ⟨a, b, rfl⟩)) (.inr (.inr ⟨S, a', rfl⟩)) hs hs'
    injection e with e1 _
    injection e1 with _ e2
    rw [e2] at ha
    exact notBS ha
  have foldA : ∀ t, A t → fold t ≠ 36 := by
    intro t h e
    obtain ⟨hp, a, b, hs, _, _⟩ := hA t h
    exact fold_hnf (steps_pure hp hs) (.inr (.inr ⟨a, b, rfl⟩)) ((InfNF.steps_fold hp hs).trans e)
  intro n
  induction n with
  | zero =>
    intro y z h _ _
    have := sz_pos y
    omega
  | succ n ih =>
    intro y z hsz hz hyz
    obtain ⟨hp, bL, bR, hs, hBL, hAR⟩ := hA _ hyz
    have hzS : z ≠ S := by
      intro e
      rw [e] at hz
      exact notBS hz
    rcases Decidable.em (y ⬝ z = S ⬝ bL ⬝ bR) with e | ne
    · injection e with _ e2
      rw [← e2] at hAR
      exact disj z hAR hz
    · rcases lemma_LL hp hzS (plus_of_steps_ne hs ne) with ⟨y', _, eR, hsy⟩ |
        ⟨p, q, _, eL, eR, hw⟩
      · have h1 := lemma_SS_sz hp.app_inv.1 hsy
        rw [eR] at hAR
        exact ih y' z (by omega) hz hAR
      · have hqS : q ≠ S := by
          intro e
          rw [e] at hw
          exact hzS (wrap_S hw)
        rw [eL] at hBL
        obtain ⟨hppq, c', hs', hc'⟩ := hB _ hBL
        obtain ⟨c, k, e1, e2⟩ := lemma_SS (sz (p ⬝ q)) (p ⬝ q) c' (Nat.le_refl _) hppq hs'
        cases k with
        | zero =>
          have e1' : p ⬝ q = S ⬝ S ⬝ c := e1
          have e2' : c' = c := e2
          injection e1' with _ e4
          have hAq : A q := by rw [e4, ← e2']; exact hc'
          have h36 : fold (q ⬝ (p ⬝ q)) = 36 :=
            claim_D hA hB hAq hBL [] (fun _ hx => by cases hx)
          rw [eR] at hAR
          exact foldA _ hAR h36
        | succ k =>
          have e1' : p ⬝ q = appS k (S ⬝ S ⬝ c) ⬝ S := e1
          injection e1' with _ e4
          exact hqS e4

/-- **Theorem N1.**  Let `A` and `B` be sets of closed S-terms such that every member of `A` has,
on its head run, a two-item head normal form `S a b` with `a ∈ B`, `b ∈ A`, and every member of
`B` has the head normal form `S S a'` with `a' ∈ A`.  Then `A` is empty. -/
theorem thm_N1 {A B : Term → Prop}
    (hA : ∀ t, A t → PureS t ∧ ∃ a b, Steps t (S ⬝ a ⬝ b) ∧ B a ∧ A b)
    (hB : ∀ t, B t → PureS t ∧ ∃ a, Steps t (S ⬝ S ⬝ a) ∧ A a) : ∀ t, ¬ A t := by
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
      rcases Decidable.em (t = S ⬝ a ⬝ b) with e | ne
      · have hlt : sz b < sz t := by rw [e]; exact sz_arg_lt _ b
        exact ih b (by omega) hb
      · obtain ⟨y, _, eb⟩ := lemma_L' ht hs ne
        rw [eb] at hb
        exact claim_E hA hB (sz y) y a (Nat.le_refl _) ha hb
  intro t h
  exact key (sz t) t (Nat.le_refl _) h

/-- No closed S-term `p` is convertible to `S (S S p) p`. -/
theorem no_S_SSp_p {p : Term} (hp : PureS p) : ¬ Convertible p (S ⬝ (S ⬝ S ⬝ p) ⬝ p) := by
  intro hc
  have hA : ∀ t, (PureS t ∧ Convertible t p) → PureS t ∧ ∃ a b, Steps t (S ⬝ a ⬝ b) ∧
      (PureS a ∧ Convertible a (S ⬝ S ⬝ p)) ∧ (PureS b ∧ Convertible b p) := by
    rintro t ⟨ht, hct⟩
    obtain ⟨a, b, hs, ca, cb⟩ := hnf2_conv ht (.app (.app .S .S) hp) hp (hct.trans hc)
    have hpab := steps_pure ht hs
    exact ⟨ht, a, b, hs, ⟨hpab.app_inv.1.app_inv.2, ca⟩, ⟨hpab.app_inv.2, cb⟩⟩
  have hB : ∀ t, (PureS t ∧ Convertible t (S ⬝ S ⬝ p)) → PureS t ∧ ∃ a, Steps t (S ⬝ S ⬝ a) ∧
      (PureS a ∧ Convertible a p) := by
    rintro t ⟨ht, hct⟩
    obtain ⟨s', a, hs, cs, ca⟩ := hnf2_conv ht .S hp hct
    have hpab := steps_pure ht hs
    obtain ⟨w, h1, h2⟩ := conv_iff_join.mp cs
    rw [InfNF.wsteps_from_S h2] at h1
    have e := InfNF.wsteps_to_S hpab.app_inv.1.app_inv.2 h1
    rw [e] at hs
    exact ⟨ht, a, hs, hpab.app_inv.2, ca⟩
  exact thm_N1 (A := fun t => PureS t ∧ Convertible t p)
    (B := fun t => PureS t ∧ Convertible t (S ⬝ S ⬝ p)) hA hB p ⟨hp, Convertible.refl p⟩

/-! ## Theorem N2 -/

theorem normal_S : Normal S := fun _ s => by cases s

theorem Normal.app_inv {f x : Term} (h : Normal (f ⬝ x)) : Normal f ∧ Normal x :=
  ⟨fun _ s => h _ (.left x s), fun _ s => h _ (.right f s)⟩

theorem normalizing_S1 {n : Term} (h : Normalizing n) : Normalizing (S ⬝ n) := by
  obtain ⟨n', hs, nf⟩ := h
  refine ⟨S ⬝ n', WSteps.right S hs, ?_⟩
  intro u s
  cases s with
  | left _ s' => cases s'
  | right _ s' => exact nf _ s'

/-- The pigeonhole step `finite_descent` under a double negation: it is enough that no member
lacks a small `D`-successor. -/
theorem finite_descent_nn {B : Nat} {P : Term → Prop} {D : Term → Term → Prop}
    (hp : ∀ t, P t → PureS t) (trans : ∀ {a b c : Term}, D a b → D b c → D a c)
    (irr : ∀ t, P t → ¬ D t t)
    (hd : ∀ t, P t → ¬¬ ∃ t₃, P t₃ ∧ D t t₃ ∧ sz t₃ ≤ B) : ∀ t, ¬ P t := by
  have key : ∀ (k : Nat) (l : List Term), l.length ≤ k → ∀ t, P t →
      (∀ t', P t' → D t t' → sz t' ≤ B → t' ∈ l) → False := by
    intro k
    induction k with
    | zero =>
      intro l hl t hP hmem
      apply hd t hP
      intro ⟨t₃, h1, h2, h3⟩
      have := List.length_pos_of_mem (hmem t₃ h1 h2 h3)
      omega
    | succ k ih =>
      intro l hl t hP hmem
      apply hd t hP
      intro ⟨t₃, h1, h2, h3⟩
      have hin := hmem t₃ h1 h2 h3
      have hlen := del_length_lt hin
      refine ih (del t₃ l) (by omega) t₃ h1 (fun t' hP' hD' hs' => ?_)
      have ne : t' ≠ t₃ := by
        intro e
        rw [e] at hD'
        exact irr t₃ h1 hD'
      exact mem_del ne (hmem t' hP' (trans h2 hD') hs')
  intro t hP
  exact key _ (enum B) (Nat.le_refl _) t hP (fun t' hP' _ hs => mem_enum B (hp t' hP') hs)

/-- Members of the sets of Theorem N2 have no normal form. -/
theorem n2_not_norm {M : Nat} {A B : Term → Prop}
    (hA : ∀ t, A t → PureS t ∧ ∃ a b, Steps t (S ⬝ a ⬝ b) ∧ A a ∧ B b)
    (hB : ∀ t, B t → PureS t ∧ ∃ n a, Steps t (S ⬝ n ⬝ a) ∧ Normalizing n ∧ sz n ≤ M ∧ A a) :
    ∀ (k : Nat) (v n : Term), sz n ≤ k → A v ∨ B v → WSteps v n → Normal n → False := by
  intro k
  induction k with
  | zero =>
    intro v n h _ _ _
    have := sz_pos n
    omega
  | succ k ih =>
    intro v n hsz hv hvn nf
    rcases hv with h | h
    · obtain ⟨hp, a, b, hs, ha, _⟩ := hA v h
      have hH := wsteps_to_normal hs.weak hvn nf
      obtain ⟨a', b', e, haa, _⟩ := hnf2_wsteps (steps_pure hp hs) hH
      rw [e] at nf hsz
      have h1 : sz a' < sz (S ⬝ a' ⬝ b') := Nat.lt_trans (sz_arg_lt S a') (sz_fun_lt _ b')
      exact ih a a' (by omega) (.inl ha) haa nf.app_inv.1.app_inv.2
    · obtain ⟨hp, m, a, hs, _, _, ha⟩ := hB v h
      have hH := wsteps_to_normal hs.weak hvn nf
      obtain ⟨m', a', e, _, haa⟩ := hnf2_wsteps (steps_pure hp hs) hH
      rw [e] at nf hsz
      have h1 : sz a' < sz (S ⬝ m' ⬝ a') := sz_arg_lt _ a'
      exact ih a a' (by omega) (.inl ha) haa nf.app_inv.2

/-- Steps 1 and 2 of Theorem N2: a member `q` of `A` whose head run takes a step to `S z vR`,
with `z` large and `vR ∈ B`, is `q⁻ z`, or its run passes through a frame `S x p u` with
`z = p u`, `u` normalizing of leaf count at most `M + 1`, and `sz x ≤ 3`. -/
theorem n2_td {M : Nat} {A B : Term → Prop}
    (hB : ∀ t, B t → PureS t ∧ ∃ n a, Steps t (S ⬝ n ⬝ a) ∧ Normalizing n ∧ sz n ≤ M ∧ A a)
    {q z vR : Term} (hq : PureS q) (hbig : M + 1 < sz z) (hs : Steps q (S ⬝ z ⬝ vR))
    (hne : q ≠ S ⬝ z ⬝ vR) (hvR : B vR) :
    (∃ qm, q = qm ⬝ z) ∨
    ∃ x p u, Steps q (S ⬝ x ⬝ p ⬝ u) ∧ z = p ⬝ u ∧ Normalizing u ∧ sz u ≤ M + 1 ∧ sz x ≤ 3 := by
  obtain ⟨hpv, n, a', hsB, hn, hnM, _⟩ := hB vR hvR
  obtain ⟨y, eR, _, hcase⟩ := lemma_TD hq (plus_of_steps_ne hs hne)
  have e1S : sz S = 1 := rfl
  have hzS : z ≠ S := by
    intro e
    rw [e] at hbig
    omega
  rw [eR] at hsB hpv
  obtain ⟨ey, _⟩ := cor_LL1 hpv hzS hsB (by omega)
  rcases hcase with ⟨qm, e, _⟩ | ⟨x, p, u, hfr, _, eL, hφ⟩
  · exact .inl ⟨qm, e⟩
  · have hpfr := steps_pure hq hfr
    have hpxu : PureS (x ⬝ u) := .app hpfr.app_inv.1.app_inv.1.app_inv.2 hpfr.app_inv.2
    obtain ⟨c, k, e1, e2⟩ := lemma_SS (sz (x ⬝ u)) (x ⬝ u) y (Nat.le_refl _) hpxu hφ
    cases k with
    | zero =>
      have e1' : x ⬝ u = S ⬝ S ⬝ c := e1
      have e2' : y = c := e2
      injection e1' with e3 e4
      have eu : u = S ⬝ n := e4.trans (e2'.symm.trans ey)
      refine .inr ⟨x, p, u, hfr, eL, ?_, ?_, ?_⟩
      · rw [eu]; exact normalizing_S1 hn
      · rw [eu]
        have e5 : sz (S ⬝ n) = 1 + sz n := rfl
        omega
      · rw [e3]
        have e5 : sz (S ⬝ S) = 2 := rfl
        omega
    | succ k =>
      have e1' : x ⬝ u = appS k (S ⬝ S ⬝ c) ⬝ S := e1
      have e2' : y = appS k c ⬝ S := e2
      injection e1' with e3 e4
      rw [ey] at e2'
      injection e2' with e5 _
      refine .inr ⟨x, p, u, hfr, eL, ?_, ?_, ?_⟩
      · rw [e4]; exact ⟨S, .refl _, normal_S⟩
      · rw [e4]
        omega
      · cases k with
        | zero =>
          have e5' : S = c := e5
          rw [e3, ← e5']
          have e6 : sz (appS 0 (S ⬝ S ⬝ S)) = 3 := rfl
          omega
        | succ k =>
          have e5' : S = appS k c ⬝ S := e5
          cases e5'

/-- **Theorem N2.**  Let `A` and `B` be sets of closed S-terms such that every member of `A` has,
on its head run, a two-item head normal form `S a b` with `a ∈ A`, `b ∈ B`, and every member of
`B` has a two-item head normal form `S n a'` with `n` normalizing of leaf count at most `M` and
`a' ∈ A`.  Then `A` is empty.  Uses Theorem 2 (`right_combs`, teeth of leaf count at most 3) and
`HeadRec.no_ground_loop` (through the pigeonhole). -/
theorem thm_N2 {M : Nat} {A B : Term → Prop}
    (hA : ∀ t, A t → PureS t ∧ ∃ a b, Steps t (S ⬝ a ⬝ b) ∧ A a ∧ B b)
    (hB : ∀ t, B t → PureS t ∧ ∃ n a, Steps t (S ⬝ n ⬝ a) ∧ Normalizing n ∧ sz n ≤ M ∧ A a) :
    ∀ t, ¬ A t := by
  have nn := n2_not_norm hA hB
  -- `A'`: members of `A` without a small descendant in `A`
  have hdesc : ∀ {t a b : Term}, Steps t (S ⬝ a ⬝ b) → Desc t a :=
    fun hs => ⟨_, hs.weak, .left _ (.right S .refl)⟩
  -- stage 2: no member of `A'` of the form `p u` with `u` good of size `s`
  have level : ∀ (d s : Nat), M + 2 ≤ s + d → ∀ p,
      ¬ ∃ u, sz u = s ∧ Normalizing u ∧ sz u ≤ M + 1 ∧ A (p ⬝ u) ∧
        ∀ t₃, A t₃ → Desc (p ⬝ u) t₃ → M + 1 < sz t₃ := by
    intro d
    induction d with
    | zero =>
      intro s hs p hP
      obtain ⟨u, h1, _, h2, _, _⟩ := hP
      omega
    | succ d ih =>
      intro s hs
      have hC : Closed 3 (fun p => ∃ u, sz u = s ∧ Normalizing u ∧ sz u ≤ M + 1 ∧ A (p ⬝ u) ∧
          ∀ t₃, A t₃ → Desc (p ⬝ u) t₃ → M + 1 < sz t₃) := by
        intro p hP
        obtain ⟨u, hsu, hnu, hu, hAg, hbig⟩ := hP
        obtain ⟨hpg, a, b, hsg, ha, hb⟩ := hA _ hAg
        refine ⟨hpg.app_inv.1, ?_⟩
        have hDa := hdesc hsg
        have hbiga := hbig a ha hDa
        obtain ⟨nu, hnu1, hnu2⟩ := hnu
        rcases Decidable.em (p ⬝ u = S ⬝ a ⬝ b) with e | ne
        · exfalso
          injection e with _ e2
          rw [← e2] at hb
          exact nn (sz nu) u nu (Nat.le_refl _) (.inr hb) hnu1 hnu2
        · rcases n2_td hB hpg hbiga hsg ne hb with ⟨qm, e⟩ | ⟨x', p', u', hfr, eL, hn', hsz', hx⟩
          · exfalso
            injection e with _ e2
            rw [← e2] at ha
            exact nn (sz nu) u nu (Nat.le_refl _) (.inl ha) hnu1 hnu2
          · rw [eL] at ha hDa
            have hbig' : ∀ t₃, A t₃ → Desc (p' ⬝ u') t₃ → M + 1 < sz t₃ :=
              fun t₃ h1 h2 => hbig t₃ h1 (hDa.trans h2)
            rcases (fact_LI hpg hfr).2 with ⟨e, hsp⟩ | lt
            · exact ⟨p', ⟨u', by rw [e]; exact hsu, hn', hsz', ha, hbig'⟩, .inr ⟨x', hx, hsp⟩⟩
            · exact absurd ⟨u', rfl, hn', hsz', ha, hbig'⟩ (ih (sz u') (by omega) p')
      exact right_combs hC
  -- stage 1: from a member of `A'` reach one of the form `p u` with `u` good
  have stage1 : ∀ (n : Nat) (t : Term), sz t ≤ n → A t →
      (∀ t₃, A t₃ → Desc t t₃ → M + 1 < sz t₃) → False := by
    intro n
    induction n with
    | zero =>
      intro t h _ _
      have := sz_pos t
      omega
    | succ n ih =>
      intro t hsz hAt hbig
      obtain ⟨ht, a, b, hs, ha, hb⟩ := hA t hAt
      have hDa := hdesc hs
      have hbiga := hbig a ha hDa
      have hbig' : ∀ t₃, A t₃ → Desc a t₃ → M + 1 < sz t₃ :=
        fun t₃ h1 h2 => hbig t₃ h1 (hDa.trans h2)
      rcases Decidable.em (t = S ⬝ a ⬝ b) with e | ne
      · have hlt : sz a < sz t := by
          rw [e]
          exact Nat.lt_trans (sz_arg_lt S a) (sz_fun_lt _ b)
        exact ih a (by omega) ha hbig'
      · rcases n2_td hB ht hbiga hs ne hb with ⟨qm, e⟩ | ⟨x, p, u, _, eL, hn, hsz', _⟩
        · have hlt : sz a < sz t := by
            rw [e]
            exact sz_arg_lt qm a
          exact ih a (by omega) ha hbig'
        · rw [eL] at ha hbig'
          exact level (M + 2) (sz u) (by omega) p ⟨u, rfl, hn, hsz', ha, hbig'⟩
  refine finite_descent_nn (B := M + 1) (D := Desc) (fun t h => (hA t h).1)
    (fun h1 h2 => Desc.trans h1 h2) (fun t h => Desc.irrefl (hA t h).1) ?_
  intro t hAt hno
  refine stage1 (sz t) t (Nat.le_refl _) hAt (fun t₃ h1 h2 => ?_)
  rcases Nat.lt_or_ge (M + 1) (sz t₃) with h | h
  · exact h
  · exact absurd ⟨t₃, h1, h2, h⟩ hno

/-- No closed S-term `p` is convertible to `S p (S n p)`, for every closed normalizing `n`. -/
theorem no_S_p_Snp {p n : Term} (hp : PureS p) (hn : PureS n) (hnn : Normalizing n) :
    ¬ Convertible p (S ⬝ p ⬝ (S ⬝ n ⬝ p)) := by
  intro hc
  obtain ⟨nf, hnnf, hnf⟩ := hnn
  have hA : ∀ t, (PureS t ∧ Convertible t p) → PureS t ∧ ∃ a b, Steps t (S ⬝ a ⬝ b) ∧
      (PureS a ∧ Convertible a p) ∧ (PureS b ∧ Convertible b (S ⬝ n ⬝ p)) := by
    rintro t ⟨ht, hct⟩
    obtain ⟨a, b, hs, ca, cb⟩ := hnf2_conv ht hp (.app (.app .S hn) hp) (hct.trans hc)
    have hpab := steps_pure ht hs
    exact ⟨ht, a, b, hs, ⟨hpab.app_inv.1.app_inv.2, ca⟩, ⟨hpab.app_inv.2, cb⟩⟩
  have hB : ∀ t, (PureS t ∧ Convertible t (S ⬝ n ⬝ p)) → PureS t ∧ ∃ m a, Steps t (S ⬝ m ⬝ a) ∧
      Normalizing m ∧ sz m ≤ sz nf ∧ (PureS a ∧ Convertible a p) := by
    rintro t ⟨ht, hct⟩
    obtain ⟨m, a, hs, cm, ca⟩ := hnf2_conv ht hn hp hct
    have hpab := steps_pure ht hs
    obtain ⟨c, h1, h2⟩ := conv_iff_join.mp cm
    have hmnf : WSteps m nf := h1.trans (wsteps_to_normal h2 hnnf hnf)
    exact ⟨ht, m, a, hs, ⟨nf, hmnf, hnf⟩, sz_wsteps hpab.app_inv.1.app_inv.2 hmnf,
      hpab.app_inv.2, ca⟩
  exact thm_N2 (M := sz nf) (A := fun t => PureS t ∧ Convertible t p)
    (B := fun t => PureS t ∧ Convertible t (S ⬝ n ⬝ p)) hA hB p ⟨hp, Convertible.refl p⟩

end Ncfp
