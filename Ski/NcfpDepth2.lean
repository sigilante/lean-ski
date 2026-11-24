import Ski.NcfpN2
open Term

/-!
# NCFP: general lemmas of §15 and the two-hole shapes of depth 2

Source: `notes/NCFP-proof.md`, §15.  Setting and notation as in `Ski/Ncfp.lean`.

What is proved:

* `lemma_SR` (Lemma SR, second item) and `lemma_Dstar` (Lemma D\*, function part) with
  `dstar_frames`.
* `mixed_combs'` (Theorem G′): mixed combs with teeth bounded at the non-literal steps only.  The
  lemmas `runG_inner'`, `runG'`, `small_descG'` are those of Theorem G in `Ski/Ncfp.lean` with the
  weaker hypothesis.
* `thm_X` (Theorem X): no set in which every member has a head normal form with one or two items,
  each in the set or small, at least one in the set, and every non-literal member has a small
  first item.
* `lemma_LC` (Lemma LC, left chain), in a form that asks only for the frames.

What is not proved here: Lemma W, the pair graph, tameness, Theorem T (see `Ski/NcfpScheme.lean`
for a restricted form).
-/

namespace Ncfp
open HnfS HeadRec Conv

/-! ## Lemma SR -/

/-- **Lemma SR** (second item).  Let the closed S-term `y z` have, on its head run, the two-item
head normal form `S h₁ h₂`.  Then `sz z ≤ sz h₂`; and if `z ≠ S`, either `y z` is literal (so
`h₂ = z`), or `sz z ≤ sz h₁` and `sz z < sz h₂`. -/
theorem lemma_SR {y z h₁ h₂ : Term} (hp : PureS (y ⬝ z)) (hs : Steps (y ⬝ z) (S ⬝ h₁ ⬝ h₂)) :
    sz z ≤ sz h₂ ∧ (z ≠ S → y ⬝ z = S ⬝ h₁ ⬝ h₂ ∨ (sz z ≤ sz h₁ ∧ sz z < sz h₂)) := by
  rcases Decidable.em (y ⬝ z = S ⬝ h₁ ⬝ h₂) with e | ne
  · have e' := e
    injection e' with _ e2
    exact ⟨by rw [e2]; exact Nat.le_refl _, fun _ => .inl e⟩
  · have key : z ≠ S → sz z ≤ sz h₁ ∧ sz z < sz h₂ := by
      intro hz
      rcases lemma_LL hp hz (plus_of_steps_ne hs ne) with ⟨y', e1, e2, _⟩ | ⟨p, q, _, e1, e2, hw⟩
      · have h := sz_arg_lt y' z
        rw [← e2] at h
        rw [e1]
        exact ⟨Nat.le_refl _, h⟩
      · have h1 := hw.sz_le
        have h2 := sz_arg_lt p q
        have h3 := sz_fun_lt q (p ⬝ q)
        rw [← e1] at h2
        rw [← e2] at h3
        exact ⟨by omega, by omega⟩
    rcases Decidable.em (z = S) with e | hz
    · refine ⟨?_, fun h => absurd e h⟩
      rw [e]
      exact sz_pos h₂
    · exact ⟨Nat.le_of_lt (key hz).2, fun _ => .inr (key hz)⟩

/-! ## Lemma D* -/

/-- The three-item frames of Lemma D\*, step 3 and 4.  Let a head run start at `f m gm` (the
frame after a three-item frame `S f g m`, `gm = g m`), with `f ≠ S` and `sz m ≥ 3`, and end at a
last frame `S S y z`.  Then `f = S S`, `y = m`, `z = gm`; or the run passes through a frame
`S (S S) p q` with `y = q`, `z = p q`, `p` a wrapping of `m` and `q = g' p`. -/
theorem dstar_frames : ∀ (n k : Nat) (f m gm y z : Term), k ≤ n → PureS (f ⬝ m ⬝ gm) →
    f ≠ S → 3 ≤ sz m → (∃ g, gm = g ⬝ m) → StepsK k (f ⬝ m ⬝ gm) (S ⬝ S ⬝ y ⬝ z) →
    (f = S ⬝ S ∧ y = m ∧ z = gm) ∨
    ∃ p q, Steps (f ⬝ m ⬝ gm) (S ⬝ (S ⬝ S) ⬝ p ⬝ q) ∧ y = q ∧ z = p ⬝ q ∧ Wrap m p ∧
      ∃ g', q = g' ⬝ p := by
  intro n
  induction n with
  | zero =>
    intro k f m gm y z hk hp hf hm hgm hrun
    have hk0 : k = 0 := Nat.le_zero.mp hk
    rw [hk0] at hrun
    cases hrun with
    | refl => exact .inl ⟨rfl, rfl, rfl⟩
  | succ n ih =>
    intro k f m gm y z hk hp hf hm hgm hrun
    have e1S : sz S = 1 := rfl
    have e2S : sz (S ⬝ S) = 2 := rfl
    have hmS : m ≠ S := by
      intro e
      rw [e] at hm
      omega
    rcases split (stepsK_steps hrun) rfl hp with ⟨e', he, hs'⟩ | ⟨f', g', h1, h2⟩
    · injection he with e1 e2
      rw [← e1] at hs'
      obtain ⟨ef, ey⟩ := cor_LL1 hp.app_inv.1 hmS hs' (by omega)
      exact .inl ⟨ef, ey, e2⟩
    · have hplus : Plus (f ⬝ m ⬝ gm) (f' ⬝ gm ⬝ (g' ⬝ gm)) :=
        steps_step_plus (Steps.left gm h1) (.S f' g' gm)
      have hp' := steps_pure hp hplus.steps
      obtain ⟨k', hlt, hk'⟩ := stepsK_plus hp hrun hplus h2
      obtain ⟨g, eg⟩ := hgm
      have hgmsz : sz m < sz gm := by rw [eg]; exact sz_arg_lt g m
      have hf' : f' ≠ S := by
        intro e
        rw [e] at h2
        have e3 := InfNF.steps_from_hnf (.inr (.inr ⟨gm, g' ⬝ gm, rfl⟩)) h2
        injection e3 with e4 _
        injection e4 with e5 _
        cases e5
      have hwm : Wrap m gm := by rw [eg]; exact .wrap g .refl
      rcases ih k' f' gm (g' ⬝ gm) y z (by omega) hp' hf' (by omega) ⟨g', rfl⟩ hk' with
        ⟨ef', ey, ez⟩ | ⟨p, q, hs2, ey, ez, hw, hq⟩
      · rw [ef'] at h1
        obtain ⟨_, eg'⟩ := cor_LL1 hp.app_inv.1 hmS h1 (by omega)
        refine .inr ⟨m, gm, ?_, ey, ?_, .refl, g, eg⟩
        · have h3 := Steps.left gm h1
          rw [eg'] at h3
          exact h3
        · rw [ez, eg']
      · exact .inr ⟨p, q, hplus.steps.trans hs2, ey, ez, Wrap.trans hwm hw, hq⟩

/-- **Lemma D\*** (function part).  Let the head run of the closed S-term `a β` take one or more
steps to the two-item head normal form `S h₁ h₂`, and let `sz β ≥ 3`.  Then `a` has, on its head
run, a two-item head normal form `S b₁ a_R`, the run of `a β` passes through `S b₁ a_R β`, and
(A) `b₁ = S`, `h₁ = β`, `h₂ = a_R β`; or
(Bn) `b₁ = S S`, `h₁ = a_R β`, `h₂ = β (a_R β)`; or
(Bf) the run passes through `S (S S) p q` with `p` a wrapping of `β`, `q = g p`, `h₁ = p q`,
`h₂ = q (p q)`.
(Exclusivity, and `b₁ ∉ {S, S S}` in case (Bf), are not stated.) -/
theorem lemma_Dstar {a β h₁ h₂ : Term} (hp : PureS (a ⬝ β)) (hβ : 3 ≤ sz β)
    (h : Plus (a ⬝ β) (S ⬝ h₁ ⬝ h₂)) :
    ∃ b₁ aR, Steps a (S ⬝ b₁ ⬝ aR) ∧ Steps (a ⬝ β) (S ⬝ b₁ ⬝ aR ⬝ β) ∧
      ((b₁ = S ∧ h₁ = β ∧ h₂ = aR ⬝ β) ∨
       (b₁ = S ⬝ S ∧ h₁ = aR ⬝ β ∧ h₂ = β ⬝ (aR ⬝ β)) ∨
       ∃ p q, Steps (a ⬝ β) (S ⬝ (S ⬝ S) ⬝ p ⬝ q) ∧ Wrap β p ∧ (∃ g, q = g ⬝ p) ∧
         h₁ = p ⬝ q ∧ h₂ = q ⬝ (p ⬝ q)) := by
  obtain ⟨y, hlast, e2⟩ := lemma_L hp h
  rcases split hlast rfl hp with ⟨e', he, hs'⟩ | ⟨f, g, h1, h2⟩
  · injection he with e1 e3
    rw [← e1] at hs'
    exact ⟨S, y, hs', Steps.left β hs', .inl ⟨rfl, e3, by rw [e2, e3]⟩⟩
  · refine ⟨f, g, h1, Steps.left β h1, ?_⟩
    have hplus : Plus (a ⬝ β) (f ⬝ β ⬝ (g ⬝ β)) :=
      steps_step_plus (Steps.left β h1) (.S f g β)
    have hp' := steps_pure hp hplus.steps
    have hf : f ≠ S := by
      intro e
      rw [e] at h2
      have e3 := InfNF.steps_from_hnf (.inr (.inr ⟨β, g ⬝ β, rfl⟩)) h2
      injection e3 with e4 _
      injection e4 with e5 _
      cases e5
    obtain ⟨k, hk⟩ := stepsK_of_steps h2
    rcases dstar_frames k k f β (g ⬝ β) y h₁ (Nat.le_refl _) hp' hf hβ ⟨g, rfl⟩ hk with
      ⟨ef, ey, ez⟩ | ⟨p, q, hs2, ey, ez, hw, hq⟩
    · exact .inr (.inl ⟨ef, ez, by rw [e2, ey, ez]⟩)
    · exact .inr (.inr ⟨p, q, hplus.steps.trans hs2, hw, hq, ez, by rw [e2, ey, ez]⟩)

/-! ## Theorem G′ -/

/-- `NextG' M t t'`: as `NextG`, with the bounds on the teeth required only when the head run of
`t` takes a step. -/
def NextG' (M : Nat) (t t' : Term) : Prop :=
  Steps t (S ⬝ t') ∨ (∃ a, (t ≠ S ⬝ a ⬝ t' → sz a ≤ M) ∧ Steps t (S ⬝ a ⬝ t')) ∨
    ∃ b, (t ≠ S ⬝ t' ⬝ b → sz b ≤ M) ∧ Steps t (S ⬝ t' ⬝ b)

theorem NextG'.desc {M : Nat} {t t' : Term} (h : NextG' M t t') : Desc t t' := by
  rcases h with h1 | ⟨a, _, h2⟩ | ⟨b, _, h3⟩
  · exact ⟨_, h1.weak, .right _ .refl⟩
  · exact ⟨_, h2.weak, .right _ .refl⟩
  · exact ⟨_, h3.weak, .left b (.right _ .refl)⟩

/-- `P` is a set of closed S-terms each of which has a next term in `P` (`NextG'`). -/
def ClosedG' (M : Nat) (P : Term → Prop) : Prop :=
  ∀ t, P t → PureS t ∧ ∃ t', P t' ∧ NextG' M t t'

/-- Inside a block of non-literal terms with last item `a` (the mixed analogue of
`run_inner`, weak bounds): a small term has appeared, or the block has ended at a large `u` with `y₀` rigid
over `u`, or the block has produced an SS-chain of `i` links. -/
theorem runG_inner' {M : Nat} {P : Term → Prop} (hC : ClosedG' M P) {t₁ y₀ a : Term}
    (ha : sz a ≤ M) (hy₀ : PureS y₀) (hD₀ : Desc t₁ (y₀ ⬝ a)) (hP₀ : P (y₀ ⬝ a))
    (grow : ∀ t y' a', P t → sz a < sz a' → sz a' ≤ M →
      Steps t (S ⬝ S ⬝ y' ⬝ a') → P (y' ⬝ a') → Res M P t a') :
    ∀ i : Nat, (∃ t₃, P t₃ ∧ Desc t₁ t₃ ∧ sz t₃ ≤ M + 1) ∨
      (∃ u, P u ∧ M + 1 < sz u ∧ Rigid u y₀) ∨
      ∃ y, SSPath i y₀ y ∧ P (y ⬝ a) ∧ Desc t₁ (y ⬝ a) := by
  intro i
  induction i with
  | zero => exact .inr (.inr ⟨y₀, .zero _, hP₀, hD₀⟩)
  | succ i ih =>
    rcases ih with ev | blk | ⟨y, path, hPy, hDy⟩
    · exact .inl ev
    · exact .inr (.inl blk)
    · obtain ⟨hpure, t', hP', hN⟩ := hC _ hPy
      have hDt' : Desc t₁ t' := hDy.trans hN.desc
      have small : sz t' ≤ M → (∃ t₃, P t₃ ∧ Desc t₁ t₃ ∧ sz t₃ ≤ M + 1) :=
        fun h => ⟨t', hP', hDt', Nat.le_succ_of_le h⟩
      rcases hN with h1 | ⟨a', ha', h2⟩ | ⟨b, hb, h3⟩
      · have e := hnf1_literal hpure h1
        injection e with _ e2
        rw [e2] at ha
        exact .inl (small ha)
      · rcases Decidable.em (y ⬝ a = S ⬝ a' ⬝ t') with e | ne
        · injection e with _ e2
          rw [e2] at ha
          exact .inl (small ha)
        · obtain ⟨y', hs, e⟩ := lemma_L' hpure h2 ne
          rw [e] at hP' hDt'
          rcases link hpure hs with ⟨ea, hy⟩ | lt
          · rw [ea] at hP' hDt'
            exact .inr (.inr ⟨y', path.snoc hy, hP', hDt'⟩)
          · rcases grow (y ⬝ a) y' a' hPy lt (ha' ne) hs hP' with ⟨t₃, h4, h5, h6⟩ | ⟨u, g, _, _, _, eq⟩
            · exact .inl ⟨t₃, h4, hDy.trans h5, h6⟩
            · injection eq with _ e2
              rw [e2] at lt
              exact absurd lt (Nat.lt_irrefl _)
      · rcases Decidable.em (y ⬝ a = S ⬝ t' ⬝ b) with e | ne
        · injection e with e1 _
          rcases Nat.lt_or_ge (M + 1) (sz t') with big | le
          · have hne : t' ≠ S := by
              intro e'
              rw [e'] at big
              have e1 : sz S = 1 := rfl
              omega
            have hr : Rigid t' y := by rw [e1]; exact .base
            exact .inr (.inl ⟨t', hP', big, sspath_rigid hne hy₀ path hr⟩)
          · exact .inl ⟨t', hP', hDt', le⟩
        · obtain ⟨y', _, e⟩ := lemma_L' hpure h3 ne
          have hb := hb ne
          have := sz_arg_lt y' t'
          rw [← e] at this
          exact .inl (small (by omega))

/-- A block of the mixed comb, from its first term `t₁` with last frame `S S y a` (the mixed
analogue of `run`, weak bounds). -/
theorem runG' {M : Nat} {P : Term → Prop} (hC : ClosedG' M P) :
    ∀ (d : Nat) (t₁ y a : Term), M - sz a ≤ d → sz a ≤ M → P t₁ → Steps t₁ (S ⬝ S ⬝ y ⬝ a) →
      P (y ⬝ a) → Res M P t₁ a := by
  have fin : ∀ (t₁ y a : Term), sz a ≤ M → P t₁ → Steps t₁ (S ⬝ S ⬝ y ⬝ a) → P (y ⬝ a) →
      (∀ t y' a', P t → sz a < sz a' → sz a' ≤ M →
        Steps t (S ⬝ S ⬝ y' ⬝ a') → P (y' ⬝ a') → Res M P t a') → Res M P t₁ a := by
    intro t₁ y a ha hP₁ hs hPy grow
    have ht₁ := (hC t₁ hP₁).1
    have hD₀ : Desc t₁ (y ⬝ a) :=
      ⟨S ⬝ a ⬝ (y ⬝ a), (hs.trans (.single (.S S y a))).weak, .right _ .refl⟩
    have hy : PureS y := (steps_pure ht₁ hs).app_inv.1.app_inv.2
    rcases runG_inner' hC ha hy hD₀ hPy grow (2 * sz y + 1) with ev | ⟨u, hPu, big, hr⟩ |
      ⟨y', path, _, _⟩
    · exact .inl ev
    · have hne : u ≠ S := by
        intro e'
        rw [e'] at big
        have e1 : sz S = 1 := rfl
        omega
      have hlt := hr.sz_lt
      have e := no_pred ht₁ hs (by omega) (hr.not_appS hne)
      exact .inr ⟨u, y, hPu, hr, big, e⟩
    · have := ss_bound (sz y) y (Nat.le_refl _) hy _ _ path
      exfalso
      omega
  intro d
  induction d with
  | zero =>
    intro t₁ y a hd ha hP₁ hs hPy
    exact fin t₁ y a ha hP₁ hs hPy (fun _ _ a' _ lt ha' _ _ => by exfalso; omega)
  | succ d ih =>
    intro t₁ y a hd ha hP₁ hs hPy
    exact fin t₁ y a ha hP₁ hs hPy
      (fun t y' a' hPt lt ha' hs' hP' => ih t y' a' (by omega) ha' hPt hs' hP')

/-- Below every term of a mixed comb there is a small term of the comb.  Induction on the leaf
count: a literal step and a completed block both lead to a smaller term. -/
theorem small_descG' {M : Nat} {P : Term → Prop} (hC : ClosedG' M P) :
    ∀ (n : Nat) (t : Term), sz t ≤ n → P t → ∃ t₃, P t₃ ∧ Desc t t₃ ∧ sz t₃ ≤ M + 1 := by
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
    have down : ∀ u, P u → Desc t u → sz u < sz t → ∃ t₃, P t₃ ∧ Desc t t₃ ∧ sz t₃ ≤ M + 1 := by
      intro u hPu hD hlt
      obtain ⟨t₃, h1, h2, h3⟩ := ih u (by omega) hPu
      exact ⟨t₃, h1, hD.trans h2, h3⟩
    have hD := hN.desc
    rcases hN with h1 | ⟨a, ha, h2⟩ | ⟨b, hb, h3⟩
    · have e := hnf1_literal ht h1
      exact down t' hP' hD (by rw [e]; exact sz_arg_lt _ _)
    · rcases Decidable.em (t = S ⬝ a ⬝ t') with e | ne
      · exact down t' hP' hD (by rw [e]; exact sz_arg_lt _ _)
      · obtain ⟨y, hs, e⟩ := lemma_L' ht h2 ne
        rw [e] at hP'
        rcases runG' hC (M - sz a) t y a (Nat.le_refl _) (ha ne) hP hs hP' with ev | ⟨u, g, hPu, hr, _, eq⟩
        · exact ev
        · have hsub : PSub u t := by rw [eq]; exact .left a (.right _ hr.sub)
          exact down u hPu ⟨t, .refl t, hsub⟩ hsub.sz_lt
    · rcases Decidable.em (t = S ⬝ t' ⬝ b) with e | ne
      · exact down t' hP' hD (by rw [e]; exact Nat.lt_trans (sz_arg_lt S t') (sz_fun_lt _ b))
      · obtain ⟨y, _, e⟩ := lemma_L' ht h3 ne
        have hb := hb ne
        have := sz_arg_lt y t'
        rw [← e] at this
        exact ⟨t', hP', hD, by omega⟩

/-- **Theorem G′** (mixed combs with teeth bounded at non-literal steps), choice-free form.  Let
`P` be a set of closed S-terms such that every `t` in `P` has, on its head run, a head normal form
`S t'`, `S a t'` or `S t' b` with `t'` in `P`, where `sz a ≤ M`, resp. `sz b ≤ M`, whenever the
run takes a step.  Then `P` is empty. -/
theorem mixed_combs' {M : Nat} {P : Term → Prop} (hC : ClosedG' M P) : ∀ t, ¬ P t :=
  desc_finite (fun t hP => (hC t hP).1) (fun t hP => small_descG' hC (sz t) t (Nat.le_refl _) hP)

/-! ## Theorem X -/

/-- **Theorem X.**  Let `Z` be a set of closed S-terms such that every member has, on its head
run, a head normal form `S c` with `c ∈ Z`, or `S c d` where each of `c`, `d` is in `Z` or has
leaf count at most `M`, at least one of them is in `Z`, and `sz c ≤ M` if the run takes a step.
Then `Z` is empty.  (Conj. HN under the hypothesis that non-literal members have a small first
item.) -/
theorem thm_X {M : Nat} {Z : Term → Prop}
    (hZ : ∀ t, Z t → PureS t ∧ ((∃ c, Steps t (S ⬝ c) ∧ Z c) ∨
      ∃ c d, Steps t (S ⬝ c ⬝ d) ∧ (Z c ∨ sz c ≤ M) ∧ (Z d ∨ sz d ≤ M) ∧ (Z c ∨ Z d) ∧
        (t ≠ S ⬝ c ⬝ d → sz c ≤ M))) : ∀ t, ¬ Z t := by
  have hC : ClosedG' M Z := by
    intro t ht
    obtain ⟨hp, hk⟩ := hZ t ht
    refine ⟨hp, ?_⟩
    rcases hk with ⟨c, hs, hc⟩ | ⟨c, d, hs, _, hd, hcd, hlit⟩
    · exact ⟨c, hc, .inl hs⟩
    · have form2 : Z d → ∃ t', Z t' ∧ NextG' M t t' :=
        fun h => ⟨d, h, .inr (.inl ⟨c, hlit, hs⟩)⟩
      rcases hd with h | h
      · exact form2 h
      · rcases hcd with h' | h'
        · exact ⟨c, h', .inr (.inr ⟨d, fun _ => h, hs⟩)⟩
        · exact form2 h'
  exact mixed_combs' hC

/-! ## Lemma LC -/

/-- **Lemma LC** (left chain).  Let `P` be a set of closed S-terms such that the head run of every
member passes through a three-item frame `S x p q` with `p q` in `P`, `sz x ≤ K` and `sz q ≤ K`.
Then `P` is empty.  (The note's hypotheses, that `p q` is the first item of the head normal form
and that case (B) of Lemma TD holds, are not needed.)  Uses Fact LI and Theorem 2. -/
theorem lemma_LC {K : Nat} {P : Term → Prop}
    (hP : ∀ t, P t → PureS t ∧ ∃ x p q, Steps t (S ⬝ x ⬝ p ⬝ q) ∧ P (p ⬝ q) ∧ sz x ≤ K ∧
      sz q ≤ K) : ∀ t, ¬ P t := by
  have level : ∀ (d s : Nat), K + 1 ≤ s + d → ∀ p, ¬ ∃ q, sz q = s ∧ P (p ⬝ q) := by
    intro d
    induction d with
    | zero =>
      intro s hs p hq
      obtain ⟨q, hq, hPt⟩ := hq
      obtain ⟨hp, x', p', q', hfr, _, _, hq'⟩ := hP _ hPt
      have := (fact_LI hp hfr).1.sz_le
      omega
    | succ d ih =>
      intro s hs
      have hC : Closed K (fun p => ∃ q, sz q = s ∧ P (p ⬝ q)) := by
        intro p hq
        obtain ⟨q, hq, hPt⟩ := hq
        obtain ⟨hp, x', p', q', hfr, hP', hx', hq'⟩ := hP _ hPt
        refine ⟨hp.app_inv.1, ?_⟩
        rcases (fact_LI hp hfr).2 with ⟨e, hsp⟩ | lt
        · exact ⟨p', ⟨q', by rw [e]; exact hq, hP'⟩, .inr ⟨x', hx', hsp⟩⟩
        · exact absurd ⟨q', rfl, hP'⟩ (ih (sz q') (by omega) p')
      exact right_combs hC
  intro t ht
  obtain ⟨_, x, p, q, _, hP', _, hq⟩ := hP t ht
  exact level (K + 1) (sz q) (by omega) p ⟨q, rfl, hP'⟩

end Ncfp
