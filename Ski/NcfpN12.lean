import Ski.NcfpXplus
open Term

/-!
# NCFP: Theorem N12, eight four-leaf contexts with a B-cycle

Source: `notes/NCFP-proof.md`, §16.2.  Setting and notation as in `Ski/Ncfp.lean`.

Conventions.  `HasTy2 X Y₁ Y₂` ("X: [Y₁, Y₂]"): every member of `X` is a closed S-term with, on
its head run, a two-item head normal form `S a b`, `a ∈ Y₁`, `b ∈ Y₂`.  `HasTy1 X Y` ("X: [Y]"):
a one-item head normal form `S c`, `c ∈ Y`.  `SmallNf M` (the note's σ): normalizing of leaf count
at most `M`.

What is proved:

* `lemma_Dstar_add` (Lemma D\* with its addendum): in case (Bf), `p` is `β`, or `a_R β`, or
  `g′ m` with `sz β ≤ sz g′` and `m` a wrapping of `β` (`dstar_frames_add` is the frame
  induction).
* `lemma_AP1` … `lemma_AP4` (Lemma AP).  AP4 asks `3 ≤ sz v` in place of `sz v > M + 1`, and in
  case (Bf) gives `sz v ≤ sz p° < sz q°`.
* `lemma_PF` (Lemma PF), with `3 ≤ sz u` in place of `sz u > M + 1`.
* `claim_P` (Claim P of Theorem N12, for `A: [B, A]`, `B: [Y₁, Y₂]`), with the scheme-dependent
  cases as hypotheses.
* `thm_N12_1` … `thm_N12_8` (Theorem N12, the eight families of sets; `M ≥ 1` as in the note).
* The eight equations, for closed `p` and closed normalizing `n`: `p` is convertible to none of
  `S (S (S n p) p) p`, `S (S (S p n) p) p`, `S (S (S n p) (S p)) p`, `S (S (S p n) (S p)) p`,
  `S (S (S p) (S n p)) p`, `S (S (S p) (S p n)) p`, `S (S p (S n p)) p`, `S (S p (S p n)) p`
  (`no_S_SSnpp_p`, `no_S_SSpnp_p`, `no_S_SSnpSp_p`, `no_S_SSpnSp_p`, `no_S_SSpSnp_p`,
  `no_S_SSpSpn_p`, `no_S_SpSnp_p`, `no_S_SpSpn_p`).

Differences from the note.  The last step is Theorem X⁺ (`thm_Xplus`, bound `M + 1`) in all eight
schemes (the note uses Theorem X in seven).  In scheme 4 the cases (f)(Bn), (f)(Bf) are closed by
AP2 (the note refers to scheme 3).  Non-normalization (NN) is derived set by set from `A: [B, A]`.

What is not proved: a general theorem for open exceptions; the pair graph.
-/

namespace Ncfp
open HnfS HeadRec Conv

/-! ## Lemma D*, addendum -/

/-- `dstar_frames` with the origin of `p`: it is `m`, or `gm`, or an application `g″ m″` with
`sz m ≤ sz g″` and `m″` a wrapping of `m`. -/
theorem dstar_frames_add : ∀ (n k : Nat) (f m gm y z : Term), k ≤ n → PureS (f ⬝ m ⬝ gm) →
    f ≠ S → 3 ≤ sz m → (∃ g, gm = g ⬝ m) → StepsK k (f ⬝ m ⬝ gm) (S ⬝ S ⬝ y ⬝ z) →
    (f = S ⬝ S ∧ y = m ∧ z = gm) ∨
    ∃ p q, Steps (f ⬝ m ⬝ gm) (S ⬝ (S ⬝ S) ⬝ p ⬝ q) ∧ y = q ∧ z = p ⬝ q ∧ Wrap m p ∧
      (∃ g', q = g' ⬝ p) ∧
      (p = m ∨ p = gm ∨ ∃ g'' m'', p = g'' ⬝ m'' ∧ sz m ≤ sz g'' ∧ Wrap m m'') := by
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
      have hg'sz : sz m ≤ sz g' := (lemma_SR hp.app_inv.1 h1).1
      have hf' : f' ≠ S := by
        intro e
        rw [e] at h2
        have e3 := InfNF.steps_from_hnf (.inr (.inr ⟨gm, g' ⬝ gm, rfl⟩)) h2
        injection e3 with e4 _
        injection e4 with e5 _
        cases e5
      have hwm : Wrap m gm := by rw [eg]; exact .wrap g .refl
      rcases ih k' f' gm (g' ⬝ gm) y z (by omega) hp' hf' (by omega) ⟨g', rfl⟩ hk' with
        ⟨ef', ey, ez⟩ | ⟨p, q, hs2, ey, ez, hw, hq, hform⟩
      · rw [ef'] at h1
        obtain ⟨_, eg'⟩ := cor_LL1 hp.app_inv.1 hmS h1 (by omega)
        refine .inr ⟨m, gm, ?_, ey, ?_, .refl, ⟨g, eg⟩, .inl rfl⟩
        · have h3 := Steps.left gm h1
          rw [eg'] at h3
          exact h3
        · rw [ez, eg']
      · refine .inr ⟨p, q, hplus.steps.trans hs2, ey, ez, Wrap.trans hwm hw, hq, ?_⟩
        rcases hform with e | e | ⟨g'', m'', e, hsz, hw''⟩
        · exact .inr (.inl e)
        · exact .inr (.inr ⟨g', gm, e, hg'sz, hwm⟩)
        · exact .inr (.inr ⟨g'', m'', e, by omega, Wrap.trans hwm hw''⟩)

/-- **Lemma D\*** with its addendum.  As `lemma_Dstar`; in case (Bf), moreover, `p = β`, or
`p = a_R β`, or `p = g′ m` with `sz β ≤ sz g′` and `m` a wrapping of `β`. -/
theorem lemma_Dstar_add {a β h₁ h₂ : Term} (hp : PureS (a ⬝ β)) (hβ : 3 ≤ sz β)
    (h : Plus (a ⬝ β) (S ⬝ h₁ ⬝ h₂)) :
    ∃ b₁ aR, Steps a (S ⬝ b₁ ⬝ aR) ∧ Steps (a ⬝ β) (S ⬝ b₁ ⬝ aR ⬝ β) ∧
      ((b₁ = S ∧ h₁ = β ∧ h₂ = aR ⬝ β) ∨
       (b₁ = S ⬝ S ∧ h₁ = aR ⬝ β ∧ h₂ = β ⬝ (aR ⬝ β)) ∨
       ∃ p q, Steps (a ⬝ β) (S ⬝ (S ⬝ S) ⬝ p ⬝ q) ∧ Wrap β p ∧ (∃ g, q = g ⬝ p) ∧
         h₁ = p ⬝ q ∧ h₂ = q ⬝ (p ⬝ q) ∧
         (p = β ∨ p = aR ⬝ β ∨ ∃ g' m, p = g' ⬝ m ∧ sz β ≤ sz g' ∧ Wrap β m)) := by
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
    rcases dstar_frames_add k k f β (g ⬝ β) y h₁ (Nat.le_refl _) hp' hf hβ ⟨g, rfl⟩ hk with
      ⟨ef, ey, ez⟩ | ⟨p, q, hs2, ey, ez, hw, hq, hform⟩
    · exact .inr (.inl ⟨ef, ez, by rw [e2, ey, ez]⟩)
    · exact .inr (.inr ⟨p, q, hplus.steps.trans hs2, hw, hq, ez, by rw [e2, ey, ez], hform⟩)

/-! ## Typed sets -/

/-- The note's σ: normalizing terms of leaf count at most `M`. -/
def SmallNf (M : Nat) (t : Term) : Prop := Normalizing t ∧ sz t ≤ M

/-- "X: [Y₁, Y₂]": every member of `X` is a closed S-term with, on its head run, a two-item head
normal form `S a b`, `a ∈ Y₁`, `b ∈ Y₂`. -/
def HasTy2 (X Y₁ Y₂ : Term → Prop) : Prop :=
  ∀ t, X t → PureS t ∧ ∃ a b, Steps t (S ⬝ a ⬝ b) ∧ Y₁ a ∧ Y₂ b

/-- "X: [Y]": every member of `X` is a closed S-term with a one-item head normal form `S c`,
`c ∈ Y`. -/
def HasTy1 (X Y : Term → Prop) : Prop :=
  ∀ t, X t → PureS t ∧ ∃ c, Steps t (S ⬝ c) ∧ Y c

theorem hnf2_ne_S {a b : Term} (h : Steps S (S ⬝ a ⬝ b)) : False := by
  have e := steps_S h
  cases e

theorem hnf2_ne_S1 {a b c : Term} (h : Steps (S ⬝ c) (S ⬝ a ⬝ b)) : False := by
  have e := InfNF.steps_from_hnf (.inr (.inl ⟨c, rfl⟩)) h
  injection e with e1 _
  cases e1

theorem HasTy2.not_S {X Y₁ Y₂ : Term → Prop} (hX : HasTy2 X Y₁ Y₂) : ¬ X S := by
  intro h
  obtain ⟨_, a, b, hs, _, _⟩ := hX _ h
  exact hnf2_ne_S hs

theorem HasTy2.not_S1 {X Y₁ Y₂ : Term → Prop} (hX : HasTy2 X Y₁ Y₂) (c : Term) :
    ¬ X (S ⬝ c) := by
  intro h
  obtain ⟨_, a, b, hs, _, _⟩ := hX _ h
  exact hnf2_ne_S1 hs

/-- The items of a two-item head normal form on the head run of a member are in the entries. -/
theorem HasTy2.items {X Y₁ Y₂ : Term → Prop} (hX : HasTy2 X Y₁ Y₂) {t a b : Term} (ht : X t)
    (hs : Steps t (S ⬝ a ⬝ b)) : Y₁ a ∧ Y₂ b := by
  obtain ⟨_, a', b', hs', ha, hb⟩ := hX t ht
  have e := run_hnf_hnf (.inr (.inr ⟨a, b, rfl⟩)) (.inr (.inr ⟨a', b', rfl⟩)) hs hs'
  injection e with e1 e2
  injection e1 with _ e3
  rw [e3, e2]
  exact ⟨ha, hb⟩

theorem disj_first {X Y P₁ P₂ Q₁ Q₂ : Term → Prop} (hX : HasTy2 X P₁ P₂) (hY : HasTy2 Y Q₁ Q₂)
    (h : ∀ t, P₁ t → Q₁ t → False) : ∀ t, X t → Y t → False := by
  intro t h1 h2
  obtain ⟨_, a, b, hs, ha, _⟩ := hX t h1
  exact h a ha (hY.items h2 hs).1

theorem disj_second {X Y P₁ P₂ Q₁ Q₂ : Term → Prop} (hX : HasTy2 X P₁ P₂) (hY : HasTy2 Y Q₁ Q₂)
    (h : ∀ t, P₂ t → Q₂ t → False) : ∀ t, X t → Y t → False := by
  intro t h1 h2
  obtain ⟨_, a, b, hs, _, hb⟩ := hX t h1
  exact h b hb (hY.items h2 hs).2

/-- A set of kind one is disjoint from a set of kind two. -/
theorem disj_kind {X Y P Q₁ Q₂ : Term → Prop} (hX : HasTy1 X P) (hY : HasTy2 Y Q₁ Q₂) :
    ∀ t, X t → Y t → False := by
  intro t h1 h2
  obtain ⟨hp, c, hs, _⟩ := hX t h1
  obtain ⟨_, a, b, hs', _, _⟩ := hY t h2
  rw [hnf1_literal hp hs] at hs'
  exact hnf2_ne_S1 hs'

/-! ## Non-normalization (NN) -/

/-- The items of a head normal form of a normalizing closed S-term are normalizing. -/
theorem norm_items2 {t a b : Term} (hp : PureS t) (hs : Steps t (S ⬝ a ⬝ b))
    (hn : Normalizing t) : Normalizing a ∧ Normalizing b := by
  obtain ⟨n, hvn, nf⟩ := hn
  have hH := wsteps_to_normal hs.weak hvn nf
  obtain ⟨a', b', e, haa, hbb⟩ := hnf2_wsteps (steps_pure hp hs) hH
  rw [e] at nf
  exact ⟨⟨a', haa, nf.app_inv.1.app_inv.2⟩, ⟨b', hbb, nf.app_inv.2⟩⟩

theorem norm_items1 {t c : Term} (hp : PureS t) (hs : Steps t (S ⬝ c)) (hn : Normalizing t) :
    Normalizing c := by
  obtain ⟨n, hvn, nf⟩ := hn
  have hH := wsteps_to_normal hs.weak hvn nf
  obtain ⟨c', e, hcc⟩ := hnf1_wsteps (steps_pure hp hs) hH
  rw [e] at nf
  exact ⟨c', hcc, nf.app_inv.2⟩

theorem nn_self {A B : Term → Prop} (hA : HasTy2 A B A) : ∀ t, A t → ¬ Normalizing t := by
  intro t ht
  refine not_normalizing (U := A) (fun v hv => ?_) ht
  obtain ⟨hp, a, b, hs, _, hb⟩ := hA v hv
  exact ⟨hp, a, b, hs, .inr hb⟩

theorem HasTy2.nn_left {X Y₁ Y₂ : Term → Prop} (hX : HasTy2 X Y₁ Y₂)
    (h : ∀ t, Y₁ t → ¬ Normalizing t) : ∀ t, X t → ¬ Normalizing t := by
  intro t ht hn
  obtain ⟨hp, a, b, hs, ha, _⟩ := hX t ht
  exact h a ha (norm_items2 hp hs hn).1

theorem HasTy2.nn_right {X Y₁ Y₂ : Term → Prop} (hX : HasTy2 X Y₁ Y₂)
    (h : ∀ t, Y₂ t → ¬ Normalizing t) : ∀ t, X t → ¬ Normalizing t := by
  intro t ht hn
  obtain ⟨hp, a, b, hs, _, hb⟩ := hX t ht
  exact h b hb (norm_items2 hp hs hn).2

theorem HasTy1.nn {X Y : Term → Prop} (hX : HasTy1 X Y) (h : ∀ t, Y t → ¬ Normalizing t) :
    ∀ t, X t → ¬ Normalizing t := by
  intro t ht hn
  obtain ⟨hp, c, hs, hc⟩ := hX t ht
  exact h c hc (norm_items1 hp hs hn)

/-! ## Lemma AP -/

/-- **Lemma AP1.**  A member `a v` of `X: [σ, Y]` with `sz v > M + 1`: `a = S c`, `sz c ≤ M`,
`v ∈ Y`. -/
theorem lemma_AP1 {M : Nat} {X Y : Term → Prop} (hX : HasTy2 X (SmallNf M) Y) {a v : Term}
    (h : X (a ⬝ v)) (hv : M + 1 < sz v) : ∃ c, a = S ⬝ c ∧ sz c ≤ M ∧ Y v := by
  obtain ⟨hp, c, d, hs, hc, hd⟩ := hX _ h
  have hvS : v ≠ S := by
    intro e
    rw [e] at hv
    have e1 : sz S = 1 := rfl
    omega
  have hcM := hc.2
  obtain ⟨e1, e2⟩ := cor_LL1 hp hvS hs (by omega)
  rw [e2] at hd
  exact ⟨c, e1, hcM, hd⟩

/-- AP1: the function part has leaf count at most `M + 1`. -/
theorem lemma_AP1_sz {M : Nat} {X Y : Term → Prop} (hX : HasTy2 X (SmallNf M) Y) {a v : Term}
    (h : X (a ⬝ v)) (hv : M + 1 < sz v) : sz a ≤ M + 1 := by
  obtain ⟨c, e, hc, _⟩ := lemma_AP1 hX h hv
  rw [e]
  show 1 + sz c ≤ M + 1
  omega

/-- **Lemma AP2.**  A member `a v` of `X: [Y, σ]` has `sz v ≤ M`. -/
theorem lemma_AP2 {M : Nat} {X Y : Term → Prop} (hX : HasTy2 X Y (SmallNf M)) {a v : Term}
    (h : X (a ⬝ v)) : sz v ≤ M := by
  obtain ⟨hp, c, d, hs, _, hd⟩ := hX _ h
  exact Nat.le_trans (lemma_SR hp hs).1 hd.2

/-- **Lemma AP3.**  A member `a v` of `X: [Y]`: `a = S` and `v ∈ Y`. -/
theorem lemma_AP3 {X Y : Term → Prop} (hX : HasTy1 X Y) {a v : Term} (h : X (a ⬝ v)) :
    a = S ∧ Y v := by
  obtain ⟨hp, c, hs, hc⟩ := hX _ h
  have e := hnf1_literal hp hs
  injection e with e1 e2
  rw [e2]
  exact ⟨e1, hc⟩

/-- **Lemma AP4.**  A member `a v` of `X: [Y₁, Y₂]` with `sz v ≥ 3`: (lit) `a = S c`, `c ∈ Y₁`,
`v ∈ Y₂`; or (A) the head normal form of `a` is `S S a′`, `v ∈ Y₁`, `a′ v ∈ Y₂`; or (Bn) it is
`S (S S) a′`, `a′ v ∈ Y₁`, `v (a′ v) ∈ Y₂`; or (Bf) the run of `a v` passes through
`S (S S) p° q°` with `sz v ≤ sz p° < sz q°`, `p° q° ∈ Y₁`, `q° (p° q°) ∈ Y₂`. -/
theorem lemma_AP4 {X Y₁ Y₂ : Term → Prop} (hX : HasTy2 X Y₁ Y₂) {a v : Term} (h : X (a ⬝ v))
    (hv : 3 ≤ sz v) :
    (∃ c, a = S ⬝ c ∧ Y₁ c ∧ Y₂ v) ∨
    (∃ a', Steps a (S ⬝ S ⬝ a') ∧ Y₁ v ∧ Y₂ (a' ⬝ v)) ∨
    (∃ a', Steps a (S ⬝ (S ⬝ S) ⬝ a') ∧ Y₁ (a' ⬝ v) ∧ Y₂ (v ⬝ (a' ⬝ v))) ∨
    ∃ p q, Steps (a ⬝ v) (S ⬝ (S ⬝ S) ⬝ p ⬝ q) ∧ sz v ≤ sz p ∧ sz p < sz q ∧ Y₁ (p ⬝ q) ∧
      Y₂ (q ⬝ (p ⬝ q)) := by
  obtain ⟨hp, h₁, h₂, hs, hy₁, hy₂⟩ := hX _ h
  rcases Decidable.em (a ⬝ v = S ⬝ h₁ ⬝ h₂) with e | ne
  · injection e with e1 e2
    rw [← e2] at hy₂
    exact .inl ⟨h₁, e1, hy₁, hy₂⟩
  · obtain ⟨b₁, aR, ha, _, hcase⟩ := lemma_Dstar hp hv (plus_of_steps_ne hs ne)
    rcases hcase with ⟨eb, e1, e2⟩ | ⟨eb, e1, e2⟩ | ⟨p, q, hfr, hw, ⟨g, hq⟩, e1, e2⟩
    · rw [eb] at ha
      rw [e1] at hy₁
      rw [e2] at hy₂
      exact .inr (.inl ⟨aR, ha, hy₁, hy₂⟩)
    · rw [eb] at ha
      rw [e1] at hy₁
      rw [e2] at hy₂
      exact .inr (.inr (.inl ⟨aR, ha, hy₁, hy₂⟩))
    · rw [e1] at hy₁
      rw [e2] at hy₂
      exact .inr (.inr (.inr ⟨p, q, hfr, hw.sz_le, by rw [hq]; exact sz_arg_lt g p, hy₁, hy₂⟩))

/-! ## Lemma PF -/

/-- **Lemma PF.**  Let `A: [B, A]` with `A ∩ B = ∅`, and `y u ∈ A` with `u ∈ B`, `sz u ≥ 3`.
Then there is `y′` with `y′ u ∈ A` and (n) the head normal form of `y′` is `S (S S) a` and
`a u ∈ B`; or (f) the run of `y′ u` passes through `S (S S) p q` with `p q ∈ B`, `q = g p`, `p` a
wrapping of `u`, and `p = u`, or `p = a u` where `S b₁ a` is the head normal form of `y′`, or
`p = g′ m` with `sz u ≤ sz g′` and `m` a wrapping of `u`.  Induction on `sz y` (Corollary SS1). -/
theorem lemma_PF {A B : Term → Prop} (hA : HasTy2 A B A) (dAB : ∀ t, A t → B t → False) :
    ∀ (n : Nat) (y u : Term), sz y ≤ n → A (y ⬝ u) → B u → 3 ≤ sz u →
      ∃ y', A (y' ⬝ u) ∧
        ((∃ a, Steps y' (S ⬝ (S ⬝ S) ⬝ a) ∧ B (a ⬝ u)) ∨
         ∃ b₁ a p q, Steps y' (S ⬝ b₁ ⬝ a) ∧ Steps (y' ⬝ u) (S ⬝ (S ⬝ S) ⬝ p ⬝ q) ∧
           B (p ⬝ q) ∧ (∃ g, q = g ⬝ p) ∧ Wrap u p ∧
           (p = u ∨ p = a ⬝ u ∨ ∃ g' m, p = g' ⬝ m ∧ sz u ≤ sz g' ∧ Wrap u m)) := by
  intro n
  induction n with
  | zero =>
    intro y u h
    have := sz_pos y
    exfalso
    omega
  | succ n ih =>
    intro y u hsz hw hu hu3
    obtain ⟨hp, h₁, h₂, hs, hy₁, hy₂⟩ := hA _ hw
    rcases Decidable.em (y ⬝ u = S ⬝ h₁ ⬝ h₂) with e | ne
    · injection e with _ e2
      rw [← e2] at hy₂
      exact (dAB u hy₂ hu).elim
    · obtain ⟨b₁, aR, ha, _, hcase⟩ := lemma_Dstar_add hp hu3 (plus_of_steps_ne hs ne)
      rcases hcase with ⟨eb, _, e2⟩ | ⟨eb, e1, _⟩ | ⟨p, q, hfr, hwp, hq, e1, _, hform⟩
      · rw [eb] at ha
        rw [e2] at hy₂
        have hsz' := lemma_SS_sz hp.app_inv.1 ha
        exact ih aR u (by omega) hy₂ hu hu3
      · rw [eb] at ha
        rw [e1] at hy₁
        exact ⟨y, hw, .inl ⟨aR, ha, hy₁⟩⟩
      · rw [e1] at hy₁
        exact ⟨y, hw, .inr ⟨b₁, aR, p, q, ha, hfr, hy₁, hq, hwp, hform⟩⟩

/-! ## Claim P -/

/-- What Claim P keeps of the form of `p` in case (f) of Lemma PF: `p` is large, and it is a
member of `B` (the case `p = u`) or an application with a large argument. -/
def PForm (M : Nat) (B : Term → Prop) (p : Term) : Prop :=
  M + 1 < sz p ∧ (B p ∨ ∃ e m, p = e ⬝ m ∧ M + 1 < sz m)

/-- A term of the form `PForm` whose head normal form has a first item of leaf count at most 2 and
a second item of leaf count at most `M + 1` is a member of `B` (Corollary LL1 excludes the
application with a large argument). -/
theorem pform_small {M : Nat} {B : Term → Prop} (hM : 1 ≤ M) {p h a' : Term}
    (hPF : PForm M B p) (hpp : PureS p) (hs : Steps p (S ⬝ h ⬝ a')) (hh : sz h ≤ 2)
    (ha : sz a' ≤ M + 1) : B p := by
  rcases hPF.2 with hB | ⟨e, m, ep, hm⟩
  · exact hB
  · rw [ep] at hpp hs
    have hmS : m ≠ S := by
      intro e'
      rw [e'] at hm
      have e1 : sz S = 1 := rfl
      omega
    obtain ⟨_, e2⟩ := cor_LL1 hpp hmS hs (by omega)
    rw [e2] at ha
    exfalso
    omega

/-- **Claim P** of Theorem N12.  Let `A: [B, A]`, `B: [Y₁, Y₂]`, with `B` disjoint from `A`, `Y₁`
and `Y₂`.  Suppose the cases (Bn) and (Bf) of Lemma AP4 for a member `a u` of `B` with `u ∈ B`
large, and the cases (A), (Bn), (Bf) for a member `p q` of `B` with `q = g p` and `p` of the form
`PForm`, are impossible (hypotheses `nBn`, `hBf`, `fA`, `fBn`; (Bf) is the same statement in both).
Then no `y u ∈ A` has `u ∈ B` with `sz u > M + 1`. -/
theorem claim_P {M : Nat} {A B Y₁ Y₂ : Term → Prop} (hM : 1 ≤ M)
    (hA : HasTy2 A B A) (hB : HasTy2 B Y₁ Y₂)
    (dAB : ∀ t, A t → B t → False) (dY₁ : ∀ t, Y₁ t → B t → False)
    (dY₂ : ∀ t, Y₂ t → B t → False)
    (nBn : ∀ a' u, B u → M + 1 < sz u → Y₁ (a' ⬝ u) → Y₂ (u ⬝ (a' ⬝ u)) → False)
    (hBf : ∀ p q, M + 1 < sz p → sz p < sz q → Y₁ (p ⬝ q) → Y₂ (q ⬝ (p ⬝ q)) → False)
    (fA : ∀ a' g p, PForm M B p → PureS p → Steps p (S ⬝ S ⬝ a') → Y₁ (g ⬝ p) →
      Y₂ (a' ⬝ (g ⬝ p)) → False)
    (fBn : ∀ a' g p, PForm M B p → PureS p → Steps p (S ⬝ (S ⬝ S) ⬝ a') →
      Y₁ (a' ⬝ (g ⬝ p)) → Y₂ (g ⬝ p ⬝ (a' ⬝ (g ⬝ p))) → False) :
    ∀ y u, A (y ⬝ u) → B u → M + 1 < sz u → False := by
  intro y u hw hu hbig
  obtain ⟨y', _, hcase⟩ := lemma_PF hA dAB (sz y) y u (Nat.le_refl _) hw hu (by omega)
  rcases hcase with ⟨a, _, hx⟩ | ⟨b₁, a, p, q, _, _, hx, ⟨g, hq⟩, hwp, hform⟩
  · -- (n): `a u ∈ B`
    rcases lemma_AP4 hB hx (by omega) with ⟨c, _, _, h2⟩ | ⟨a', _, h1, _⟩ | ⟨a', _, h1, h2⟩ |
      ⟨p', q', _, hp1, hp2, h1, h2⟩
    · exact dY₂ u h2 hu
    · exact dY₁ u h1 hu
    · exact nBn a' u hu hbig h1 h2
    · exact hBf p' q' (by omega) hp2 h1 h2
  · -- (f): `p q ∈ B`, `q = g p`
    have hpu := hwp.sz_le
    have hpq : sz p < sz q := by rw [hq]; exact sz_arg_lt g p
    have hpp : PureS p := (hB _ hx).1.app_inv.1
    have hPF : PForm M B p := by
      refine ⟨by omega, ?_⟩
      rcases hform with e | e | ⟨g', m, e, _, hwm⟩
      · rw [e]
        exact .inl hu
      · exact .inr ⟨a, u, e, hbig⟩
      · have h3 := hwm.sz_le
        exact .inr ⟨g', m, e, by omega⟩
    rcases lemma_AP4 hB hx (by omega) with ⟨c, ec, h1, _⟩ | ⟨a', hs, h1, h2⟩ | ⟨a', hs, h1, h2⟩ |
      ⟨p', q', _, hp1, hp2, h1, h2⟩
    · -- (lit): `p = S c`, `c ∈ Y₁`
      rcases hform with e | e | ⟨g', m, e, hsz, _⟩
      · rw [e] at ec
        rw [ec] at hu
        exact hB.not_S1 c hu
      · rw [e] at ec
        injection ec with _ e2
        rw [← e2] at h1
        exact dY₁ u h1 hu
      · rw [e] at ec
        injection ec with e1 _
        rw [e1] at hsz
        have e1S : sz S = 1 := rfl
        omega
    · rw [hq] at h1 h2
      exact fA a' g p hPF hpp hs h1 h2
    · rw [hq] at h1 h2
      exact fBn a' g p hPF hpp hs h1 h2
    · exact hBf p' q' (by omega) hp2 h1 h2

/-- With Claim P: a member `y z` of `A: [B, A]` with `sz z > M + 1` has `z ∈ A` (it is literal)
or `z ∈ B` (case (A) of Lemma AP4). -/
theorem big_arg_A {M : Nat} {A B : Term → Prop} (hM : 1 ≤ M) (hA : HasTy2 A B A)
    (hP : ∀ y u, A (y ⬝ u) → B u → M + 1 < sz u → False) {y z : Term} (h : A (y ⬝ z))
    (hz : M + 1 < sz z) : A z ∨ B z := by
  rcases lemma_AP4 hA h (by omega) with ⟨c, _, _, h2⟩ | ⟨a', _, h1, _⟩ | ⟨a', _, h1, h2⟩ |
    ⟨p, q, _, hp1, _, h1, h2⟩
  · exact .inl h2
  · exact .inr h1
  · have h3 := sz_arg_lt a' z
    exact (hP z (a' ⬝ z) h2 h1 (by omega)).elim
  · have h3 := sz_fun_lt p q
    exact (hP q (p ⬝ q) h2 h1 (by omega)).elim

/-- With Claim P: the first item of a non-literal member of `A` has leaf count at most `M + 1`. -/
theorem first_A {M : Nat} {A B : Term → Prop}
    (hP : ∀ y u, A (y ⬝ u) → B u → M + 1 < sz u → False) {y a : Term} (h : A (y ⬝ a))
    (ha : B a) : sz a ≤ M + 1 := by
  rcases Nat.lt_or_ge (M + 1) (sz a) with big | le
  · exact (hP y a h ha big).elim
  · exact le

/-- A member with a two-item head normal form, in the form of the hypothesis of Theorem X⁺: the
condition on a non-literal member is asked of the last frame `S S y a`. -/
theorem xp_mem {M : Nat} {Z : Term → Prop} {t a b : Term} (hp : PureS t)
    (hs : Steps t (S ⬝ a ⬝ b)) (ha : Z a ∨ sz a ≤ M) (hb : Z b ∨ sz b ≤ M) (hab : Z a ∨ Z b)
    (hne : ∀ y, b = y ⬝ a → sz a ≤ M ∨ y = S ∨ ∃ c', sz c' ≤ M ∧ y = S ⬝ c') :
    PureS t ∧ ((∃ c, Steps t (S ⬝ c) ∧ Z c) ∨
      ∃ c d, Steps t (S ⬝ c ⬝ d) ∧ (Z c ∨ sz c ≤ M) ∧ (Z d ∨ sz d ≤ M) ∧ (Z c ∨ Z d) ∧
        (t ≠ S ⬝ c ⬝ d → sz c ≤ M ∨ d = S ⬝ c ∨ ∃ c', sz c' ≤ M ∧ d = S ⬝ c' ⬝ c)) := by
  refine ⟨hp, .inr ⟨a, b, hs, ha, hb, hab, fun ne => ?_⟩⟩
  obtain ⟨y, _, eb⟩ := lemma_L' hp hs ne
  rcases hne y eb with h | h | ⟨c', h1, h2⟩
  · exact .inl h
  · exact .inr (.inl (by rw [eb, h]))
  · exact .inr (.inr ⟨c', h1, by rw [eb, h2]⟩)

/-! ## Theorem N12: the eight families -/

/-- **Theorem N12, scheme 1** (`S (S (S n p) p) p`): there are no sets `A ≠ ∅`, `B`, `C` with
`A: [B, A]`, `B: [C, A]`, `C: [σ, A]`. -/
theorem thm_N12_1 {M : Nat} {A B C : Term → Prop} (hM : 1 ≤ M) (hA : HasTy2 A B A)
    (hB : HasTy2 B C A) (hC : HasTy2 C (SmallNf M) A) : ∀ t, ¬ A t := by
  have nnA := nn_self hA
  have nnB := hB.nn_right nnA
  have nnC := hC.nn_right nnA
  have dAC : ∀ t, A t → C t → False := disj_first hA hC (fun t h1 h2 => nnB t h1 h2.1)
  have dCB : ∀ t, C t → B t → False := disj_first hC hB (fun t h1 h2 => nnC t h2 h1.1)
  have dAB : ∀ t, A t → B t → False := disj_first hA hB (fun t h1 h2 => dCB t h2 h1)
  have hP : ∀ y u, A (y ⬝ u) → B u → M + 1 < sz u → False := by
    refine claim_P hM hA hB dAB dCB dAB ?_ ?_ ?_ ?_
    · intro a' u hu hbig h1 _
      obtain ⟨_, _, _, h⟩ := lemma_AP1 hC h1 hbig
      exact dAB u h hu
    · intro p q hp hpq h1 _
      have h3 := lemma_AP1_sz hC h1 (by omega)
      omega
    · intro a' g p hPF _ hs h1 _
      obtain ⟨_, _, _, h⟩ := lemma_AP1 hC h1 hPF.1
      exact hB.not_S (hA.items h hs).1
    · intro a' g p hPF hpp hs h1 _
      have h0 := sz_arg_lt g p
      have h3 := hPF.1
      have hsm := lemma_AP1_sz hC h1 (by omega)
      have e2S : sz (S ⬝ S) = 2 := rfl
      exact hC.not_S1 S (hB.items (pform_small hM hPF hpp hs (by omega) hsm) hs).1
  refine fun t h => thm_Xplus (M := M + 1) (Z := fun t => A t ∨ B t ∨ C t) ?_ t (.inl h)
  rintro t (h | h | h)
  · obtain ⟨hp, a, b, hs, ha, hb⟩ := hA t h
    refine xp_mem hp hs (.inl (.inr (.inl ha))) (.inl (.inl hb)) (.inl (.inr (.inl ha)))
      (fun y eb => .inl ?_)
    rw [eb] at hb
    exact first_A hP hb ha
  · obtain ⟨hp, a, b, hs, ha, hb⟩ := hB t h
    refine xp_mem hp hs (.inl (.inr (.inr ha))) (.inl (.inl hb)) (.inl (.inr (.inr ha)))
      (fun y eb => .inl ?_)
    rw [eb] at hb
    rcases Nat.lt_or_ge (M + 1) (sz a) with big | le
    · rcases big_arg_A hM hA hP hb big with h' | h'
      · exact (dAC a h' ha).elim
      · exact (dCB a ha h').elim
    · exact le
  · obtain ⟨hp, a, b, hs, ha, hb⟩ := hC t h
    exact xp_mem hp hs (.inr (Nat.le_succ_of_le ha.2)) (.inl (.inl hb)) (.inr (.inl hb))
      (fun _ _ => .inl (Nat.le_succ_of_le ha.2))

/-- **Theorem N12, scheme 2** (`S (S (S p n) p) p`): there are no sets `A ≠ ∅`, `B`, `C` with
`A: [B, A]`, `B: [C, A]`, `C: [A, σ]`. -/
theorem thm_N12_2 {M : Nat} {A B C : Term → Prop} (hM : 1 ≤ M) (hA : HasTy2 A B A)
    (hB : HasTy2 B C A) (hC : HasTy2 C A (SmallNf M)) : ∀ t, ¬ A t := by
  have nnA := nn_self hA
  have dAC : ∀ t, A t → C t → False := disj_second hA hC (fun t h1 h2 => nnA t h1 h2.1)
  have dCB : ∀ t, C t → B t → False := disj_second hC hB (fun t h1 h2 => nnA t h2 h1.1)
  have dAB : ∀ t, A t → B t → False := disj_first hA hB (fun t h1 h2 => dCB t h2 h1)
  have hP : ∀ y u, A (y ⬝ u) → B u → M + 1 < sz u → False := by
    refine claim_P hM hA hB dAB dCB dAB ?_ ?_ ?_ ?_
    · intro a' u _ hbig h1 _
      have h3 := lemma_AP2 hC h1
      omega
    · intro p q hp hpq h1 _
      have h3 := lemma_AP2 hC h1
      omega
    · intro a' g p hPF _ _ h1 _
      have h3 := lemma_AP2 hC h1
      have h4 := hPF.1
      omega
    · intro a' g p hPF _ _ h1 _
      have h3 := lemma_AP2 hC h1
      have h4 := hPF.1
      have h5 := sz_arg_lt g p
      omega
  refine fun t h => thm_Xplus (M := M + 1) (Z := fun t => A t ∨ B t ∨ C t) ?_ t (.inl h)
  rintro t (h | h | h)
  · obtain ⟨hp, a, b, hs, ha, hb⟩ := hA t h
    refine xp_mem hp hs (.inl (.inr (.inl ha))) (.inl (.inl hb)) (.inl (.inr (.inl ha)))
      (fun y eb => .inl ?_)
    rw [eb] at hb
    exact first_A hP hb ha
  · obtain ⟨hp, a, b, hs, ha, hb⟩ := hB t h
    refine xp_mem hp hs (.inl (.inr (.inr ha))) (.inl (.inl hb)) (.inl (.inr (.inr ha)))
      (fun y eb => .inl ?_)
    rw [eb] at hb
    rcases Nat.lt_or_ge (M + 1) (sz a) with big | le
    · rcases big_arg_A hM hA hP hb big with h' | h'
      · exact (dAC a h' ha).elim
      · exact (dCB a ha h').elim
    · exact le
  · obtain ⟨hp, a, b, hs, ha, hb⟩ := hC t h
    refine xp_mem hp hs (.inl (.inl ha)) (.inr (Nat.le_succ_of_le hb.2)) (.inl (.inl ha))
      (fun y eb => .inl ?_)
    have h3 := sz_arg_lt y a
    rw [← eb] at h3
    have h4 := hb.2
    omega

/-- **Theorem N12, scheme 3** (`S (S (S n p) (S p)) p`): there are no sets `A ≠ ∅`, `B`, `C`,
`D` with `A: [B, A]`, `B: [C, D]`, `C: [σ, A]`, `D: [A]`. -/
theorem thm_N12_3 {M : Nat} {A B C D : Term → Prop} (hM : 1 ≤ M) (hA : HasTy2 A B A)
    (hB : HasTy2 B C D) (hC : HasTy2 C (SmallNf M) A) (hD : HasTy1 D A) : ∀ t, ¬ A t := by
  have nnA := nn_self hA
  have nnD := hD.nn nnA
  have nnB := hB.nn_right nnD
  have nnC := hC.nn_right nnA
  have dAC : ∀ t, A t → C t → False := disj_first hA hC (fun t h1 h2 => nnB t h1 h2.1)
  have dCB : ∀ t, C t → B t → False := disj_first hC hB (fun t h1 h2 => nnC t h2 h1.1)
  have dDB : ∀ t, D t → B t → False := disj_kind hD hB
  have dAB : ∀ t, A t → B t → False := disj_first hA hB (fun t h1 h2 => dCB t h2 h1)
  have hP : ∀ y u, A (y ⬝ u) → B u → M + 1 < sz u → False := by
    refine claim_P hM hA hB dAB dCB dDB ?_ ?_ ?_ ?_
    · intro a' u hu hbig h1 _
      obtain ⟨_, _, _, h⟩ := lemma_AP1 hC h1 hbig
      exact dAB u h hu
    · intro p q hp hpq h1 _
      have h3 := lemma_AP1_sz hC h1 (by omega)
      omega
    · intro a' g p _ _ _ h1 h2
      exact dAC _ (lemma_AP3 hD h2).2 h1
    · intro a' g p _ _ _ _ h2
      have e := (lemma_AP3 hD h2).1
      cases e
  refine fun t h => thm_Xplus (M := M + 1) (Z := fun t => A t ∨ B t ∨ C t ∨ D t) ?_ t (.inl h)
  rintro t (h | h | h | h)
  · obtain ⟨hp, a, b, hs, ha, hb⟩ := hA t h
    refine xp_mem hp hs (.inl (.inr (.inl ha))) (.inl (.inl hb)) (.inl (.inr (.inl ha)))
      (fun y eb => .inl ?_)
    rw [eb] at hb
    exact first_A hP hb ha
  · obtain ⟨hp, a, b, hs, ha, hb⟩ := hB t h
    refine xp_mem hp hs (.inl (.inr (.inr (.inl ha)))) (.inl (.inr (.inr (.inr hb))))
      (.inl (.inr (.inr (.inl ha)))) (fun y eb => ?_)
    rw [eb] at hb
    exact (dAC a (lemma_AP3 hD hb).2 ha).elim
  · obtain ⟨hp, a, b, hs, ha, hb⟩ := hC t h
    exact xp_mem hp hs (.inr (Nat.le_succ_of_le ha.2)) (.inl (.inl hb)) (.inr (.inl hb))
      (fun _ _ => .inl (Nat.le_succ_of_le ha.2))
  · obtain ⟨hp, c, hs, hc⟩ := hD t h
    exact ⟨hp, .inl ⟨c, hs, .inl hc⟩⟩

/-- **Theorem N12, scheme 4** (`S (S (S p n) (S p)) p`): there are no sets `A ≠ ∅`, `B`, `C`,
`D` with `A: [B, A]`, `B: [C, D]`, `C: [A, σ]`, `D: [A]`. -/
theorem thm_N12_4 {M : Nat} {A B C D : Term → Prop} (hM : 1 ≤ M) (hA : HasTy2 A B A)
    (hB : HasTy2 B C D) (hC : HasTy2 C A (SmallNf M)) (hD : HasTy1 D A) : ∀ t, ¬ A t := by
  have nnA := nn_self hA
  have nnD := hD.nn nnA
  have dAC : ∀ t, A t → C t → False := disj_second hA hC (fun t h1 h2 => nnA t h1 h2.1)
  have dCB : ∀ t, C t → B t → False := disj_second hC hB (fun t h1 h2 => nnD t h2 h1.1)
  have dDB : ∀ t, D t → B t → False := disj_kind hD hB
  have dAB : ∀ t, A t → B t → False := disj_first hA hB (fun t h1 h2 => dCB t h2 h1)
  have hP : ∀ y u, A (y ⬝ u) → B u → M + 1 < sz u → False := by
    refine claim_P hM hA hB dAB dCB dDB ?_ ?_ ?_ ?_
    · intro a' u _ hbig h1 _
      have h3 := lemma_AP2 hC h1
      omega
    · intro p q hp hpq h1 _
      have h3 := lemma_AP2 hC h1
      omega
    · intro a' g p hPF _ _ h1 _
      have h3 := lemma_AP2 hC h1
      have h4 := hPF.1
      omega
    · intro a' g p hPF _ _ h1 _
      have h3 := lemma_AP2 hC h1
      have h4 := hPF.1
      have h5 := sz_arg_lt g p
      omega
  refine fun t h => thm_Xplus (M := M + 1) (Z := fun t => A t ∨ B t ∨ C t ∨ D t) ?_ t (.inl h)
  rintro t (h | h | h | h)
  · obtain ⟨hp, a, b, hs, ha, hb⟩ := hA t h
    refine xp_mem hp hs (.inl (.inr (.inl ha))) (.inl (.inl hb)) (.inl (.inr (.inl ha)))
      (fun y eb => .inl ?_)
    rw [eb] at hb
    exact first_A hP hb ha
  · obtain ⟨hp, a, b, hs, ha, hb⟩ := hB t h
    refine xp_mem hp hs (.inl (.inr (.inr (.inl ha)))) (.inl (.inr (.inr (.inr hb))))
      (.inl (.inr (.inr (.inl ha)))) (fun y eb => ?_)
    rw [eb] at hb
    exact (dAC a (lemma_AP3 hD hb).2 ha).elim
  · obtain ⟨hp, a, b, hs, ha, hb⟩ := hC t h
    refine xp_mem hp hs (.inl (.inl ha)) (.inr (Nat.le_succ_of_le hb.2)) (.inl (.inl ha))
      (fun y eb => .inl ?_)
    have h3 := sz_arg_lt y a
    rw [← eb] at h3
    have h4 := hb.2
    omega
  · obtain ⟨hp, c, hs, hc⟩ := hD t h
    exact ⟨hp, .inl ⟨c, hs, .inl hc⟩⟩

/-- **Theorem N12, scheme 5** (`S (S (S p) (S n p)) p`): there are no sets `A ≠ ∅`, `B`, `C`,
`D` with `A: [B, A]`, `B: [D, C]`, `D: [A]`, `C: [σ, A]`. -/
theorem thm_N12_5 {M : Nat} {A B C D : Term → Prop} (hM : 1 ≤ M) (hA : HasTy2 A B A)
    (hB : HasTy2 B D C) (hD : HasTy1 D A) (hC : HasTy2 C (SmallNf M) A) : ∀ t, ¬ A t := by
  have nnA := nn_self hA
  have nnD := hD.nn nnA
  have dCB : ∀ t, C t → B t → False := disj_first hC hB (fun t h1 h2 => nnD t h2 h1.1)
  have dDB : ∀ t, D t → B t → False := disj_kind hD hB
  have dDA : ∀ t, D t → A t → False := disj_kind hD hA
  have dAB : ∀ t, A t → B t → False := disj_first hA hB (fun t h1 h2 => dDB t h2 h1)
  have hP : ∀ y u, A (y ⬝ u) → B u → M + 1 < sz u → False := by
    refine claim_P hM hA hB dAB dDB dCB ?_ ?_ ?_ ?_
    · intro a' u hu _ h1 _
      exact dAB u (lemma_AP3 hD h1).2 hu
    · intro p q hp _ h1 _
      have e := (lemma_AP3 hD h1).1
      rw [e] at hp
      have e1S : sz S = 1 := rfl
      omega
    · intro a' g p _ _ hs h1 _
      exact hB.not_S (hA.items (lemma_AP3 hD h1).2 hs).1
    · intro a' g p hPF _ _ h1 h2
      have hAq := (lemma_AP3 hD h1).2
      have h3 := hPF.1
      have h4 := sz_arg_lt g p
      have h5 := sz_arg_lt a' (g ⬝ p)
      obtain ⟨c, e, _, _⟩ := lemma_AP1 hC h2 (by omega)
      rw [e] at hAq
      exact hA.not_S1 c hAq
  refine fun t h => thm_Xplus (M := M + 1) (Z := fun t => A t ∨ B t ∨ C t ∨ D t) ?_ t (.inl h)
  rintro t (h | h | h | h)
  · obtain ⟨hp, a, b, hs, ha, hb⟩ := hA t h
    refine xp_mem hp hs (.inl (.inr (.inl ha))) (.inl (.inl hb)) (.inl (.inr (.inl ha)))
      (fun y eb => .inl ?_)
    rw [eb] at hb
    exact first_A hP hb ha
  · obtain ⟨hp, a, b, hs, ha, hb⟩ := hB t h
    refine xp_mem hp hs (.inl (.inr (.inr (.inr ha)))) (.inl (.inr (.inr (.inl hb))))
      (.inl (.inr (.inr (.inr ha)))) (fun y eb => .inl ?_)
    rw [eb] at hb
    rcases Nat.lt_or_ge (M + 1) (sz a) with big | le
    · obtain ⟨_, _, _, h'⟩ := lemma_AP1 hC hb big
      exact (dDA a ha h').elim
    · exact le
  · obtain ⟨hp, a, b, hs, ha, hb⟩ := hC t h
    exact xp_mem hp hs (.inr (Nat.le_succ_of_le ha.2)) (.inl (.inl hb)) (.inr (.inl hb))
      (fun _ _ => .inl (Nat.le_succ_of_le ha.2))
  · obtain ⟨hp, c, hs, hc⟩ := hD t h
    exact ⟨hp, .inl ⟨c, hs, .inl hc⟩⟩

/-- **Theorem N12, scheme 6** (`S (S (S p) (S p n)) p`): there are no sets `A ≠ ∅`, `B`, `C`,
`D` with `A: [B, A]`, `B: [D, C]`, `D: [A]`, `C: [A, σ]`. -/
theorem thm_N12_6 {M : Nat} {A B C D : Term → Prop} (hM : 1 ≤ M) (hA : HasTy2 A B A)
    (hB : HasTy2 B D C) (hD : HasTy1 D A) (hC : HasTy2 C A (SmallNf M)) : ∀ t, ¬ A t := by
  have nnA := nn_self hA
  have nnC := hC.nn_left nnA
  have dCB : ∀ t, C t → B t → False := disj_second hC hB (fun t h1 h2 => nnC t h2 h1.1)
  have dDB : ∀ t, D t → B t → False := disj_kind hD hB
  have dAB : ∀ t, A t → B t → False := disj_first hA hB (fun t h1 h2 => dDB t h2 h1)
  have hP : ∀ y u, A (y ⬝ u) → B u → M + 1 < sz u → False := by
    refine claim_P hM hA hB dAB dDB dCB ?_ ?_ ?_ ?_
    · intro a' u hu _ h1 _
      exact dAB u (lemma_AP3 hD h1).2 hu
    · intro p q hp _ h1 _
      have e := (lemma_AP3 hD h1).1
      rw [e] at hp
      have e1S : sz S = 1 := rfl
      omega
    · intro a' g p _ _ hs h1 _
      exact hB.not_S (hA.items (lemma_AP3 hD h1).2 hs).1
    · intro a' g p hPF _ _ _ h2
      have h3 := hPF.1
      have h4 := sz_arg_lt g p
      have h5 := sz_arg_lt a' (g ⬝ p)
      have h6 := lemma_AP2 hC h2
      omega
  refine fun t h => thm_Xplus (M := M + 1) (Z := fun t => A t ∨ B t ∨ C t ∨ D t) ?_ t (.inl h)
  rintro t (h | h | h | h)
  · obtain ⟨hp, a, b, hs, ha, hb⟩ := hA t h
    refine xp_mem hp hs (.inl (.inr (.inl ha))) (.inl (.inl hb)) (.inl (.inr (.inl ha)))
      (fun y eb => .inl ?_)
    rw [eb] at hb
    exact first_A hP hb ha
  · obtain ⟨hp, a, b, hs, ha, hb⟩ := hB t h
    refine xp_mem hp hs (.inl (.inr (.inr (.inr ha)))) (.inl (.inr (.inr (.inl hb))))
      (.inl (.inr (.inr (.inr ha)))) (fun y eb => .inl ?_)
    rw [eb] at hb
    exact Nat.le_succ_of_le (lemma_AP2 hC hb)
  · obtain ⟨hp, a, b, hs, ha, hb⟩ := hC t h
    refine xp_mem hp hs (.inl (.inl ha)) (.inr (Nat.le_succ_of_le hb.2)) (.inl (.inl ha))
      (fun y eb => .inl ?_)
    have h3 := sz_arg_lt y a
    rw [← eb] at h3
    have h4 := hb.2
    omega
  · obtain ⟨hp, c, hs, hc⟩ := hD t h
    exact ⟨hp, .inl ⟨c, hs, .inl hc⟩⟩

/-- **Theorem N12, scheme 7** (`S (S p (S n p)) p`): there are no sets `A ≠ ∅`, `B`, `C` with
`A: [B, A]`, `B: [A, C]`, `C: [σ, A]`.  Here a non-literal member of `B` with a large first item
`z` has the second item `S c z`, `sz c ≤ M`: the exceptional members of Theorem X⁺. -/
theorem thm_N12_7 {M : Nat} {A B C : Term → Prop} (hM : 1 ≤ M) (hA : HasTy2 A B A)
    (hB : HasTy2 B A C) (hC : HasTy2 C (SmallNf M) A) : ∀ t, ¬ A t := by
  have nnA := nn_self hA
  have nnB := hB.nn_left nnA
  have dCB : ∀ t, C t → B t → False := disj_first hC hB (fun t h1 h2 => nnA t h2 h1.1)
  have dAC : ∀ t, A t → C t → False := disj_first hA hC (fun t h1 h2 => nnB t h1 h2.1)
  have dAB : ∀ t, A t → B t → False := disj_second hA hB (fun t h1 h2 => dAC t h1 h2)
  have hP : ∀ y u, A (y ⬝ u) → B u → M + 1 < sz u → False := by
    refine claim_P hM hA hB dAB dAB dCB ?_ ?_ ?_ ?_
    · intro a' u hu hbig _ h2
      have h3 := sz_arg_lt a' u
      obtain ⟨c, e, _, _⟩ := lemma_AP1 hC h2 (by omega)
      rw [e] at hu
      exact hB.not_S1 c hu
    · intro p q hp hpq _ h2
      have h3 := sz_arg_lt p q
      have h4 := lemma_AP1_sz hC h2 (by omega)
      omega
    · intro a' g p hPF hpp hs _ h2
      have h0 := sz_arg_lt g p
      have h3 := hPF.1
      have hsm := lemma_AP1_sz hC h2 (by omega)
      have e1S : sz S = 1 := rfl
      exact hA.not_S (hB.items (pform_small hM hPF hpp hs (by omega) hsm) hs).1
    · intro a' g p hPF _ _ _ h2
      have h3 := hPF.1
      have h4 := sz_arg_lt g p
      have h5 := sz_arg_lt a' (g ⬝ p)
      have h6 := lemma_AP1_sz hC h2 (by omega)
      omega
  refine fun t h => thm_Xplus (M := M + 1) (Z := fun t => A t ∨ B t ∨ C t) ?_ t (.inl h)
  rintro t (h | h | h)
  · obtain ⟨hp, a, b, hs, ha, hb⟩ := hA t h
    refine xp_mem hp hs (.inl (.inr (.inl ha))) (.inl (.inl hb)) (.inl (.inr (.inl ha)))
      (fun y eb => .inl ?_)
    rw [eb] at hb
    exact first_A hP hb ha
  · obtain ⟨hp, a, b, hs, ha, hb⟩ := hB t h
    refine xp_mem hp hs (.inl (.inl ha)) (.inl (.inr (.inr hb))) (.inl (.inl ha))
      (fun y eb => ?_)
    rw [eb] at hb
    rcases Nat.lt_or_ge (M + 1) (sz a) with big | le
    · obtain ⟨c, e, hc, _⟩ := lemma_AP1 hC hb big
      exact .inr (.inr ⟨c, Nat.le_succ_of_le hc, e⟩)
    · exact .inl le
  · obtain ⟨hp, a, b, hs, ha, hb⟩ := hC t h
    exact xp_mem hp hs (.inr (Nat.le_succ_of_le ha.2)) (.inl (.inl hb)) (.inr (.inl hb))
      (fun _ _ => .inl (Nat.le_succ_of_le ha.2))

/-- **Theorem N12, scheme 8** (`S (S p (S p n)) p`): there are no sets `A ≠ ∅`, `B`, `C` with
`A: [B, A]`, `B: [A, C]`, `C: [A, σ]`. -/
theorem thm_N12_8 {M : Nat} {A B C : Term → Prop} (hM : 1 ≤ M) (hA : HasTy2 A B A)
    (hB : HasTy2 B A C) (hC : HasTy2 C A (SmallNf M)) : ∀ t, ¬ A t := by
  have nnA := nn_self hA
  have nnC := hC.nn_left nnA
  have dCB : ∀ t, C t → B t → False := disj_second hC hB (fun t h1 h2 => nnC t h2 h1.1)
  have dAC : ∀ t, A t → C t → False := disj_second hA hC (fun t h1 h2 => nnA t h1 h2.1)
  have dAB : ∀ t, A t → B t → False := disj_second hA hB (fun t h1 h2 => dAC t h1 h2)
  have hP : ∀ y u, A (y ⬝ u) → B u → M + 1 < sz u → False := by
    refine claim_P hM hA hB dAB dAB dCB ?_ ?_ ?_ ?_
    · intro a' u _ hbig _ h2
      have h3 := sz_arg_lt a' u
      have h4 := lemma_AP2 hC h2
      omega
    · intro p q hp _ _ h2
      have h3 := sz_fun_lt p q
      have h4 := lemma_AP2 hC h2
      omega
    · intro a' g p hPF _ _ _ h2
      have h3 := hPF.1
      have h4 := sz_arg_lt g p
      have h5 := lemma_AP2 hC h2
      omega
    · intro a' g p hPF _ _ _ h2
      have h3 := hPF.1
      have h4 := sz_arg_lt g p
      have h5 := sz_arg_lt a' (g ⬝ p)
      have h6 := lemma_AP2 hC h2
      omega
  refine fun t h => thm_Xplus (M := M + 1) (Z := fun t => A t ∨ B t ∨ C t) ?_ t (.inl h)
  rintro t (h | h | h)
  · obtain ⟨hp, a, b, hs, ha, hb⟩ := hA t h
    refine xp_mem hp hs (.inl (.inr (.inl ha))) (.inl (.inl hb)) (.inl (.inr (.inl ha)))
      (fun y eb => .inl ?_)
    rw [eb] at hb
    exact first_A hP hb ha
  · obtain ⟨hp, a, b, hs, ha, hb⟩ := hB t h
    refine xp_mem hp hs (.inl (.inl ha)) (.inl (.inr (.inr hb))) (.inl (.inl ha))
      (fun y eb => .inl ?_)
    rw [eb] at hb
    exact Nat.le_succ_of_le (lemma_AP2 hC hb)
  · obtain ⟨hp, a, b, hs, ha, hb⟩ := hC t h
    refine xp_mem hp hs (.inl (.inl ha)) (.inr (Nat.le_succ_of_le hb.2)) (.inl (.inl ha))
      (fun y eb => .inl ?_)
    have h3 := sz_arg_lt y a
    rw [← eb] at h3
    have h4 := hb.2
    omega

/-! ## Conversion classes ((Eq) of the note) -/

/-- The conversion class of `r` among the closed S-terms. -/
def Cls (r : Term) (t : Term) : Prop := PureS t ∧ Convertible t r

theorem cls2 {r r₁ r₂ : Term} (h₁ : PureS r₁) (h₂ : PureS r₂)
    (h : Convertible r (S ⬝ r₁ ⬝ r₂)) : HasTy2 (Cls r) (Cls r₁) (Cls r₂) := by
  rintro t ⟨ht, hct⟩
  obtain ⟨a, b, hs, ca, cb⟩ := hnf2_conv ht h₁ h₂ (hct.trans h)
  have hpab := steps_pure ht hs
  exact ⟨ht, a, b, hs, ⟨hpab.app_inv.1.app_inv.2, ca⟩, ⟨hpab.app_inv.2, cb⟩⟩

theorem cls2_left {M : Nat} {r n nf r₂ : Term} (hn : PureS n) (hnnf : WSteps n nf)
    (hnf : Normal nf) (hM : sz nf ≤ M) (h₂ : PureS r₂) (h : Convertible r (S ⬝ n ⬝ r₂)) :
    HasTy2 (Cls r) (SmallNf M) (Cls r₂) := by
  rintro t ⟨ht, hct⟩
  obtain ⟨m, a, hs, hpa, ca, hm, hsz⟩ := hnf2_conv_left ht h₂ hn hnnf hnf (hct.trans h)
  exact ⟨ht, m, a, hs, ⟨hm, Nat.le_trans hsz hM⟩, hpa, ca⟩

theorem cls2_right {M : Nat} {r n nf r₁ : Term} (h₁ : PureS r₁) (hn : PureS n)
    (hnnf : WSteps n nf) (hnf : Normal nf) (hM : sz nf ≤ M)
    (h : Convertible r (S ⬝ r₁ ⬝ n)) : HasTy2 (Cls r) (Cls r₁) (SmallNf M) := by
  rintro t ⟨ht, hct⟩
  obtain ⟨a, m, hs, hpa, ca, hm, hsz⟩ := hnf2_conv_right ht h₁ hn hnnf hnf (hct.trans h)
  exact ⟨ht, a, m, hs, ⟨hpa, ca⟩, hm, Nat.le_trans hsz hM⟩

theorem cls1 {r r₁ : Term} (h₁ : PureS r₁) (h : Convertible r (S ⬝ r₁)) :
    HasTy1 (Cls r) (Cls r₁) := by
  rintro t ⟨ht, hct⟩
  obtain ⟨c, e, cc⟩ := hnf1_conv ht h₁ (hct.trans h)
  have hpc : PureS c := by
    rw [e] at ht
    exact ht.app_inv.2
  exact ⟨ht, c, by rw [e]; exact .refl _, hpc, cc⟩

/-! ## Theorem N12: the eight equations -/

/-- `p` is not convertible to `S (S (S n p) p) p`, for closed `p` and closed normalizing `n`. -/
theorem no_S_SSnpp_p {p n : Term} (hp : PureS p) (hn : PureS n) (hnn : Normalizing n) :
    ¬ Convertible p (S ⬝ (S ⬝ (S ⬝ n ⬝ p) ⬝ p) ⬝ p) := by
  intro hc
  obtain ⟨nf, hnnf, hnf⟩ := hnn
  have hpC : PureS (S ⬝ n ⬝ p) := .app (.app .S hn) hp
  have hpB : PureS (S ⬝ (S ⬝ n ⬝ p) ⬝ p) := .app (.app .S hpC) hp
  exact thm_N12_1 (M := sz nf) (sz_pos nf) (cls2 hpB hp hc) (cls2 hpC hp (Convertible.refl _))
    (cls2_left hn hnnf hnf (Nat.le_refl _) hp (Convertible.refl _)) p ⟨hp, Convertible.refl p⟩

/-- `p` is not convertible to `S (S (S p n) p) p`, for closed `p` and closed normalizing `n`. -/
theorem no_S_SSpnp_p {p n : Term} (hp : PureS p) (hn : PureS n) (hnn : Normalizing n) :
    ¬ Convertible p (S ⬝ (S ⬝ (S ⬝ p ⬝ n) ⬝ p) ⬝ p) := by
  intro hc
  obtain ⟨nf, hnnf, hnf⟩ := hnn
  have hpC : PureS (S ⬝ p ⬝ n) := .app (.app .S hp) hn
  have hpB : PureS (S ⬝ (S ⬝ p ⬝ n) ⬝ p) := .app (.app .S hpC) hp
  exact thm_N12_2 (M := sz nf) (sz_pos nf) (cls2 hpB hp hc) (cls2 hpC hp (Convertible.refl _))
    (cls2_right hp hn hnnf hnf (Nat.le_refl _) (Convertible.refl _)) p ⟨hp, Convertible.refl p⟩

/-- `p` is not convertible to `S (S (S n p) (S p)) p`, for closed `p` and closed normalizing
`n`. -/
theorem no_S_SSnpSp_p {p n : Term} (hp : PureS p) (hn : PureS n) (hnn : Normalizing n) :
    ¬ Convertible p (S ⬝ (S ⬝ (S ⬝ n ⬝ p) ⬝ (S ⬝ p)) ⬝ p) := by
  intro hc
  obtain ⟨nf, hnnf, hnf⟩ := hnn
  have hpC : PureS (S ⬝ n ⬝ p) := .app (.app .S hn) hp
  have hpD : PureS (S ⬝ p) := .app .S hp
  have hpB : PureS (S ⬝ (S ⬝ n ⬝ p) ⬝ (S ⬝ p)) := .app (.app .S hpC) hpD
  exact thm_N12_3 (M := sz nf) (sz_pos nf) (cls2 hpB hp hc) (cls2 hpC hpD (Convertible.refl _))
    (cls2_left hn hnnf hnf (Nat.le_refl _) hp (Convertible.refl _))
    (cls1 hp (Convertible.refl _)) p ⟨hp, Convertible.refl p⟩

/-- `p` is not convertible to `S (S (S p n) (S p)) p`, for closed `p` and closed normalizing
`n`. -/
theorem no_S_SSpnSp_p {p n : Term} (hp : PureS p) (hn : PureS n) (hnn : Normalizing n) :
    ¬ Convertible p (S ⬝ (S ⬝ (S ⬝ p ⬝ n) ⬝ (S ⬝ p)) ⬝ p) := by
  intro hc
  obtain ⟨nf, hnnf, hnf⟩ := hnn
  have hpC : PureS (S ⬝ p ⬝ n) := .app (.app .S hp) hn
  have hpD : PureS (S ⬝ p) := .app .S hp
  have hpB : PureS (S ⬝ (S ⬝ p ⬝ n) ⬝ (S ⬝ p)) := .app (.app .S hpC) hpD
  exact thm_N12_4 (M := sz nf) (sz_pos nf) (cls2 hpB hp hc) (cls2 hpC hpD (Convertible.refl _))
    (cls2_right hp hn hnnf hnf (Nat.le_refl _) (Convertible.refl _))
    (cls1 hp (Convertible.refl _)) p ⟨hp, Convertible.refl p⟩

/-- `p` is not convertible to `S (S (S p) (S n p)) p`, for closed `p` and closed normalizing
`n`. -/
theorem no_S_SSpSnp_p {p n : Term} (hp : PureS p) (hn : PureS n) (hnn : Normalizing n) :
    ¬ Convertible p (S ⬝ (S ⬝ (S ⬝ p) ⬝ (S ⬝ n ⬝ p)) ⬝ p) := by
  intro hc
  obtain ⟨nf, hnnf, hnf⟩ := hnn
  have hpC : PureS (S ⬝ n ⬝ p) := .app (.app .S hn) hp
  have hpD : PureS (S ⬝ p) := .app .S hp
  have hpB : PureS (S ⬝ (S ⬝ p) ⬝ (S ⬝ n ⬝ p)) := .app (.app .S hpD) hpC
  exact thm_N12_5 (M := sz nf) (sz_pos nf) (cls2 hpB hp hc) (cls2 hpD hpC (Convertible.refl _))
    (cls1 hp (Convertible.refl _))
    (cls2_left hn hnnf hnf (Nat.le_refl _) hp (Convertible.refl _)) p ⟨hp, Convertible.refl p⟩

/-- `p` is not convertible to `S (S (S p) (S p n)) p`, for closed `p` and closed normalizing
`n`. -/
theorem no_S_SSpSpn_p {p n : Term} (hp : PureS p) (hn : PureS n) (hnn : Normalizing n) :
    ¬ Convertible p (S ⬝ (S ⬝ (S ⬝ p) ⬝ (S ⬝ p ⬝ n)) ⬝ p) := by
  intro hc
  obtain ⟨nf, hnnf, hnf⟩ := hnn
  have hpC : PureS (S ⬝ p ⬝ n) := .app (.app .S hp) hn
  have hpD : PureS (S ⬝ p) := .app .S hp
  have hpB : PureS (S ⬝ (S ⬝ p) ⬝ (S ⬝ p ⬝ n)) := .app (.app .S hpD) hpC
  exact thm_N12_6 (M := sz nf) (sz_pos nf) (cls2 hpB hp hc) (cls2 hpD hpC (Convertible.refl _))
    (cls1 hp (Convertible.refl _))
    (cls2_right hp hn hnnf hnf (Nat.le_refl _) (Convertible.refl _)) p ⟨hp, Convertible.refl p⟩

/-- `p` is not convertible to `S (S p (S n p)) p`, for closed `p` and closed normalizing `n`. -/
theorem no_S_SpSnp_p {p n : Term} (hp : PureS p) (hn : PureS n) (hnn : Normalizing n) :
    ¬ Convertible p (S ⬝ (S ⬝ p ⬝ (S ⬝ n ⬝ p)) ⬝ p) := by
  intro hc
  obtain ⟨nf, hnnf, hnf⟩ := hnn
  have hpC : PureS (S ⬝ n ⬝ p) := .app (.app .S hn) hp
  have hpB : PureS (S ⬝ p ⬝ (S ⬝ n ⬝ p)) := .app (.app .S hp) hpC
  exact thm_N12_7 (M := sz nf) (sz_pos nf) (cls2 hpB hp hc) (cls2 hp hpC (Convertible.refl _))
    (cls2_left hn hnnf hnf (Nat.le_refl _) hp (Convertible.refl _)) p ⟨hp, Convertible.refl p⟩

/-- `p` is not convertible to `S (S p (S p n)) p`, for closed `p` and closed normalizing `n`. -/
theorem no_S_SpSpn_p {p n : Term} (hp : PureS p) (hn : PureS n) (hnn : Normalizing n) :
    ¬ Convertible p (S ⬝ (S ⬝ p ⬝ (S ⬝ p ⬝ n)) ⬝ p) := by
  intro hc
  obtain ⟨nf, hnnf, hnf⟩ := hnn
  have hpC : PureS (S ⬝ p ⬝ n) := .app (.app .S hp) hn
  have hpB : PureS (S ⬝ p ⬝ (S ⬝ p ⬝ n)) := .app (.app .S hp) hpC
  exact thm_N12_8 (M := sz nf) (sz_pos nf) (cls2 hpB hp hc) (cls2 hp hpC (Convertible.refl _))
    (cls2_right hp hn hnnf hnf (Nat.le_refl _) (Convertible.refl _)) p ⟨hp, Convertible.refl p⟩

end Ncfp
