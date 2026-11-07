import Ski.CantorTotal

open Term

/-!
# The fan step at ℕ∞: totality at ∞ gives a modulus

`NatLift.nat_lift` lifts every m-local `f : Nat → Bool`.  This module shows that
m-locality is no stronger than totality on the points of ℕ∞: a function total
on the numerals *and at the infinite numeral* is m-local for some `m`
(`nat_fan`).  So, as a statement about classes, the line between lift and no
lift is totality at ∞:

- `nat_lift_inf`: `natL` lifts every `f` total on the numerals and at `ω`;
- `NatLift.no_lift_local_plus_one`: no closed term lifts them together with
  `G ω`, which is total on the numerals and has no value at `ω`.

Not proved: that adding *any* single function without a value at `ω` defeats
every lift.

The proof generalizes `NoLift.sim` in two ways.
- **The right side.** `RelW` relates an infinite numeral to *any* term with
  enough successor layers (`NatLift.AtLeast`), not only to numerals.  The right
  side then only needs weak reduction.
- **The target.** `simW` follows a head run to *any* weak head normal form `v`
  and returns a related `v'`.  A run to `K ⬝ I` ends at some `K ⬝ x` with
  `x ↠ I`, and `x`'s own run is simulated in turn.

The values at the numerals below the modulus come from totality by finite
choice, without the axiom of choice (`finite_choice`).
-/

namespace NatFan

open NoLift LiftBool Search CantorLift NatLift

-- ---------------------------------------------------------------------------
-- Spines under weak reduction
-- ---------------------------------------------------------------------------

theorem wsteps_spine {u v : Term} (h : WSteps u v) : ∀ r, WSteps (spineApp u r) (spineApp v r)
  | [] => h
  | a :: r => wsteps_spine (WSteps.left a h) r

-- ---------------------------------------------------------------------------
-- The relation
-- ---------------------------------------------------------------------------

/-- `RelW b t t'`: `t'` is `t` with some infinite numerals replaced by terms with
    at least `b` successor layers. -/
inductive RelW (b : Nat) : Term → Term → Prop
  | refl (t : Term) : RelW b t t
  | omega {z u : Term} (hz : Steps z (fixB succS)) {m : Nat} (hm : b ≤ m) (hu : AtLeast m u) :
      RelW b (omegaT z) u
  | app {f f' x x' : Term} : RelW b f f' → RelW b x x' → RelW b (f ⬝ x) (f' ⬝ x')

theorem RelW.mono {b b' : Nat} (hb : b' ≤ b) {t t' : Term} : RelW b t t' → RelW b' t t'
  | .refl t => .refl t
  | .omega hz hm hu => .omega hz (Nat.le_trans hb hm) hu
  | .app hf hx => .app (hf.mono hb) (hx.mono hb)

inductive HeadW (b : Nat) : Term → Term → Prop
  | leaf {h : Term} (hl : h = S ∨ h = K ∨ h = I) : HeadW b h h
  | omega {z u : Term} (hz : Steps z (fixB succS)) {m : Nat} (hm : b ≤ m) (hu : AtLeast m u) :
      HeadW b (omegaT z) u

theorem relW_spineApp {b : Nat} {u u' : Term} (hu : RelW b u u') :
    ∀ {r r' : List Term}, Pairs (RelW b) r r' → RelW b (spineApp u r) (spineApp u' r')
  | [], [], .nil => hu
  | _ :: _, _ :: _, .cons ha hr => relW_spineApp (.app hu ha) hr

theorem pairsW_refl {b : Nat} : ∀ r : List Term, Pairs (RelW b) r r
  | [] => .nil
  | a :: r => .cons (.refl a) (pairsW_refl r)

theorem pairsW_append {b : Nat} {r r' : List Term} (hr : Pairs (RelW b) r r')
    {x x' : Term} (hx : RelW b x x') : Pairs (RelW b) (r ++ [x]) (r' ++ [x']) := by
  induction hr with
  | nil => exact .cons hx .nil
  | cons ha _ ih => exact .cons ha ih

theorem pairsW_mono {b b' : Nat} (hb : b' ≤ b) {r r' : List Term}
    (hr : Pairs (RelW b) r r') : Pairs (RelW b') r r' := by
  induction hr with
  | nil => exact .nil
  | cons ha _ ih => exact .cons (ha.mono hb) ih

theorem RelW.spine {b : Nat} {t t' : Term} (h : RelW b t t') :
    ∃ hd hd' r r', HeadW b hd hd' ∧ Pairs (RelW b) r r' ∧
      t = spineApp hd r ∧ t' = spineApp hd' r' := by
  induction h with
  | refl t =>
    obtain ⟨hd, r, hl, rfl⟩ := leaf_spine t
    exact ⟨hd, hd, r, r, .leaf hl, pairsW_refl r, rfl, rfl⟩
  | omega hz hm hu => exact ⟨_, _, [], [], .omega hz hm hu, .nil, rfl, rfl⟩
  | app _ hx ih _ =>
    obtain ⟨hd, hd', r, r', hh, hr, rfl, rfl⟩ := ih
    exact ⟨hd, hd', r ++ [_], r' ++ [_], hh, pairsW_append hr hx,
      (spineApp_append _ _ _).symm, (spineApp_append _ _ _).symm⟩

-- ---------------------------------------------------------------------------
-- The infinite numeral with few arguments, explicitly
-- ---------------------------------------------------------------------------

/-- `M = S (K (S I)) K`, `succS = S (K K) M`. -/
def Mt : Term := S ⬝ (K ⬝ (S ⬝ I)) ⬝ K

theorem omega_head0 {z : Term} (hz : Steps z (fixB succS)) :
    Steps (omegaT z) (K ⬝ (Mt ⬝ omegaT (I ⬝ z))) :=
  (fixSelf_unroll (F := succS) hz).trans (iter_sound (k := 2) rfl)

theorem omega_head1 {z : Term} (hz : Steps z (fixB succS)) (a : Term) :
    Steps (omegaT z ⬝ a) (S ⬝ I ⬝ (K ⬝ omegaT (I ⬝ z))) :=
  (Steps.left a (fixSelf_unroll (F := succS) hz)).trans (iter_sound (k := 5) rfl)

theorem succ_whnf0 (x : Term) : WSteps (succS ⬝ x) (K ⬝ (Mt ⬝ x)) :=
  (iter_sound (k := 2) rfl : Steps (succS ⬝ x) (K ⬝ (Mt ⬝ x))).weak

theorem succ_whnf1 (x a : Term) : WSteps (succS ⬝ x ⬝ a) (S ⬝ I ⬝ (K ⬝ x)) :=
  (iter_sound (k := 5) rfl : Steps (succS ⬝ x ⬝ a) (S ⬝ I ⬝ (K ⬝ x))).weak

theorem atLeast_pos {m : Nat} {u : Term} (hm : 1 ≤ m) (hu : AtLeast m u) :
    ∃ u', WSteps u (succS ⬝ u') ∧ AtLeast (m - 1) u' := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  exact hu

-- ---------------------------------------------------------------------------
-- The general simulation
-- ---------------------------------------------------------------------------

/-- **The simulation, to any weak head normal form.**  If `t` head-reduces to a
    whnf `v` in `n < b` steps and `RelW b t t'`, then `t'` weakly reduces to some
    `v'` related to `v` at `b - n`. -/
theorem simW : ∀ (fuel n : Nat) {t t' v : Term} {b : Nat}, n ≤ fuel →
    RelW b t t' → StepsN n t v → Whnf v → n < b → ∃ v', WSteps t' v' ∧ RelW (b - n) v v' := by
  intro fuel
  induction fuel with
  | zero =>
    intro n t t' v b hf hrel hn hv hb
    obtain rfl : n = 0 := by omega
    cases hn
    exact ⟨t', .refl _, by simpa using hrel⟩
  | succ fuel ihf =>
  intro n t t' v b hf hrel hn hv hb
  have ih : ∀ m, m < n → ∀ {t t' : Term} {b : Nat}, RelW b t t' → StepsN m t v → m < b →
      ∃ v', WSteps t' v' ∧ RelW (b - m) v v' :=
    fun m hm _ _ _ hr hs hb' => ihf m (by omega) hr hs hv hb'
  -- a whnf `t` stops the run at once
  have stop : Whnf t → ∃ v', WSteps t' v' ∧ RelW (b - n) v v' := fun ht => by
    cases hn with
    | refl => exact ⟨t', .refl _, by simpa using hrel⟩
    | step h _ => exact (ht.no_step h).elim
  obtain ⟨hd, hd', r, r', hh, hr, rfl, rfl⟩ := hrel.spine
  cases hh with
  | leaf hl =>
    -- one head step on both sides, then the induction hypothesis
    have lock : ∀ {u u' : Term}, Step (spineApp hd r) u → Step (spineApp hd r') u' → RelW b u u' →
        ∃ v', WSteps (spineApp hd r') v' ∧ RelW (b - n) v v' := by
      intro u u' h h' hu
      obtain ⟨m, rfl, hm⟩ := stepsN_after hn hv h
      obtain ⟨v', hv', hrel'⟩ := ih m (by omega) hu hm (by omega)
      exact ⟨v', (WSteps.single h'.weak).trans hv', hrel'.mono (by omega)⟩
    rcases hl with rfl | rfl | rfl
    · cases hr with
      | nil => exact stop .S
      | cons ha hr =>
        cases hr with
        | nil => exact stop (.S1 _)
        | cons hb' hr =>
          cases hr with
          | nil => exact stop (.S2 _ _)
          | cons hc hrest =>
            exact lock (step_spine (.S _ _ _) _) (step_spine (.S _ _ _) _)
              (relW_spineApp (.app (.app ha hc) (.app hb' hc)) hrest)
    · cases hr with
      | nil => exact stop .K
      | cons ha hr =>
        cases hr with
        | nil => exact stop (.K1 _)
        | cons _ hrest =>
          exact lock (step_spine (.K _ _) _) (step_spine (.K _ _) _) (relW_spineApp ha hrest)
    · cases hr with
      | nil => exact stop .I
      | cons ha hrest =>
        exact lock (step_spine (.I _) _) (step_spine (.I _) _) (relW_spineApp ha hrest)
  | @omega z u hz m hm hu =>
    -- the run takes at least one step, so `m ≥ b > n ≥ 1`
    have hn1 : 1 ≤ n := by
      cases hn with
      | refl => exact (hv.no_step (step_spine (.left z (.K _ _)) _)).elim
      | step _ _ => omega
    obtain ⟨u1, hu1, hu1'⟩ := atLeast_pos (by omega) hu
    have hpair : RelW (b - n) (omegaT (I ⬝ z)) u1 :=
      .omega (.step (.I _) hz) (by omega) hu1'
    cases hr with
    | nil =>
      have h0 := omega_head0 hz
      rw [steps_whnf_det hn.steps hv h0 (.K1 _)]
      exact ⟨_, hu1.trans (succ_whnf0 u1), .app (.refl K) (.app (.refl Mt) hpair)⟩
    | cons ha hr =>
      cases hr with
      | nil =>
        rename_i a a'
        have h1 := omega_head1 hz a
        rw [steps_whnf_det hn.steps hv h1 (.S2 _ _)]
        exact ⟨_, (WSteps.left _ hu1).trans (succ_whnf1 u1 _),
          .app (.refl (S ⬝ I)) (.app (.refl K) hpair)⟩
      | cons hs hrest =>
        rename_i a a' s s' rest rest'
        obtain ⟨h1, h2⟩ := omega_steps hz a s
        obtain ⟨n', hn', hrun⟩ := stepsN_through_lt hn hv (step_spine h1 rest) (steps_spine h2 rest)
        have hright : WSteps (spineApp hd' (a' :: s' :: rest')) (spineApp (s' ⬝ (K ⬝ u1 ⬝ s')) rest') :=
          (wsteps_spine (WSteps.left _ (WSteps.left _ hu1)) rest').trans
            (steps_spine (succS_steps _ _ _) rest').weak
        have hrel' : RelW (b - 1) (spineApp (s ⬝ (K ⬝ omegaT (I ⬝ z) ⬝ s)) rest)
            (spineApp (s' ⬝ (K ⬝ u1 ⬝ s')) rest') :=
          relW_spineApp (.app (hs.mono (Nat.sub_le _ _))
              (.app (.app (.refl K) (.omega (.step (.I _) hz) (by omega) hu1')) (hs.mono (Nat.sub_le _ _))))
            (pairsW_mono (Nat.sub_le _ _) hrest)
        obtain ⟨v', hv', hrv⟩ := ih n' hn' hrel' hrun (by omega)
        exact ⟨v', hright.trans hv', hrv.mono (by omega)⟩

theorem simW' (n : Nat) {t t' v : Term} {b : Nat} (hrel : RelW b t t') (hn : StepsN n t v)
    (hv : Whnf v) (hb : n < b) : ∃ v', WSteps t' v' ∧ RelW (b - n) v v' :=
  simW n n (Nat.le_refl _) hrel hn hv hb

-- ---------------------------------------------------------------------------
-- Inversions
-- ---------------------------------------------------------------------------

theorem omegaT_ne_leaf {z : Term} : omegaT z ≠ S ∧ omegaT z ≠ K ∧ omegaT z ≠ I :=
  ⟨fun h => Term.noConfusion h, fun h => Term.noConfusion h, fun h => Term.noConfusion h⟩

theorem relW_K {b : Nat} {v' : Term} (h : RelW b K v') : v' = K := by
  cases h with
  | refl => rfl

theorem relW_I {b : Nat} {v' : Term} (h : RelW b I v') : v' = I := by
  cases h with
  | refl => rfl

theorem relW_Kx {b : Nat} {x v' : Term} (h : RelW b (K ⬝ x) v') : ∃ x', v' = K ⬝ x' ∧ RelW b x x' := by
  cases h with
  | refl => exact ⟨x, rfl, .refl _⟩
  | app hf hx => exact ⟨_, by rw [relW_K hf], hx⟩

-- weak reductions out of a whnf keep its shape

theorem shape_K1 {x u : Term} (h : WSteps (K ⬝ x) u) : ∃ x', u = K ⬝ x' ∧ WSteps x x' := by
  generalize ht : K ⬝ x = t at h
  induction h generalizing x with
  | refl => exact ⟨x, ht.symm, .refl _⟩
  | step h1 _ ih =>
    subst ht
    cases h1 with
    | left _ h => cases h
    | right _ h =>
      obtain ⟨x', hu, hx⟩ := ih rfl
      exact ⟨x', hu, .step h hx⟩

theorem shape_S1 {x u : Term} (h : WSteps (S ⬝ x) u) : ∃ x', u = S ⬝ x' := by
  generalize ht : S ⬝ x = t at h
  induction h generalizing x with
  | refl => exact ⟨x, ht.symm⟩
  | step h1 _ ih =>
    subst ht
    cases h1 with
    | left _ h => cases h
    | right _ h => exact ih rfl

theorem shape_S2 {x y u : Term} (h : WSteps (S ⬝ x ⬝ y) u) : ∃ x' y', u = S ⬝ x' ⬝ y' := by
  generalize ht : S ⬝ x ⬝ y = t at h
  induction h generalizing x y with
  | refl => exact ⟨x, y, ht.symm⟩
  | step h1 _ ih =>
    subst ht
    cases h1 with
    | left _ h =>
      cases h with
      | left _ h => cases h
      | right _ h => exact ih rfl
    | right _ h => exact ih rfl

theorem shape_S {u : Term} (h : WSteps S u) : u = S := by
  cases h with
  | refl => rfl
  | step h _ => cases h

theorem wsteps_from_I {u : Term} (h : WSteps I u) : u = I := by
  cases h with
  | refl => rfl
  | step h _ => cases h

/-- A whnf that reduces to `I` is `I`. -/
theorem whnf_to_I {v : Term} (hv : Whnf v) (h : WSteps v I) : v = I := by
  cases hv with
  | I => rfl
  | S => exact absurd (shape_S h) (by intro h; cases h)
  | K => exact absurd (K_wsteps h) (by intro h; cases h)
  | S1 x => obtain ⟨_, h'⟩ := shape_S1 h; cases h'
  | S2 x y => obtain ⟨_, _, h'⟩ := shape_S2 h; cases h'
  | K1 x => obtain ⟨_, h', _⟩ := shape_K1 h; cases h'

/-- A whnf that reduces to `K ⬝ I` is `K ⬝ x` with `x ↠ I`. -/
theorem whnf_to_KI {v : Term} (hv : Whnf v) (h : WSteps v (K ⬝ I)) : ∃ x, v = K ⬝ x ∧ WSteps x I := by
  cases hv with
  | K1 x =>
    obtain ⟨x', h', hx⟩ := shape_K1 h
    cases h'
    exact ⟨x, rfl, hx⟩
  | I => exact absurd (wsteps_from_I h) (by intro h; cases h)
  | S => exact absurd (shape_S h) (by intro h; cases h)
  | K => exact absurd (K_wsteps h) (by intro h; cases h)
  | S1 x => obtain ⟨_, h'⟩ := shape_S1 h; cases h'
  | S2 x y => obtain ⟨_, _, h'⟩ := shape_S2 h; cases h'

-- ---------------------------------------------------------------------------
-- The fan step
-- ---------------------------------------------------------------------------

/-- **Finite choice**, without the axiom of choice. -/
theorem finite_choice (P : Nat → Bool → Prop) : ∀ m, (∀ c, c < m → ∃ b, P c b) →
    ∃ φ : Nat → Bool, ∀ c, c < m → P c (φ c)
  | 0, _ => ⟨fun _ => false, fun c hc => absurd hc (Nat.not_lt_zero _)⟩
  | m + 1, h => by
    obtain ⟨φ, hφ⟩ := finite_choice P m fun c hc => h c (by omega)
    obtain ⟨b, hb⟩ := h m (by omega)
    refine ⟨fun c => if c = m then b else φ c, fun c hc => ?_⟩
    by_cases hcm : c = m
    · subst hcm; simpa using hb
    · simpa [hcm] using hφ c (by omega)

/-- A head run to a whnf from a weak reduction to a boolean. -/
theorem head_run {t : Term} {b : Bool} (h : WSteps t (boolT b)) :
    ∃ n v, StepsN n t v ∧ Whnf v ∧ WSteps v (boolT b) := by
  have hb : Whnf (boolT b) := by cases b <;> constructor
  obtain ⟨v, ⟨hs, hv⟩, hvb⟩ := eval_back h ⟨.refl _, hb⟩
  obtain ⟨n, hn⟩ := counted hs
  exact ⟨n, v, hn, hv, hvb⟩

/-- **The value at ω extends to every term with enough layers.** -/
theorem fan_value {f : Term} {b : Bool} (hω : WSteps (f ⬝ omega0) (boolT b)) :
    ∃ m, ∀ u, AtLeast m u → WSteps (f ⬝ u) (boolT b) := by
  obtain ⟨n1, v, hn1, hv, hvb⟩ := head_run hω
  have rel : ∀ m u, AtLeast m u → RelW m (f ⬝ omega0) (f ⬝ u) := fun m u hu =>
    .app (.refl f) (.omega (.refl _) (Nat.le_refl _) hu)
  cases b with
  | true =>
    have hvK : v = K := hv.wsteps_K hvb
    subst hvK
    refine ⟨n1 + 1, fun u hu => ?_⟩
    obtain ⟨v', hv', hrel⟩ := simW' n1 (rel _ u hu) hn1 .K (by omega)
    rw [relW_K hrel] at hv'
    exact hv'
  | false =>
    obtain ⟨x, rfl, hx⟩ := whnf_to_KI hv hvb
    -- run `x` to its whnf, which must be `I`
    have hx' : WSteps x I := hx
    obtain ⟨n3, v3, hn3, hv3, hv3I⟩ : ∃ n v, StepsN n x v ∧ Whnf v ∧ WSteps v I := by
      obtain ⟨v, ⟨hs, hv⟩, hvI⟩ := eval_back hx' ⟨.refl _, .I⟩
      obtain ⟨n, hn⟩ := counted hs
      exact ⟨n, v, hn, hv, hvI⟩
    have hv3eq : v3 = I := whnf_to_I hv3 hv3I
    subst hv3eq
    refine ⟨n1 + n3 + 2, fun u hu => ?_⟩
    obtain ⟨v', hv', hrel⟩ := simW' n1 (rel _ u hu) hn1 (.K1 _) (by omega)
    obtain ⟨x', rfl, hxx⟩ := relW_Kx hrel
    obtain ⟨v'', hv'', hrel''⟩ := simW' n3 hxx hn3 .I (by omega)
    rw [relW_I hrel''] at hv''
    exact hv'.trans (WSteps.right K hv'')

/-- **The fan step at ℕ∞.**  A function total on the numerals and at the
    infinite numeral is `m`-local for some `m`. -/
theorem nat_fan {f : Term} (hT : Total f) {b : Bool} (hω : WSteps (f ⬝ omega0) (boolT b)) :
    ∃ m φ, NLocal m φ f := by
  obtain ⟨m, hm⟩ := fan_value hω
  obtain ⟨φ, hφ⟩ := finite_choice (fun c r => WSteps (f ⬝ num c) (boolT r)) m fun c _ => hT c
  refine ⟨m, fun c => if c < m then φ c else b, fun c hc => ?_, fun u hu => ?_⟩
  · simpa [hc] using hφ c hc
  · simpa using hm u hu

/-- **`natL` lifts every function total on the points of ℕ∞**: on the numerals
    and at `ω`. -/
theorem nat_lift_inf {f : Term} (hT : Total f) {b : Bool} (hω : WSteps (f ⬝ omega0) (boolT b)) :
    LiftsAt natL f := by
  obtain ⟨m, φ, hf⟩ := nat_fan hT hω
  exact liftsAt_of_nlocal hf

/-- **The dichotomy at Nat → Bool.**  For a function total on the numerals,
    having a modulus is the same as having a value at `ω`. -/
theorem local_iff_total_inf {f : Term} (hT : Total f) :
    (∃ m φ, NLocal m φ f) ↔ ∃ b : Bool, WSteps (f ⬝ omega0) (boolT b) := by
  constructor
  · rintro ⟨m, φ, hf⟩; exact ⟨φ m, hf.2 _ (omega_atLeast m (.refl _))⟩
  · rintro ⟨b, hb⟩; exact nat_fan hT hb

/-- `natL` lifts every function total on the points of ℕ∞ in the full sense of
    the definition: `natL f` reduces to a code `⟨c⟩`, and `c` agrees with `f` on
    the numerals. -/
theorem nat_lift_inf' {f : Term} (hT : Total f) {b : Bool}
    (hω : WSteps (f ⬝ omega0) (boolT b)) :
    ∃ c, WSteps (natL ⬝ f) (quoteT c) ∧
      ∀ (n : Nat) (r : Bool), WSteps (f ⬝ num n) (boolT r) → WSteps (c ⬝ num n) (boolT r) := by
  obtain ⟨m, φ, hf⟩ := nat_fan hT hω
  exact ⟨_, (nat_lift hf).1, (nat_lift hf).2⟩

/-- **`G ω₀` has no value at `ω₀`**: it is total on the numerals (constantly
    false), so a value at `ω₀` would give it a modulus (`nat_fan`), which it has
    not (`G_omega_not_local`). -/
theorem G_omega_no_value : ¬ ∃ b : Bool, WSteps (G ⬝ omega0 ⬝ omega0) (boolT b) := by
  intro ⟨b, hb⟩
  have hT : Total (G ⬝ omega0) := fun n => ⟨false, G_omega n (Steps.refl _)⟩
  obtain ⟨m, φ, hf⟩ := nat_fan hT hb
  exact G_omega_not_local m φ hf

end NatFan
