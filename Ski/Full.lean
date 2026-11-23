import Ski.Phi
import Ski.GCertSound
import Ski.TopTermMain
open Term

/-!
# Finite index of the full observable (S6, Theorem 9)

Mechanization of Theorem 9 (named `theorem_six` after an earlier draft's numbering) of the S6 paper (`s6-prefix-regularity/main.tex`, Section 4; the
combined invariant R7 of `notes/S4-bounded-exposure.md`).  Setting: closed terms over `S`.

* `PeriodicF 𝔐 N p`: the constants of S6: `N ≥ 10`, `p ≥ 1`, and `σ^j = σ^j'`, `φ^j = φ^j'` for
  `j, j' ≥ N − 2` congruent mod `p`, where `σ a = s·a` (`SModel.sIter`) and `φ (a, b) = (b, a·b)`
  (`SModel.fibM`).  Finiteness of `M` is not assumed for part (a).
* `Psi 𝔐 t a b`: the head run of `t` reaches a stable frame `f w` (`f` without hnf) with
  `a = M f`, `b = M w`.  `ObsF 𝔐 t o`: the full observable `O`, as a relation: `o = .hnf l` if
  the head run reaches an hnf with item values `l`; `o = .bot a b` if `Psi 𝔐 t a b`.  It is a
  total function on closed S-terms (`obsF_total`, `obsF_unique`).  S6 reads `Ψ` at the *first*
  stable frame; every stable frame on the head run gives the same pair (`psi_unique`), and
  `first_stable` gives the first one.
* `coreK`, `coreV`: the core form `t = S^k v`, `v = S` or `v` of at least two items.
* `Base0` (S6's `≈₋₁`), `Apx n` (`≈_{n−1}`), `SimL n` (`≃_{n−1}`), `SimF g = SimL (g + 1)` (`≃_g`).
* **(a)** `theorem_six`: `t ≃₇₇ t'` implies `O(C[t]) = O(C[t'])` for every context `C`.
* **(b)** `sig`: a computable signature into the explicitly finite type `SigT m (N + p) n`
  (built from `Fin`, `×`, `Option`), with `sig_sound`: equal signatures at level `n` imply
  `SimL n`; `sigCode`, `sigCode_inj`: an injection of `SigT m c n` into `Fin (sigBound m c n)`,
  `sigBound m c 0 = c·m·(m² + 1)`, `sigBound m c (n+1) = c·m·(m² + 1)·(sigBound m c n ² + 1)`.
  `sig_congruence`: equal signatures at level 78 imply equal observables in every context.
-/

namespace Full
open HnfS HnfSound BExp Phi

/-! ## Constants, the observable, the relations -/

/-- The constants of S6, Section 4: `N ≥ 10`, `p ≥ 1`; for `j, j' ≥ N − 2` congruent mod `p`,
`σ^j = σ^j'` and `φ^j = φ^j'` on all of `M`, `M²`. -/
structure PeriodicF (𝔐 : SModel) (N p : Nat) : Prop where
  hN : 10 ≤ N
  hp : 1 ≤ p
  sit : ∀ j j' : Nat, N - 2 ≤ j → N - 2 ≤ j' → j % p = j' % p → ∀ m, 𝔐.sIter j m = 𝔐.sIter j' m
  fib : ∀ j j' : Nat, N - 2 ≤ j → N - 2 ≤ j' → j % p = j' % p → ∀ q, 𝔐.fibM j q = 𝔐.fibM j' q

/-- `Ψ` as a relation: the head run of `t` reaches a stable frame `f w` (`f` has no hnf) with
values `a = M f`, `b = M w`.  Only hnf-less terms have one, and the pair is unique
(`psi_unique`). -/
def Psi (𝔐 : SModel) (t : Term) (a b : 𝔐.M) : Prop :=
  ∃ f w, Steps t (f ⬝ w) ∧ ¬ HasHnf f ∧ a = 𝔐.val f ∧ b = 𝔐.val w

/-- Values of the full observable: the item values of the hnf (the list carries the arity), or
`(⊥, M f, M w)`. -/
inductive Out (α : Type) : Type
  | hnf (items : List α) : Out α
  | bot (f w : α) : Out α

/-- **The full observable `O`** of S6, Definition 3, as a relation. -/
def ObsF (𝔐 : SModel) (t : Term) : Out 𝔐.M → Prop
  | .hnf l => ∃ v, Steps t v ∧ IsHnf v ∧ l = (spine v).map 𝔐.val
  | .bot a b => Psi 𝔐 t a b

/-- The exponent `k` of the core form `t = S^k v`. -/
def coreK : Term → Nat
  | .app .S x => coreK x + 1
  | _ => 0

/-- The core `v` of the core form `t = S^k v`: `S`, or a term of at least two items. -/
def coreV : Term → Term
  | .app .S x => coreV x
  | t => t

/-- S6's `≈₋₁`: equal values and, if `v` has no hnf, equal `Ψ`. -/
def Base0 (𝔐 : SModel) (v v' : Term) : Prop :=
  𝔐.val v = 𝔐.val v' ∧ (¬ HasHnf v → ∀ a b, Psi 𝔐 v a b ↔ Psi 𝔐 v' a b)

/-- S6's `≈_{n−1}` on cores: `Apx 0 = ≈₋₁`; `Apx (n+1) v v'` iff `v ≈₋₁ v'` and, for the two-item
hnfs `S a b`, `S a' b'` of `v`, `v'`: `a ≃_{n−1} a'` and `b ≃_{n−1} b'` (`≃` unfolded into the
core forms, see `SimL`). -/
def Apx (𝔐 : SModel) (N p : Nat) : Nat → Term → Term → Prop
  | 0 => Base0 𝔐
  | n + 1 => fun v v' => Base0 𝔐 v v' ∧
      ∀ a b a' b' : Term, Steps v (S ⬝ a ⬝ b) → Steps v' (S ⬝ a' ⬝ b') →
        (TowRel N p (coreK a) (coreK a') ∧ Apx 𝔐 N p n (coreV a) (coreV a')) ∧
        (TowRel N p (coreK b) (coreK b') ∧ Apx 𝔐 N p n (coreV b) (coreV b'))

/-- S6's `≃_{n−1}`: the core forms `(k, v)`, `(k', v')` satisfy `k ∼ k'` (`TowRel`) and
`v ≈_{n−1} v'`. -/
def SimL (𝔐 : SModel) (N p n : Nat) (u u' : Term) : Prop :=
  TowRel N p (coreK u) (coreK u') ∧ Apx 𝔐 N p n (coreV u) (coreV u')

/-- **S6's `≃_g`**, `g ≥ 0`. -/
def SimF (𝔐 : SModel) (N p g : Nat) : Term → Term → Prop := SimL 𝔐 N p (g + 1)

/-- The frame `f w` is stable, decided on blocks. -/
def stableB : Term → Bool
  | .app f _ => fold f == 36
  | _ => false

/-! ## Values, steps, stable frames -/

/-- The value is invariant under head steps (the S-law of the model). -/
theorem val_step (𝔐 : SModel) {t t' : Term} (s : Step t t') : PureS t → 𝔐.val t = 𝔐.val t' := by
  induction s with
  | S f g x => intro _; exact 𝔐.law _ _ _
  | K x y => intro h; exact absurd h.app_inv.1.app_inv.1 PureS.not_K
  | I x => intro h; exact absurd h.app_inv.1 PureS.not_I
  | left x _ ih => intro h; show 𝔐.app _ _ = 𝔐.app _ _; rw [ih h.app_inv.1]

theorem val_steps (𝔐 : SModel) {t u : Term} (h : Steps t u) : PureS t → 𝔐.val t = 𝔐.val u := by
  induction h with
  | refl => intro _; rfl
  | step s _ ih => intro ht; exact (val_step 𝔐 s ht).trans (ih (wstep_pure s.weak ht).1)

theorem bot_of_nohnf {f : Term} (hf : PureS f) (h : ¬ HasHnf f) : fold f = 36 := by
  rcases Nat.decEq (fold f) 36 with hb | hb
  · exact (h (sound f hf hb)).elim
  · exact hb

theorem fold_frame {f w : Term} (hw : PureS w) (hb : fold f = 36) : fold (f ⬝ w) = 36 := by
  show β (fold f) (fold w) = 36
  rw [hb]; exact absorb (fold_lt hw)

/-- A head step of `f w` with `f` hnf-less is a head step of `f`. -/
theorem stable_step' {f w u : Term} (hf : PureS f) (hb : fold f = 36) (s : Step (f ⬝ w) u) :
    ∃ f', u = f' ⬝ w ∧ Step f f' := by
  cases s with
  | S a c x =>
    exfalso
    obtain ⟨h1, hc⟩ := hf.app_inv
    exact (hnf_blocks (fold_lt h1.app_inv.2) (fold_lt hc)).2 hb
  | K x y => exact absurd hf.app_inv.1 PureS.not_K
  | I x => exact absurd hf PureS.not_I
  | left _ h => exact ⟨_, rfl, h⟩

/-- Once at a stable frame `f w`, the head run keeps `w` and head-reduces `f`. -/
theorem stable_run {w : Term} : ∀ {t u : Term}, Steps t u → ∀ {f : Term}, t = f ⬝ w → PureS f →
    fold f = 36 → ∃ f', u = f' ⬝ w ∧ Steps f f' := by
  intro t u h
  induction h with
  | refl t => intro f e _ _; exact ⟨f, e, .refl _⟩
  | step s _ ih =>
    intro f e hf hb
    subst e
    obtain ⟨f', e', s'⟩ := stable_step' hf hb s
    obtain ⟨hp, he⟩ := wstep_pure s'.weak hf
    obtain ⟨f'', e'', ss⟩ := ih e' hp (he.trans hb)
    exact ⟨f'', e'', .step s' ss⟩

/-- Stable frames on one head run have the same value pair. -/
theorem psi_unique (𝔐 : SModel) {t : Term} (ht : PureS t) {a b a' b' : 𝔐.M}
    (h : Psi 𝔐 t a b) (h' : Psi 𝔐 t a' b') : a = a' ∧ b = b' := by
  obtain ⟨f, w, hs, hn, rfl, rfl⟩ := h
  obtain ⟨f', w', hs', hn', rfl, rfl⟩ := h'
  have hf := (steps_pure ht hs).app_inv.1
  have hf' := (steps_pure ht hs').app_inv.1
  rcases steps_linear hs hs' with hl | hl
  · obtain ⟨g, e, sg⟩ := stable_run hl rfl hf (bot_of_nohnf hf hn)
    injection e with e1 e2
    exact ⟨by rw [e1]; exact val_steps 𝔐 sg hf, by rw [e2]⟩
  · obtain ⟨g, e, sg⟩ := stable_run hl rfl hf' (bot_of_nohnf hf' hn')
    injection e with e1 e2
    exact ⟨by rw [e1]; exact (val_steps 𝔐 sg hf').symm, by rw [e2]⟩

/-- A term with a stable frame on its head run has no hnf (block ⊥). -/
theorem bot_of_psi (𝔐 : SModel) {t : Term} (ht : PureS t) {a b : 𝔐.M} (h : Psi 𝔐 t a b) :
    fold t = 36 := by
  obtain ⟨f, w, hs, hn, _, _⟩ := h
  have hp := steps_pure ht hs
  rw [← steps_fold ht hs]
  exact fold_frame hp.app_inv.2 (bot_of_nohnf hp.app_inv.1 hn)

/-- `Ψ` of a literal stable frame. -/
theorem psi_frame (𝔐 : SModel) {f w : Term} (hf : PureS f) (hw : PureS w) (hb : fold f = 36)
    (a b : 𝔐.M) : Psi 𝔐 (f ⬝ w) a b ↔ a = 𝔐.val f ∧ b = 𝔐.val w := by
  have h0 : Psi 𝔐 (f ⬝ w) (𝔐.val f) (𝔐.val w) :=
    ⟨f, w, .refl _, no_hnf_of_bot hf hb, rfl, rfl⟩
  constructor
  · intro h; exact psi_unique 𝔐 (.app hf hw) h h0
  · rintro ⟨rfl, rfl⟩; exact h0

theorem psi_of_steps (𝔐 : SModel) {P Q : Term} {a b : 𝔐.M} (s : Steps P Q) (h : Psi 𝔐 Q a b) :
    Psi 𝔐 P a b := by
  obtain ⟨f, w, h1, h2, h3, h4⟩ := h
  exact ⟨f, w, s.trans h1, h2, h3, h4⟩

/-! ## Runs to the hnf or the first stable frame -/

/-- The end of a run: an hnf or a stable frame. -/
def Terminal (u : Term) : Prop := IsHnf u ∨ GCert.Stable u

theorem stable_iff {f w : Term} (hf : PureS f) : GCert.Stable (f ⬝ w) ↔ fold f = 36 := by
  constructor
  · rintro ⟨f0, w0, e, hn⟩
    injection e with e1 _
    rw [e1]; rw [e1] at hf
    exact bot_of_nohnf hf hn
  · intro hb; exact ⟨f, w, rfl, no_hnf_of_bot hf hb⟩

theorem stableB_iff {t : Term} (ht : PureS t) : stableB t = true ↔ GCert.Stable t := by
  cases ht with
  | S => exact ⟨fun h => Bool.noConfusion h, fun ⟨_, _, e, _⟩ => Term.noConfusion e⟩
  | @app f w hf hw =>
    show (fold f == 36) = true ↔ _
    exact beq_iff_eq.trans (stable_iff hf).symm

theorem hnf_spine {t : Term} (h : IsHnf t) : (spine t).length ≤ 2 := by
  rcases h with rfl | ⟨x, rfl⟩ | ⟨x, y, rfl⟩
  · exact Nat.zero_le 2
  · exact Nat.le_succ 1
  · exact Nat.le_refl 2

theorem run_steps' {k n : Nat} {t u : Term} (h : GCert.Run k n t u) : Steps t u := by
  induction h with
  | refl => exact .refl _
  | step _ hS _ _ ih => rw [hS]; exact .step (step_foldl (.S _ _ _) _) ih

/-- The head run of a closed S-term reaches an hnf or a stable frame, through frames that are
not stable (from `TopTerm.reach_all`). -/
theorem run_of_reach {t : Term} (h : TopTerm.Reach t) : PureS t →
    ∃ k n u, GCert.Run k n t u ∧ Terminal u := by
  induction h with
  | hnf hu => intro _; exact ⟨0, 0, _, .refl _, .inl hu⟩
  | bot hf hb => intro _; exact ⟨0, 0, _, .refl _, .inr ⟨_, _, rfl, no_hnf_of_bot hf hb⟩⟩
  | @step t t' s _ ih =>
    intro ht
    cases hsb : stableB t with
    | true => exact ⟨0, 0, t, .refl _, .inr ((stableB_iff ht).1 hsb)⟩
    | false =>
      obtain ⟨u₁, u₂, u₃, rest, hs, rfl⟩ := Phi.step_spine ht s
      have hS : t = rest.foldl Term.app (S ⬝ u₁ ⬝ u₂ ⬝ u₃) := by
        have h0 := pure_eq_foldl ht
        rw [hs] at h0
        exact h0
      obtain ⟨k, n, u, hr, hu⟩ := ih (wstep_pure s.weak ht).1
      exact ⟨_, _, u, .step hs hS (fun hst => by
        rw [(stableB_iff ht).2 hst] at hsb; exact Bool.noConfusion hsb) hr, hu⟩

theorem run_total {t : Term} (ht : PureS t) : ∃ k n u, GCert.Run k n t u ∧ Terminal u :=
  run_of_reach (TopTerm.reach_all ht) ht

theorem psi_of_run (𝔐 : SModel) {k n : Nat} {t u : Term} (ht : PureS t) (hb : fold t = 36)
    (hr : GCert.Run k n t u) (hu : Terminal u) : ∃ a b, Psi 𝔐 t a b := by
  have hs := run_steps' hr
  rcases hu with hu | ⟨f, w, rfl, hn⟩
  · exact absurd ((steps_fold ht hs).trans hb) (fold_hnf (steps_pure ht hs) hu)
  · exact ⟨_, _, f, w, hs, hn, rfl, rfl⟩

/-- The first step of a run from a frame of at least three items that is not stable. -/
theorem run_inv {k n : Nat} {t u : Term} (hr : GCert.Run k n t u) (hu : Terminal u)
    (hns : ¬ GCert.Stable t) {u₁ u₂ u₃ : Term} {rest : List Term}
    (hs : spine t = u₁ :: u₂ :: u₃ :: rest) :
    ∃ k₁ n₁, k = k₁ + 1 ∧ n = n₁ + (if GCert.isOther u₁ then 1 else 0) ∧
      GCert.Run k₁ n₁ (rest.foldl Term.app (u₁ ⬝ u₃ ⬝ (u₂ ⬝ u₃))) u := by
  cases hr with
  | refl =>
    rcases hu with hu | hu
    · exact (GCert.short_ne hs (hnf_spine hu)).elim
    · exact (hns hu).elim
  | @step k₁ n₁ _ _ a₁ a₂ a₃ rest' hs' hS _ hr' =>
    have e := hs.symm.trans hs'
    injection e with e1 e
    injection e with e2 e
    injection e with e3 e4
    subst e1; subst e2; subst e3; subst e4
    exact ⟨k₁, n₁, rfl, rfl, hr'⟩

/-- Head steps from frames that are not stable. -/
inductive NSteps : Term → Term → Prop
  | refl (t : Term) : NSteps t t
  | step {t t' u : Term} : ¬ GCert.Stable t → Step t t' → NSteps t' u → NSteps t u

/-- A run to its end passes through every term reached by such steps. -/
theorem run_adv {P Q : Term} (h : NSteps P Q) : ∀ {k n : Nat} {u : Term}, GCert.Run k n P u →
    Terminal u → ∃ k' n', k' ≤ k ∧ n' ≤ n ∧ GCert.Run k' n' Q u := by
  induction h with
  | refl => intro k n u hr _; exact ⟨k, n, Nat.le_refl _, Nat.le_refl _, hr⟩
  | @step t t' q hns s _ ih =>
    intro k n u hr hu
    cases hr with
    | refl =>
      rcases hu with hu | hu
      · exact (no_step_hnf hu s).elim
      · exact (hns hu).elim
    | @step k₁ n₁ _ _ u₁ u₂ u₃ rest hs hS _ hr' =>
      have s2 : Step t (rest.foldl Term.app (u₁ ⬝ u₃ ⬝ (u₂ ⬝ u₃))) := by
        rw [hS]; exact step_foldl (.S u₁ u₂ u₃) rest
      have e := Step.det s s2
      subst e
      obtain ⟨k', n', hk, hn, h'⟩ := ih hr' hu
      exact ⟨k', n', Nat.le_succ_of_le hk, Nat.le_trans hn (Nat.le_add_right _ _), h'⟩

theorem nsteps_left {f g : Term} (w : Term) (h : Steps f g) : PureS f → fold f ≠ 36 →
    NSteps (f ⬝ w) (g ⬝ w) := by
  induction h with
  | refl => intro _ _; exact .refl _
  | step s _ ih =>
    intro hf hb
    obtain ⟨hp, he⟩ := wstep_pure s.weak hf
    exact .step (fun hst => hb ((stable_iff hf).1 hst)) (.left w s) (ih hp (by rw [he]; exact hb))

theorem list_snoc {α : Type} : ∀ (as : List α), as ≠ [] → ∃ l w, as = l ++ [w]
  | [], h => absurd rfl h
  | [a], _ => ⟨[], a, rfl⟩
  | a :: b :: l, _ =>
    let ⟨l', w, e⟩ := list_snoc (b :: l) (List.cons_ne_nil _ _)
    ⟨a :: l', w, congrArg (List.cons a) e⟩

theorem foldl_snoc (h : Term) (l : List Term) (w : Term) :
    (l ++ [w]).foldl Term.app h = l.foldl Term.app h ⬝ w := by
  rw [List.foldl_append]; rfl

/-- Head steps of the head of a frame that is not stable, with at least one argument. -/
theorem nsteps_args {a b : Term} {as : List Term} (hab : Steps a b) (pa : PureS a)
    (pas : ∀ c ∈ as, PureS c) (hne : as ≠ []) (hns : ¬ GCert.Stable (as.foldl Term.app a)) :
    NSteps (as.foldl Term.app a) (as.foldl Term.app b) := by
  obtain ⟨l, w, rfl⟩ := list_snoc as hne
  have pl : ∀ c ∈ l, PureS c := fun c hc => pas c (List.mem_append_left _ hc)
  rw [foldl_snoc] at hns
  rw [foldl_snoc, foldl_snoc]
  have pf := pure_foldl l pa pl
  exact nsteps_left w (steps_foldl hab l) pf (fun hb => hns ((stable_iff pf).2 hb))

/-- The burst (S6, Lemma 7) passes no stable frame. -/
theorem nsteps_burst : ∀ (k : Nat) {u x y : Term}, PureS u → PureS x → PureS y →
    NSteps (iterS k u ⬝ x ⬝ y) (u ⬝ (fibT k (x, y)).1 ⬝ (fibT k (x, y)).2) := by
  intro k
  induction k with
  | zero => intro u x y _ _ _; exact .refl _
  | succ k ih =>
    intro u x y pu px py
    have pf : PureS (S ⬝ iterS k u ⬝ x) := .app (.app .S (iterS_pure k pu)) px
    exact .step (fun hst => fold_hnf pf (.inr (.inr ⟨_, _, rfl⟩)) ((stable_iff pf).1 hst))
      (.S (iterS k u) x y) (ih pu py (.app px py))

theorem nsteps_head {a b : Term} {as : List Term} (hab : Steps a b) (h0 : NSteps a b)
    (pa : PureS a) (pas : ∀ c ∈ as, PureS c) (hns : ¬ GCert.Stable (as.foldl Term.app a)) :
    NSteps (as.foldl Term.app a) (as.foldl Term.app b) := by
  cases as with
  | nil => exact h0
  | cons _ _ => exact nsteps_args hab pa pas (List.cons_ne_nil _ _) hns

/-! ## The observable is a function -/

/-- The observable is defined on every closed S-term. -/
theorem obsF_total (𝔐 : SModel) {t : Term} (ht : PureS t) : ∃ o, ObsF 𝔐 t o := by
  obtain ⟨k, n, u, hr, hu⟩ := run_total ht
  have hs := run_steps' hr
  rcases hu with hu | ⟨f, w, rfl, hn⟩
  · exact ⟨.hnf _, u, hs, hu, rfl⟩
  · exact ⟨.bot _ _, f, w, hs, hn, rfl, rfl⟩

/-- The observable is a function. -/
theorem obsF_unique (𝔐 : SModel) {t : Term} (ht : PureS t) {o o' : Out 𝔐.M}
    (h : ObsF 𝔐 t o) (h' : ObsF 𝔐 t o') : o = o' := by
  cases o with
  | hnf l =>
    obtain ⟨v, hs, hv, e⟩ := h
    have hb : fold t ≠ 36 := by rw [← steps_fold ht hs]; exact fold_hnf (steps_pure ht hs) hv
    cases o' with
    | hnf l' =>
      obtain ⟨v', hs', hv', e'⟩ := h'
      rw [e, e', hnf_unique hs hv hs' hv']
    | bot a b => exact absurd (bot_of_psi 𝔐 ht h') hb
  | bot a b =>
    cases o' with
    | hnf l' =>
      obtain ⟨v, hs, hv, e⟩ := h'
      have hb : fold t ≠ 36 := by rw [← steps_fold ht hs]; exact fold_hnf (steps_pure ht hs) hv
      exact absurd (bot_of_psi 𝔐 ht h) hb
    | bot a' b' =>
      obtain ⟨e1, e2⟩ := psi_unique 𝔐 ht h h'
      rw [e1, e2]

/-- The head run of an hnf-less term reaches a first stable frame: a run (`GCert.Run`) all of
whose frames before the last are not stable.  Its value pair is `Ψ`. -/
theorem first_stable (𝔐 : SModel) {t : Term} (ht : PureS t) (hn : ¬ HasHnf t) :
    ∃ k n f w, GCert.Run k n t (f ⬝ w) ∧ ¬ HasHnf f ∧ ObsF 𝔐 t (.bot (𝔐.val f) (𝔐.val w)) := by
  obtain ⟨k, n, u, hr, hu⟩ := run_total ht
  have hs := run_steps' hr
  rcases hu with hu | ⟨f, w, rfl, hf⟩
  · exact (hn ⟨u, hs.weak, hu⟩).elim
  · exact ⟨k, n, f, w, hr, hf, f, w, hs, hf, rfl, rfl⟩

/-! ## Core forms -/

theorem core_eq : ∀ t : Term, t = iterS (coreK t) (coreV t)
  | .app .S x => congrArg (Term.app S) (core_eq x)
  | .S => rfl
  | .K => rfl
  | .I => rfl
  | .app (.app _ _) _ => rfl
  | .app .K _ => rfl
  | .app .I _ => rfl

theorem coreK_coreV : ∀ t : Term, coreK (coreV t) = 0
  | .app .S x => coreK_coreV x
  | .S => rfl
  | .K => rfl
  | .I => rfl
  | .app (.app _ _) _ => rfl
  | .app .K _ => rfl
  | .app .I _ => rfl

theorem coreV_pure : ∀ {t : Term}, PureS t → PureS (coreV t)
  | .S, _ => .S
  | .app .S x, h => coreV_pure (t := x) h.app_inv.2
  | .app (.app _ _) _, h => h
  | .app .K _, h => h
  | .app .I _, h => h
  | .K, h => h
  | .I, h => h

theorem coreV_zero : ∀ {t : Term}, coreK t = 0 → coreV t = t
  | .app .S _, h => absurd h (Nat.succ_ne_zero _)
  | .S, _ => rfl
  | .K, _ => rfl
  | .I, _ => rfl
  | .app (.app _ _) _, _ => rfl
  | .app .K _, _ => rfl
  | .app .I _, _ => rfl

theorem coreK_succ : ∀ {t : Term} {j : Nat}, coreK t = j + 1 → ∃ x, t = S ⬝ x ∧ coreK x = j
  | .app .S x, _, h => ⟨x, rfl, Nat.succ.inj h⟩
  | .S, _, h => absurd h.symm (Nat.succ_ne_zero _)
  | .K, _, h => absurd h.symm (Nat.succ_ne_zero _)
  | .I, _, h => absurd h.symm (Nat.succ_ne_zero _)
  | .app (.app _ _) _, _, h => absurd h.symm (Nat.succ_ne_zero _)
  | .app .K _, _, h => absurd h.symm (Nat.succ_ne_zero _)
  | .app .I _, _, h => absurd h.symm (Nat.succ_ne_zero _)

/-- A core is `S` or has at least two items (S6, Lemma 5). -/
theorem core_cases : ∀ {t : Term}, PureS t → coreK t = 0 → t = S ∨ GCert.isOther t = true
  | .S, _, _ => .inl rfl
  | .app .S _, _, h => absurd h (Nat.succ_ne_zero _)
  | .app (.app _ _) _, _, _ => .inr rfl
  | .app .K _, h, _ => absurd h.app_inv.1 PureS.not_K
  | .app .I _, h, _ => absurd h.app_inv.1 PureS.not_I
  | .K, h, _ => absurd h PureS.not_K
  | .I, h, _ => absurd h PureS.not_I

theorem other_blocks : ∀ {t : Term}, PureS t → GCert.isOther t = true →
    fold t ∉ PsiSkel.oneBlocks ∧ fold t ≠ 0
  | .app (.app _ _) _, h, _ =>
    PsiSkel.fold_two_items h.app_inv.1.app_inv.1 h.app_inv.1.app_inv.2 h.app_inv.2
  | .S, _, h => Bool.noConfusion h
  | .K, _, h => Bool.noConfusion h
  | .I, _, h => Bool.noConfusion h
  | .app .S _, _, h => Bool.noConfusion h
  | .app .K _, _, h => Bool.noConfusion h
  | .app .I _, _, h => Bool.noConfusion h

/-- The hnf of a term of at least two items has exactly two items. -/
theorem hnf_two {v w : Term} (pv : PureS v) (hs : Steps v w) (hw : IsHnf w)
    (h1 : fold v ∉ PsiSkel.oneBlocks) (h0 : fold v ≠ 0) : ∃ a b, w = S ⬝ a ⬝ b := by
  have e := steps_fold pv hs
  have pw := steps_pure pv hs
  rcases hw with rfl | ⟨x, rfl⟩ | ⟨a, b, rfl⟩
  · exact absurd e.symm h0
  · exact absurd (by rw [← e]; exact PsiSkel.fold_one_item pw.app_inv.2) h1
  · exact ⟨a, b, rfl⟩

theorem val_iterS (𝔐 : SModel) : ∀ (k : Nat) (v : Term),
    𝔐.val (iterS k v) = 𝔐.sIter k (𝔐.val v)
  | 0, _ => rfl
  | k + 1, v => congrArg (𝔐.app 𝔐.s) (val_iterS 𝔐 k v)

theorem iterS_succ' : ∀ (k : Nat) (v : Term), iterS k (S ⬝ v) = iterS (k + 1) v
  | 0, _ => rfl
  | k + 1, v => congrArg (Term.app S) (iterS_succ' k v)

theorem S_of_val (𝔐 : SModel) {u' : Term} (hu' : PureS u') (h : 𝔐.val S = 𝔐.val u') : u' = S :=
  fold_eq_zero hu' (fold_eq_of_val 𝔐 .S hu' h).symm

section
variable {𝔐 : SModel} {N p : Nat}

theorem apx_base : ∀ {n : Nat} {v v' : Term}, Apx 𝔐 N p n v v' → Base0 𝔐 v v'
  | 0, _, _, h => h
  | _ + 1, _, _, h => h.1

theorem sIter_tow (hper : PeriodicF 𝔐 N p) {k k' : Nat} (h : TowRel N p k k') (m : 𝔐.M) :
    𝔐.sIter k m = 𝔐.sIter k' m := by
  rcases h with e | ⟨a, b, c⟩
  · rw [e]
  · exact hper.sit k k' (Nat.le_trans (Nat.sub_le N 2) a) (Nat.le_trans (Nat.sub_le N 2) b) c m

/-- `≃`-related terms have equal values. -/
theorem simL_val (hper : PeriodicF 𝔐 N p) {n : Nat} {u u' : Term} (h : SimL 𝔐 N p n u u') :
    𝔐.val u = 𝔐.val u' := by
  have h1 : 𝔐.val u = 𝔐.sIter (coreK u) (𝔐.val (coreV u)) := by
    rw [← val_iterS, ← core_eq u]
  have h1' : 𝔐.val u' = 𝔐.sIter (coreK u') (𝔐.val (coreV u')) := by
    rw [← val_iterS, ← core_eq u']
  rw [h1, h1', (apx_base h.2).1]
  exact sIter_tow hper h.1 _

/-! ## Fibonacci pairs -/

theorem fibT_succ' : ∀ (k : Nat) (q : Term × Term),
    fibT (k + 1) q = ((fibT k q).2, (fibT k q).1 ⬝ (fibT k q).2)
  | 0, _ => rfl
  | k + 1, q => fibT_succ' k (q.2, q.1 ⬝ q.2)

theorem fib_vals (hper : PeriodicF 𝔐 N p) {i i' : Nat} (hi : N - 2 ≤ i) (hi' : N - 2 ≤ i')
    (hc : i % p = i' % p) {x y x' y' : Term} (ex : 𝔐.val x = 𝔐.val x')
    (ey : 𝔐.val y = 𝔐.val y') :
    𝔐.val (fibT i (x, y)).1 = 𝔐.val (fibT i' (x', y')).1 ∧
    𝔐.val (fibT i (x, y)).2 = 𝔐.val (fibT i' (x', y')).2 := by
  have h := val_fibT 𝔐 i x y
  have h' := val_fibT 𝔐 i' x' y'
  rw [ex, ey, hper.fib i i' hi hi' hc] at h
  have e := h.trans h'.symm
  exact ⟨congrArg Prod.fst e, congrArg Prod.snd e⟩

/-- (A) pairs of S6: hnf-less, equal values, equal `Ψ`. -/
def Dead (𝔐 : SModel) (u u' : Term) : Prop :=
  fold u = 36 ∧ 𝔐.val u = 𝔐.val u' ∧ ∀ a b, Psi 𝔐 u a b ↔ Psi 𝔐 u' a b

theorem dead_frame {f w f' w' : Term} (hf : PureS f) (hw : PureS w) (hf' : PureS f')
    (hw' : PureS w') (hb : fold f = 36) (ef : 𝔐.val f = 𝔐.val f') (ew : 𝔐.val w = 𝔐.val w') :
    Dead 𝔐 (f ⬝ w) (f' ⬝ w') := by
  have hb' : fold f' = 36 := by rw [← fold_eq_of_val 𝔐 hf hf' ef]; exact hb
  refine ⟨fold_frame hw hb, by show 𝔐.app _ _ = 𝔐.app _ _; rw [ef, ew], fun a b => ?_⟩
  rw [psi_frame 𝔐 hf hw hb, psi_frame 𝔐 hf' hw' hb', ef, ew]

/-- After a burst of length `k ≥ N ≥ 10`, the two Fibonacci terms are stable frames, and their
`M`- and `Ψ`-values depend only on the class of `k` (S6, Section 4, with Lemma 7). -/
theorem fib_pair (hper : PeriodicF 𝔐 N p) {k k' : Nat} (hk : N ≤ k) (hk' : N ≤ k')
    (hc : k % p = k' % p) {x y x' y' : Term} (px : PureS x) (py : PureS y) (px' : PureS x')
    (py' : PureS y') (ex : 𝔐.val x = 𝔐.val x') (ey : 𝔐.val y = 𝔐.val y') :
    Dead 𝔐 (fibT k (x, y)).1 (fibT k' (x', y')).1 ∧
    Dead 𝔐 (fibT k (x, y)).2 (fibT k' (x', y')).2 := by
  have hN := hper.hN
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 + 1 := ⟨k - 2, by omega⟩
  obtain ⟨j', rfl⟩ : ∃ j', k' = j' + 1 + 1 := ⟨k' - 2, by omega⟩
  have hc1 : (j + 1) % p = (j' + 1) % p := mod_pred hper.hp hc
  have hc0 : j % p = j' % p := mod_pred hper.hp hc1
  obtain ⟨i, ei⟩ : ∃ i, j = i + 8 := ⟨j - 8, by omega⟩
  obtain ⟨i', ei'⟩ : ∃ i', j' = i' + 8 := ⟨j' - 8, by omega⟩
  have d0 := fib_dead i px py
  rw [← ei] at d0
  have d1 := fib_dead (i + 1) px py
  rw [show i + 1 + 8 = j + 1 by omega] at d1
  have v0 := fib_vals hper (i := j) (i' := j') (by omega) (by omega) hc0 ex ey
  have v1 := fib_vals hper (i := j + 1) (i' := j' + 1) (by omega) (by omega) hc1 ex ey
  have p0 := fibT_pure j px py
  have p0' := fibT_pure j' px' py'
  have p1 := fibT_pure (j + 1) px py
  have p1' := fibT_pure (j' + 1) px' py'
  have e1 := fibT_succ' (j + 1) (x, y)
  have e1' := fibT_succ' (j' + 1) (x', y')
  have e0 := fibT_succ' j (x, y)
  have e0' := fibT_succ' j' (x', y')
  constructor
  · have h : Dead 𝔐 ((fibT j (x, y)).1 ⬝ (fibT j (x, y)).2)
        ((fibT j' (x', y')).1 ⬝ (fibT j' (x', y')).2) :=
      dead_frame p0.1 p0.2 p0'.1 p0'.2 d0.1 v0.1 v0.2
    rw [e1, e1', e0, e0']
    exact h
  · have h : Dead 𝔐 ((fibT (j + 1) (x, y)).1 ⬝ (fibT (j + 1) (x, y)).2)
        ((fibT (j' + 1) (x', y')).1 ⬝ (fibT (j' + 1) (x', y')).2) :=
      dead_frame p1.1 p1.2 p1'.1 p1'.2 d1.1 v1.1 v1.2
    rw [e1, e1']
    exact h

/-! ## Configurations -/

/-- **Configurations** (S6, proof of Theorem 9), as a relation on pairs of terms: `P'` arises
from `P` by replacing disjoint occurrences `u` by `u'`, each an (A) pair (`dead`) or a pair
`u ≃_{n−1} u'` with `n ≥ r` (`grad`: S6's invariant (I2), `g ≥ ρ − 1`, with the bound `r ≥ ρ(P)`
in place of `ρ(P)`).  S6 restricts the graded pairs to kind (C); here every `≃`-pair may be
recorded, and `hr_chain`, `hr_of_rel`, `hr_of_free` sort them when they reach the head. -/
inductive RelF (𝔐 : SModel) (N p r : Nat) : Term → Term → Prop
  | atom : RelF 𝔐 N p r Term.S Term.S
  | app {f f' x x' : Term} : RelF 𝔐 N p r f f' → RelF 𝔐 N p r x x' →
      RelF 𝔐 N p r (f ⬝ x) (f' ⬝ x')
  | dead {u u' : Term} : PureS u → PureS u' → Dead 𝔐 u u' → RelF 𝔐 N p r u u'
  | grad {n : Nat} {u u' : Term} : PureS u → PureS u' → r ≤ n → SimL 𝔐 N p n u u' →
      RelF 𝔐 N p r u u'

/-- Closed terms of equal value. -/
def VP (𝔐 : SModel) (a a' : Term) : Prop := PureS a ∧ PureS a' ∧ 𝔐.val a = 𝔐.val a'

theorem RelF.vp (hper : PeriodicF 𝔐 N p) {r : Nat} {u u' : Term} (h : RelF 𝔐 N p r u u') :
    VP 𝔐 u u' := by
  induction h with
  | atom => exact ⟨.S, .S, rfl⟩
  | app _ _ ihf ihx =>
    exact ⟨.app ihf.1 ihx.1, .app ihf.2.1 ihx.2.1,
      by show 𝔐.app _ _ = 𝔐.app _ _; rw [ihf.2.2, ihx.2.2]⟩
  | dead hu hu' hd => exact ⟨hu, hu', hd.2.1⟩
  | grad hu hu' _ hl => exact ⟨hu, hu', simL_val hper hl⟩

theorem RelF.mono {r r' : Nat} {u u' : Term} (hr : r' ≤ r) (h : RelF 𝔐 N p r u u') :
    RelF 𝔐 N p r' u u' := by
  induction h with
  | atom => exact .atom
  | app _ _ ihf ihx => exact .app ihf ihx
  | dead hu hu' hd => exact .dead hu hu' hd
  | grad hu hu' hn hl => exact .grad hu hu' (Nat.le_trans hr hn) hl

theorem vp_foldl {as as' : List Term} (ha : All₂ (VP 𝔐) as as') : ∀ {h h' : Term}, VP 𝔐 h h' →
    VP 𝔐 (as.foldl Term.app h) (as'.foldl Term.app h') := by
  induction ha with
  | nil => intro h h' hh; exact hh
  | cons hab _ ih =>
    intro h h' hh
    exact ih ⟨.app hh.1 hab.1, .app hh.2.1 hab.2.1,
      by show 𝔐.app _ _ = 𝔐.app _ _; rw [hh.2.2, hab.2.2]⟩

theorem all2_snoc {α : Type} {R : α → α → Prop} : ∀ {as as' : List α}, All₂ R as as' →
    as ≠ [] → ∃ l w l' w', as = l ++ [w] ∧ as' = l' ++ [w'] ∧ All₂ R l l' ∧ R w w'
  | _, _, .nil, h => absurd rfl h
  | _, _, .cons hab .nil, _ => ⟨[], _, [], _, rfl, rfl, .nil, hab⟩
  | _, _, .cons hab (.cons h2 h3), _ =>
    let ⟨l, w, l', w', e, e', hl, hw⟩ := all2_snoc (.cons h2 h3) (List.cons_ne_nil _ _)
    ⟨_ :: l, w, _ :: l', w', congrArg (List.cons _) e, congrArg (List.cons _) e', .cons hab hl, hw⟩

/-- The head of a configuration: both heads `S`; an (A) pair; a pair `S^k v`, `S^k' v'` with
`k, k' ≥ N` congruent mod `p` and cores `v ≈_{n−1} v'`, `n ≥ r` (S6's case H2); or a pair of
cores with one level to spare, `v ≈_n v'`, `n ≥ r` (S6's invariant (I1), case H3). -/
def HeadF (𝔐 : SModel) (N p r : Nat) (h h' : Term) : Prop :=
  (h = S ∧ h' = S) ∨
  (PureS h ∧ PureS h' ∧ Dead 𝔐 h h') ∨
  (∃ k k' v v' n, h = iterS k v ∧ h' = iterS k' v' ∧ N ≤ k ∧ N ≤ k' ∧ k % p = k' % p ∧
    PureS v ∧ PureS v' ∧ coreK v = 0 ∧ coreK v' = 0 ∧ r ≤ n ∧ Apx 𝔐 N p n v v') ∨
  (∃ n, PureS h ∧ PureS h' ∧ coreK h = 0 ∧ coreK h' = 0 ∧ r ≤ n ∧ Apx 𝔐 N p (n + 1) h h')

/-- A configuration in spine form: related heads applied to pairwise related arguments. -/
def HRF (𝔐 : SModel) (N p r : Nat) (P P' : Term) : Prop :=
  ∃ h h' as as', P = List.foldl Term.app h as ∧ P' = List.foldl Term.app h' as' ∧
    HeadF 𝔐 N p r h h' ∧ All₂ (RelF 𝔐 N p r) as as'

/-- The conclusion for a configuration: both sides reach hnfs of the same arity with items of
equal values, or both reach stable frames with the same value pair. -/
def GoodF (𝔐 : SModel) (P P' : Term) : Prop :=
  Good 𝔐 P P' ∨ ∃ a b, Psi 𝔐 P a b ∧ Psi 𝔐 P' a b

theorem GoodF.of_steps {P P' Q Q' : Term} (h : GoodF 𝔐 Q Q') (s : Steps P Q)
    (s' : Steps P' Q') : GoodF 𝔐 P P' := by
  rcases h with h | ⟨a, b, h1, h2⟩
  · exact .inl (h.of_steps s s')
  · exact .inr ⟨a, b, psi_of_steps 𝔐 s h1, psi_of_steps 𝔐 s' h2⟩

theorem headF_vp (hper : PeriodicF 𝔐 N p) {r : Nat} {h h' : Term} (hh : HeadF 𝔐 N p r h h') :
    VP 𝔐 h h' := by
  rcases hh with ⟨rfl, rfl⟩ | ⟨hu, hu', hd⟩ |
    ⟨k, k', v, v', n, rfl, rfl, hk, hk', hc, pv, pv', _, _, _, hA⟩ | ⟨n, ph, ph', _, _, _, hA⟩
  · exact ⟨.S, .S, rfl⟩
  · exact ⟨hu, hu', hd.2.1⟩
  · refine ⟨iterS_pure k pv, iterS_pure k' pv', ?_⟩
    rw [val_iterS, val_iterS, (apx_base hA).1]
    exact sIter_tow hper (.inr ⟨hk, hk', hc⟩) _
  · exact ⟨ph, ph', (apx_base hA).1⟩

theorem hrF_app {r : Nat} {f f' x x' : Term} (h : HRF 𝔐 N p r f f')
    (hx : RelF 𝔐 N p r x x') : HRF 𝔐 N p r (f ⬝ x) (f' ⬝ x') := by
  obtain ⟨h, h', as, as', rfl, rfl, hh, ha⟩ := h
  exact ⟨h, h', as ++ [x], as' ++ [x'], by rw [List.foldl_append]; rfl,
    by rw [List.foldl_append]; rfl, hh, ha.append (.cons hx .nil)⟩

theorem hrF_foldl {r : Nat} {rest rest' : List Term} (ha : All₂ (RelF 𝔐 N p r) rest rest') :
    ∀ {f f' : Term}, HRF 𝔐 N p r f f' →
      HRF 𝔐 N p r (rest.foldl Term.app f) (rest'.foldl Term.app f') := by
  induction ha with
  | nil => intro f f' h; exact h
  | cons hx _ ih => intro f f' h; exact ih (hrF_app h hx)

/-- A `≃`-pair that is not a pair of cores may stand at the head at its own level: `k = k'`
gives `S` applied to the pair one `S` shorter (S6's case H1), `k ≠ k'` a burst pair. -/
theorem hr_chain {r n : Nat} {u u' : Term} (hu : PureS u) (hu' : PureS u') (hn : r ≤ n)
    (hl : SimL 𝔐 N p n u u') (hk : coreK u ≠ 0 ∨ coreK u' ≠ 0) : HRF 𝔐 N p r u u' := by
  rcases hl.1 with e | ⟨a, b, c⟩
  · obtain ⟨j, hj⟩ : ∃ j, coreK u = j + 1 := ⟨coreK u - 1, by omega⟩
    have hj' : coreK u' = j + 1 := by rw [← e]; exact hj
    obtain ⟨x, rfl, cx⟩ := coreK_succ hj
    obtain ⟨x', rfl, cx'⟩ := coreK_succ hj'
    exact ⟨S, S, [x], [x'], rfl, rfl, .inl ⟨rfl, rfl⟩,
      .cons (.grad hu.app_inv.2 hu'.app_inv.2 hn ⟨.inl (by rw [cx, cx']), hl.2⟩) .nil⟩
  · exact ⟨u, u', [], [], rfl, rfl, .inr (.inr (.inl ⟨coreK u, coreK u', coreV u, coreV u', n,
      core_eq u, core_eq u', a, b, c, coreV_pure hu, coreV_pure hu', coreK_coreV u,
      coreK_coreV u', hn, hl.2⟩)), .nil⟩

/-- A related pair with one unit of level to spare may stand at the head. -/
theorem hr_of_rel {r : Nat} {u u' : Term} (h : RelF 𝔐 N p (r + 1) u u') : HRF 𝔐 N p r u u' := by
  induction h with
  | atom => exact ⟨S, S, [], [], rfl, rfl, .inl ⟨rfl, rfl⟩, .nil⟩
  | app _ hx ihf _ => exact hrF_app ihf (hx.mono (Nat.le_succ r))
  | dead hu hu' hd => exact ⟨_, _, [], [], rfl, rfl, .inr (.inl ⟨hu, hu', hd⟩), .nil⟩
  | @grad n u u' hu hu' hn hl =>
    rcases Nat.decEq (coreK u) 0 with h0 | h0
    · exact hr_chain hu hu' (Nat.le_of_succ_le hn) hl (.inl h0)
    · rcases Nat.decEq (coreK u') 0 with h0' | h0'
      · exact hr_chain hu hu' (Nat.le_of_succ_le hn) hl (.inr h0')
      · cases n with
        | zero => exact absurd hn (Nat.not_succ_le_zero r)
        | succ m =>
          have hA := hl.2
          rw [coreV_zero h0, coreV_zero h0'] at hA
          exact ⟨u, u', [], [], rfl, rfl,
            .inr (.inr (.inr ⟨m, hu, hu', h0, h0', Nat.le_of_succ_le_succ hn, hA⟩)), .nil⟩

/-- A related pair whose left side is `S` or a one-item term `S x` may stand at the head at
its own level: it comes to the head by a free step. -/
theorem hr_of_free (hper : PeriodicF 𝔐 N p) {r : Nat} {u u' : Term}
    (h : RelF 𝔐 N p r u u') (ho : GCert.isOther u = false) : HRF 𝔐 N p r u u' := by
  cases h with
  | atom => exact ⟨S, S, [], [], rfl, rfl, .inl ⟨rfl, rfl⟩, .nil⟩
  | @app f f' x x' hf hx =>
    have vf := hf.vp hper
    have pf := vf.1
    cases pf with
    | S =>
      have e := S_of_val 𝔐 vf.2.1 vf.2.2
      subst e
      exact ⟨S, S, [x], [x'], rfl, rfl, .inl ⟨rfl, rfl⟩, .cons hx .nil⟩
    | app _ _ => exact Bool.noConfusion ho
  | dead hu hu' hd => exact ⟨_, _, [], [], rfl, rfl, .inr (.inl ⟨hu, hu', hd⟩), .nil⟩
  | @grad n _ _ hu hu' hn hl =>
    rcases Nat.decEq (coreK u) 0 with h0 | h0
    · exact hr_chain hu hu' hn hl (.inl h0)
    · rcases Nat.decEq (coreK u') 0 with h0' | h0'
      · exact hr_chain hu hu' hn hl (.inr h0')
      · rcases core_cases hu h0 with e | e
        · subst e
          have e' := S_of_val 𝔐 hu' (simL_val hper hl)
          subst e'
          exact ⟨S, S, [], [], rfl, rfl, .inl ⟨rfl, rfl⟩, .nil⟩
        · rw [e] at ho; exact Bool.noConfusion ho

/-- Start: filling the holes of a context with related terms gives a configuration. -/
theorem rel_plugF {r n : Nat} {t t' : Term} (ht : PureS t) (ht' : PureS t') (hn : r ≤ n)
    (h : SimL 𝔐 N p n t t') : ∀ C : Ctx, RelF 𝔐 N p r (C.plug t) (C.plug t') := by
  intro C
  induction C with
  | hole => exact .grad ht ht' hn h
  | s => exact .atom
  | app _ _ ihc ihd => exact .app ihc ihd

/-! ## The cases of the proof -/

/-- S6, case T for hnfs: frames of at most two items of pairwise equal values. -/
theorem goodF_short {as as' : List Term} (ha : All₂ (VP 𝔐) as as') (hl : as.length ≤ 2)
    (hl' : as'.length ≤ 2) : GoodF 𝔐 (as.foldl Term.app S) (as'.foldl Term.app S) := by
  have hP : PureS (as.foldl Term.app S) := pure_foldl as .S (ha.forall_left fun _ _ h => h.1)
  have hP' : PureS (as'.foldl Term.app S) :=
    pure_foldl as' .S (ha.forall_right fun _ _ h => h.2.1)
  have hsp : spine (as.foldl Term.app S) = as := by rw [spine_foldl]; rfl
  have hsp' : spine (as'.foldl Term.app S) = as' := by rw [spine_foldl]; rfl
  refine .inl ⟨_, _, .refl _, isHnf_of_short hP (by rw [hsp]; exact hl), .refl _,
    isHnf_of_short hP' (by rw [hsp']; exact hl'), ?_⟩
  rw [hsp, hsp']
  exact ha.mono fun _ _ h => h.2.2

/-- S6, case T for stable frames. -/
theorem goodF_stable {f w f' w' : Term} (hf : VP 𝔐 f f') (hw : VP 𝔐 w w') (hb : fold f = 36) :
    GoodF 𝔐 (f ⬝ w) (f' ⬝ w') :=
  .inr ⟨𝔐.val f, 𝔐.val w, ⟨f, w, .refl _, no_hnf_of_bot hf.1 hb, rfl, rfl⟩,
    ⟨f', w', .refl _,
      no_hnf_of_bot hf.2.1 (by rw [← fold_eq_of_val 𝔐 hf.1 hf.2.1 hf.2.2]; exact hb),
      hf.2.2, hw.2.2⟩⟩

/-- A configuration with at least one argument is a stable frame on the left, and then the
conclusion holds, or it is not stable. -/
theorem good_or_ns {h h' : Term} {as as' : List Term} (hh : VP 𝔐 h h')
    (ha : All₂ (VP 𝔐) as as') (hne : as ≠ []) :
    GoodF 𝔐 (as.foldl Term.app h) (as'.foldl Term.app h') ∨
      ¬ GCert.Stable (as.foldl Term.app h) := by
  obtain ⟨l, w, l', w', rfl, rfl, hl, hw⟩ := all2_snoc ha hne
  have hf := vp_foldl hl hh
  rw [foldl_snoc, foldl_snoc]
  rcases Nat.decEq (fold (l.foldl Term.app h)) 36 with hb | hb
  · exact .inr fun hst => hb ((stable_iff hf.1).1 hst)
  · exact .inl (goodF_stable hf hw hb)

theorem dead_stable {h : Term} {as : List Term} (ph : PureS h) (hb : fold h = 36)
    (pas : ∀ a ∈ as, PureS a) (hne : as ≠ []) : GCert.Stable (as.foldl Term.app h) := by
  obtain ⟨l, w, rfl⟩ := list_snoc as hne
  have pl : ∀ a ∈ l, PureS a := fun a ha => pas a (List.mem_append_left _ ha)
  exact ⟨l.foldl Term.app h, w, foldl_snoc _ _ _,
    no_hnf_of_bot (pure_foldl l ph pl) (fold_foldl_bot l hb pl)⟩

/-- The induction hypothesis of the Claim: it holds for runs of fewer than `K` steps. -/
def IHF (𝔐 : SModel) (N p K : Nat) : Prop :=
  ∀ k, k < K → ∀ (n r : Nat) (P P' u : Term), GCert.Run k n P u → Terminal u → n ≤ r →
    HRF 𝔐 N p r P P' → GoodF 𝔐 P P'

/-- S6, cases T and N for a frame with head `S` and at least three items: a stable frame, or
the head step on both sides.  A non-free step lowers the bound `r`, which pays for the first
item coming to the head; a free step brings `S` or a one-item term to the head.  The items
after the step are given as related (`hpost`); before it only their values are needed. -/
theorem stepS (hper : PeriodicF 𝔐 N p) {K : Nat} (IH : IHF 𝔐 N p K) {k n r : Nat}
    {u u₁ u₂ u₃ u₁' u₂' u₃' : Term} {rest rest' : List Term} (hk : k ≤ K)
    (hrun : GCert.Run k n (List.foldl Term.app S (u₁ :: u₂ :: u₃ :: rest)) u) (hu : Terminal u)
    (hn : n ≤ r) (h1 : RelF 𝔐 N p r u₁ u₁') (h2 : VP 𝔐 u₂ u₂') (h3 : VP 𝔐 u₃ u₃')
    (hpost : All₂ (RelF 𝔐 N p r) (u₃ :: (u₂ ⬝ u₃) :: rest) (u₃' :: (u₂' ⬝ u₃') :: rest')) :
    GoodF 𝔐 (List.foldl Term.app S (u₁ :: u₂ :: u₃ :: rest))
      (List.foldl Term.app S (u₁' :: u₂' :: u₃' :: rest')) := by
  have hrest : All₂ (VP 𝔐) rest rest' := by
    cases hpost with
    | cons _ h =>
      cases h with
      | cons _ h => exact h.mono fun _ _ h => h.vp hper
  have hva : All₂ (VP 𝔐) (u₁ :: u₂ :: u₃ :: rest) (u₁' :: u₂' :: u₃' :: rest') :=
    .cons (h1.vp hper) (.cons h2 (.cons h3 hrest))
  rcases good_or_ns (h := S) (h' := S) ⟨.S, .S, rfl⟩ hva (List.cons_ne_nil _ _) with g | hns
  · exact g
  · have hs : spine (List.foldl Term.app S (u₁ :: u₂ :: u₃ :: rest)) = u₁ :: u₂ :: u₃ :: rest := by
      rw [spine_foldl]; rfl
    obtain ⟨k₁, n₁, ek, en, hrun1⟩ := run_inv hrun hu hns hs
    have s : Step (List.foldl Term.app S (u₁ :: u₂ :: u₃ :: rest))
        (rest.foldl Term.app (u₁ ⬝ u₃ ⬝ (u₂ ⬝ u₃))) := step_foldl (.S u₁ u₂ u₃) rest
    have s' : Step (List.foldl Term.app S (u₁' :: u₂' :: u₃' :: rest'))
        (rest'.foldl Term.app (u₁' ⬝ u₃' ⬝ (u₂' ⬝ u₃'))) := step_foldl (.S u₁' u₂' u₃') rest'
    have key : ∃ r1, n₁ ≤ r1 ∧ HRF 𝔐 N p r1 (rest.foldl Term.app (u₁ ⬝ u₃ ⬝ (u₂ ⬝ u₃)))
        (rest'.foldl Term.app (u₁' ⬝ u₃' ⬝ (u₂' ⬝ u₃'))) := by
      cases ho : GCert.isOther u₁ with
      | true =>
        rw [ho] at en
        have en' : n = n₁ + 1 := en
        obtain ⟨r1, rfl⟩ : ∃ r1, r = r1 + 1 := ⟨r - 1, by omega⟩
        exact ⟨r1, by omega,
          hrF_foldl (hpost.mono fun _ _ h => h.mono (Nat.le_succ r1)) (hr_of_rel h1)⟩
      | false =>
        rw [ho] at en
        have en' : n = n₁ + 0 := en
        exact ⟨r, by omega, hrF_foldl hpost (hr_of_free hper h1 ho)⟩
    obtain ⟨r1, hr1, hHR⟩ := key
    exact (IH k₁ (by omega) n₁ r1 _ _ u hrun1 hu hr1 hHR).of_steps (.single s) (.single s')

/-- S6, cases T and N: the head is `S` on both sides. -/
theorem caseS (hper : PeriodicF 𝔐 N p) {K : Nat} (IH : IHF 𝔐 N p K) {k n r : Nat} {u : Term}
    {as as' : List Term} (hk : k ≤ K) (hrun : GCert.Run k n (as.foldl Term.app S) u)
    (hu : Terminal u) (hn : n ≤ r) (ha : All₂ (RelF 𝔐 N p r) as as') :
    GoodF 𝔐 (as.foldl Term.app S) (as'.foldl Term.app S) := by
  cases ha with
  | nil => exact goodF_short (.nil : All₂ (VP 𝔐) [] []) (Nat.zero_le 2) (Nat.zero_le 2)
  | cons h1 ha =>
    cases ha with
    | nil => exact goodF_short (.cons (h1.vp hper) .nil) (Nat.le_succ 1) (Nat.le_succ 1)
    | cons h2 ha =>
      cases ha with
      | nil =>
        exact goodF_short (.cons (h1.vp hper) (.cons (h2.vp hper) .nil)) (Nat.le_refl 2)
          (Nat.le_refl 2)
      | cons h3 hrest =>
        exact stepS hper IH hk hrun hu hn h1 (h2.vp hper) (h3.vp hper)
          (.cons h3 (.cons (.app h2 h3) hrest))

/-- S6, case H2: a burst pair `S^(j+1) v`, `S^(j'+1) v'` at the head with at least two
arguments, in a frame that is not stable.  Both sides run to `S v P_j Q_j r⃗` (`iterS_run`,
passing no stable frame: `nsteps_burst`); the next step is the last of the burst and gives the
(A) pairs `(P_k, P'_k')`, `(Q_k, Q'_k')` of `fib_pair`. -/
theorem caseT (hper : PeriodicF 𝔐 N p) {K : Nat} (IH : IHF 𝔐 N p K) {k n r j j' m : Nat}
    {u v v' x y x' y' : Term} {rest rest' : List Term} (hk : k ≤ K)
    (hrun : GCert.Run k n (rest.foldl Term.app (iterS j (S ⬝ v) ⬝ x ⬝ y)) u) (hu : Terminal u)
    (hn : n ≤ r) (hns : ¬ GCert.Stable (rest.foldl Term.app (iterS j (S ⬝ v) ⬝ x ⬝ y)))
    (hj : N ≤ j + 1) (hj' : N ≤ j' + 1) (hc : (j + 1) % p = (j' + 1) % p) (pv : PureS v)
    (pv' : PureS v') (cv : coreK v = 0) (cv' : coreK v' = 0) (hm : r ≤ m)
    (hA : Apx 𝔐 N p m v v') (hx : VP 𝔐 x x') (hy : VP 𝔐 y y')
    (hrest : All₂ (RelF 𝔐 N p r) rest rest') :
    GoodF 𝔐 (rest.foldl Term.app (iterS j (S ⬝ v) ⬝ x ⬝ y))
      (rest'.foldl Term.app (iterS j' (S ⬝ v') ⬝ x' ⬝ y')) := by
  have hN := hper.hN
  have st : Steps (rest.foldl Term.app (iterS j (S ⬝ v) ⬝ x ⬝ y))
      (List.foldl Term.app S (v :: (fibT j (x, y)).1 :: (fibT j (x, y)).2 :: rest)) :=
    steps_foldl (iterS_run j (S ⬝ v) x y) rest
  have st' : Steps (rest'.foldl Term.app (iterS j' (S ⬝ v') ⬝ x' ⬝ y'))
      (List.foldl Term.app S (v' :: (fibT j' (x', y')).1 :: (fibT j' (x', y')).2 :: rest')) :=
    steps_foldl (iterS_run j' (S ⬝ v') x' y') rest'
  have prest : ∀ c ∈ rest, PureS c := hrest.forall_left fun _ _ h => (h.vp hper).1
  have nst : NSteps (rest.foldl Term.app (iterS j (S ⬝ v) ⬝ x ⬝ y))
      (List.foldl Term.app S (v :: (fibT j (x, y)).1 :: (fibT j (x, y)).2 :: rest)) :=
    nsteps_head (iterS_run j (S ⬝ v) x y) (nsteps_burst j (.app .S pv) hx.1 hy.1)
      (.app (.app (iterS_pure j (.app .S pv)) hx.1) hy.1) prest hns
  obtain ⟨k₁, n₁, hk1, hn1, hrun1⟩ := run_adv nst hrun hu
  have h1 : RelF 𝔐 N p r v v' := by
    refine .grad pv pv' hm ⟨.inl (by rw [cv, cv']), ?_⟩
    rw [coreV_zero cv, coreV_zero cv']; exact hA
  have hc0 : j % p = j' % p := mod_pred hper.hp hc
  have vj := fib_vals hper (i := j) (i' := j') (by omega) (by omega) hc0 hx.2.2 hy.2.2
  have pj := fibT_pure j hx.1 hy.1
  have pj' := fibT_pure j' hx.2.1 hy.2.1
  obtain ⟨d1, d2⟩ := fib_pair hper hj hj' hc hx.1 hy.1 hx.2.1 hy.2.1 hx.2.2 hy.2.2
  rw [fibT_succ' j, fibT_succ' j'] at d1 d2
  have hpost : All₂ (RelF 𝔐 N p r)
      ((fibT j (x, y)).2 :: ((fibT j (x, y)).1 ⬝ (fibT j (x, y)).2) :: rest)
      ((fibT j' (x', y')).2 :: ((fibT j' (x', y')).1 ⬝ (fibT j' (x', y')).2) :: rest') :=
    .cons (.dead pj.2 pj'.2 d1) (.cons (.dead (.app pj.1 pj.2) (.app pj'.1 pj'.2) d2) hrest)
  exact (stepS hper IH (Nat.le_trans hk1 hk) hrun1 hu (Nat.le_trans hn1 hn) h1
    ⟨pj.1, pj'.1, vj.1⟩ ⟨pj.2, pj'.2, vj.2⟩ hpost).of_steps st st'

/-- **The Claim** (S6, proof of Theorem 9).  For a configuration `(P, P')` and a run of `P` to
its hnf or first stable frame with at most `r` non-free steps: both sides reach hnfs with items
of equal values, or stable frames with the same value pair.  Induction on the length of the run.
Cases by the head: `S` (`caseS`: T, N); an (A) pair (T: `P` is the pair or a stable frame); a
burst pair (T with at most one argument, else H2: `caseT`); a pair of cores with a level to
spare (T, or H3: head-reduce both to their two-item hnfs and replace the pair by its items, one
level lower).  S6's case H1 is `hr_chain`. -/
theorem coreF (hper : PeriodicF 𝔐 N p) : ∀ (k n r : Nat) (P P' u : Term), GCert.Run k n P u →
    Terminal u → n ≤ r → HRF 𝔐 N p r P P' → GoodF 𝔐 P P' := by
  intro k
  induction k using Nat.strongRecOn with
  | _ k IH =>
    intro n r P P' u hrun hu hn hHR
    obtain ⟨h, h', as, as', rfl, rfl, hh, ha⟩ := hHR
    have hvh := headF_vp hper hh
    have hva : All₂ (VP 𝔐) as as' := ha.mono fun _ _ h => h.vp hper
    rcases hh with ⟨rfl, rfl⟩ | ⟨ph, ph', hd⟩ |
      ⟨kk, kk', v, v', m, rfl, rfl, hkN, hkN', hc, pv, pv', cv, cv', hm, hA⟩ |
      ⟨m, ph, ph', ch, ch', hm, hA⟩
    · exact caseS hper IH (Nat.le_refl _) hrun hu hn ha
    · -- an (A) pair at the head
      cases ha with
      | nil =>
        obtain ⟨a, b, hpsi⟩ := psi_of_run 𝔐 ph hd.1 hrun hu
        exact .inr ⟨a, b, hpsi, (hd.2.2 a b).1 hpsi⟩
      | cons hx ha =>
        rcases good_or_ns hvh hva (List.cons_ne_nil _ _) with g | hns
        · exact g
        · exact (hns (dead_stable ph hd.1 (hva.forall_left fun _ _ h => h.1)
            (List.cons_ne_nil _ _))).elim
    · -- a burst pair at the head
      have hN := hper.hN
      obtain ⟨j, rfl⟩ : ∃ j, kk = j + 1 := ⟨kk - 1, by omega⟩
      obtain ⟨j', rfl⟩ : ∃ j', kk' = j' + 1 := ⟨kk' - 1, by omega⟩
      have hj : 𝔐.val (iterS j v) = 𝔐.val (iterS j' v') := by
        rw [val_iterS, val_iterS, (apx_base hA).1]
        exact hper.sit j j' (by omega) (by omega) (mod_pred hper.hp hc) _
      cases ha with
      | nil =>
        show GoodF 𝔐 (S ⬝ iterS j v) (S ⬝ iterS j' v')
        exact .inl ⟨_, _, .refl _, .inr (.inl ⟨_, rfl⟩), .refl _, .inr (.inl ⟨_, rfl⟩),
          .cons hj .nil⟩
      | @cons x x' as as' hx ha =>
        cases ha with
        | nil =>
          show GoodF 𝔐 (S ⬝ iterS j v ⬝ x) (S ⬝ iterS j' v' ⬝ x')
          exact .inl ⟨_, _, .refl _, .inr (.inr ⟨_, _, rfl⟩), .refl _, .inr (.inr ⟨_, _, rfl⟩),
            .cons hj (.cons (hx.vp hper).2.2 .nil)⟩
        | @cons y y' rest rest' hy hrest =>
          rcases good_or_ns hvh hva (List.cons_ne_nil _ _) with g | hns
          · exact g
          · have eP : List.foldl Term.app (iterS (j + 1) v) (x :: y :: rest) =
                rest.foldl Term.app (iterS j (S ⬝ v) ⬝ x ⬝ y) :=
              (congrArg (fun z => rest.foldl Term.app (z ⬝ x ⬝ y)) (iterS_succ' j v)).symm
            have eP' : List.foldl Term.app (iterS (j' + 1) v') (x' :: y' :: rest') =
                rest'.foldl Term.app (iterS j' (S ⬝ v') ⬝ x' ⬝ y') :=
              (congrArg (fun z => rest'.foldl Term.app (z ⬝ x' ⬝ y')) (iterS_succ' j' v')).symm
            rw [eP] at hrun hns
            rw [eP, eP']
            exact caseT hper IH (Nat.le_refl _) hrun hu hn hns hkN hkN' hc pv pv' cv cv' hm hA
              (hx.vp hper) (hy.vp hper) hrest
    · -- a pair of cores at the head, one level to spare
      rcases Nat.decEq (fold h) 36 with hb | hb
      · rcases core_cases ph ch with rfl | ho
        · have e' := S_of_val 𝔐 ph' hvh.2.2
          subst e'
          exact caseS hper IH (Nat.le_refl _) hrun hu hn ha
        · obtain ⟨w, hw, hwn⟩ := head_hnf ph hb
          have ef := fold_eq_of_val 𝔐 ph ph' hvh.2.2
          obtain ⟨w', hw', hwn'⟩ := head_hnf ph' (by rw [← ef]; exact hb)
          obtain ⟨hb1, hb0⟩ := other_blocks ph ho
          obtain ⟨a, b, rfl⟩ := hnf_two ph hw hwn hb1 hb0
          obtain ⟨a', b', rfl⟩ := hnf_two ph' hw' hwn' (by rw [← ef]; exact hb1)
            (by rw [← ef]; exact hb0)
          obtain ⟨sa, sb⟩ := hA.2 a b a' b' hw hw'
          have pab := steps_pure ph hw
          have pab' := steps_pure ph' hw'
          cases ha with
          | nil =>
            exact .inl ⟨_, _, hw, .inr (.inr ⟨_, _, rfl⟩), hw', .inr (.inr ⟨_, _, rfl⟩),
              .cons (simL_val hper sa) (.cons (simL_val hper sb) .nil)⟩
          | @cons x x' as as' hx ha =>
            rcases good_or_ns hvh hva (List.cons_ne_nil _ _) with g | hns
            · exact g
            · have st : Steps (List.foldl Term.app h (x :: as))
                  (List.foldl Term.app (S ⬝ a ⬝ b) (x :: as)) := steps_foldl hw _
              have st' : Steps (List.foldl Term.app h' (x' :: as'))
                  (List.foldl Term.app (S ⬝ a' ⬝ b') (x' :: as')) := steps_foldl hw' _
              have nst := nsteps_args hw ph (hva.forall_left fun _ _ h => h.1)
                (List.cons_ne_nil x as) hns
              obtain ⟨k₁, n₁, hk1, hn1, hrun1⟩ := run_adv nst hrun hu
              exact (caseS hper IH hk1 (as := a :: b :: x :: as) (as' := a' :: b' :: x' :: as')
                hrun1 hu (Nat.le_trans hn1 hn)
                (.cons (.grad pab.app_inv.1.app_inv.2 pab'.app_inv.1.app_inv.2 hm sa)
                  (.cons (.grad pab.app_inv.2 pab'.app_inv.2 hm sb) (.cons hx ha)))).of_steps
                st st'
      · cases ha with
        | nil =>
          obtain ⟨a, b, hpsi⟩ := psi_of_run 𝔐 ph hb hrun hu
          exact .inr ⟨a, b, hpsi, ((hA.1.2 (no_hnf_of_bot ph hb)) a b).1 hpsi⟩
        | cons hx ha =>
          rcases good_or_ns hvh hva (List.cons_ne_nil _ _) with g | hns
          · exact g
          · exact (hns (dead_stable ph hb (hva.forall_left fun _ _ h => h.1)
              (List.cons_ne_nil _ _))).elim

end

/-! ## (a) Theorem 9 -/

/-- **The invariant-preservation form**: if `t ≃₇₇ t'`, then `C[t]`, `C[t']` both reach hnfs
with items of equal values, or both reach stable frames with the same value pair.  The bound
`ρ ≤ 77` is `GCert.psi_skeleton`; the run exists by `TopTerm.reach_all`. -/
theorem good_of_simF (𝔐 : SModel) {N p : Nat} (hper : PeriodicF 𝔐 N p) {t t' : Term}
    (ht : PureS t) (ht' : PureS t') (h : SimF 𝔐 N p 77 t t') (C : Ctx) :
    GoodF 𝔐 (C.plug t) (C.plug t') := by
  have hrel : RelF 𝔐 N p 78 (C.plug t) (C.plug t') := rel_plugF ht ht' (Nat.le_refl 78) h C
  have hP := (hrel.vp hper).1
  obtain ⟨k, n, u, hrun, hu⟩ := run_total hP
  exact coreF hper k n 77 _ _ u hrun hu (GCert.psi_skeleton hP hrun) (hr_of_rel hrel)

/-- **Theorem 9 of S6.**  If `t ≃₇₇ t'` then `O(C[t]) = O(C[t'])` for every context `C`. -/
theorem theorem_six (𝔐 : SModel) {N p : Nat} (hper : PeriodicF 𝔐 N p) {t t' : Term}
    (ht : PureS t) (ht' : PureS t') (h : SimF 𝔐 N p 77 t t') (C : Ctx) (o : Out 𝔐.M) :
    ObsF 𝔐 (C.plug t) o ↔ ObsF 𝔐 (C.plug t') o := by
  have hrel : RelF 𝔐 N p 78 (C.plug t) (C.plug t') := rel_plugF ht ht' (Nat.le_refl 78) h C
  have hP := (hrel.vp hper).1
  have hP' := (hrel.vp hper).2.1
  have key : ∃ o₀, ObsF 𝔐 (C.plug t) o₀ ∧ ObsF 𝔐 (C.plug t') o₀ := by
    rcases good_of_simF 𝔐 hper ht ht' h C with ⟨v, v', h1, h2, h3, h4, h5⟩ | ⟨a, b, hp, hp'⟩
    · exact ⟨.hnf ((spine v).map 𝔐.val), ⟨v, h1, h2, rfl⟩, ⟨v', h3, h4, h5.map_eq⟩⟩
    · exact ⟨.bot a b, hp, hp'⟩
  obtain ⟨o₀, h0, h0'⟩ := key
  constructor
  · intro ho; rw [obsF_unique 𝔐 hP ho h0]; exact h0'
  · intro ho; rw [obsF_unique 𝔐 hP' ho h0']; exact h0

/-! ## (b) The signature -/

/-- Closed S-terms. -/
abbrev PT : Type := {t : Term // PureS t}

/-- The target of the head step of a frame of at least three items. -/
def nextOf (t : Term) : Option Term :=
  match spine t with
  | u₁ :: u₂ :: u₃ :: rest => some (rest.foldl Term.app (u₁ ⬝ u₃ ⬝ (u₂ ⬝ u₃)))
  | _ => none

theorem nextOf_step {t t' : Term} (ht : PureS t) (h : nextOf t = some t') : Step t t' := by
  unfold nextOf at h
  match hs : spine t with
  | u₁ :: u₂ :: u₃ :: rest =>
    rw [hs] at h
    have h' : some (rest.foldl Term.app (u₁ ⬝ u₃ ⬝ (u₂ ⬝ u₃))) = some t' := h
    injection h' with h'
    subst h'
    have h0 := pure_eq_foldl ht
    rw [hs] at h0
    rw [h0]
    exact step_foldl (.S u₁ u₂ u₃) rest
  | [] => rw [hs] at h; have h' : (none : Option Term) = some t' := h; cases h'
  | [_] => rw [hs] at h; have h' : (none : Option Term) = some t' := h; cases h'
  | [_, _] =>
    rw [hs] at h; have h' : (none : Option Term) = some t' := h; cases h'

theorem nextOf_none {t : Term} (ht : PureS t) (h : nextOf t = none) : IsHnf t := by
  unfold nextOf at h
  match hs : spine t with
  | u₁ :: u₂ :: u₃ :: rest =>
    rw [hs] at h
    have h' : some (rest.foldl Term.app (u₁ ⬝ u₃ ⬝ (u₂ ⬝ u₃))) = (none : Option Term) := h
    cases h'
  | [] => exact isHnf_of_short ht (by rw [hs]; exact Nat.zero_le 2)
  | [_] => exact isHnf_of_short ht (by rw [hs]; exact Nat.le_succ 1)
  | [_, _] => exact isHnf_of_short ht (by rw [hs]; exact Nat.le_refl 2)

theorem get_spec {α : Type} : ∀ {o : Option α} (h : o.isSome = true), o = some (o.get h)
  | some _, _ => rfl
  | none, h => Bool.noConfusion h

theorem none_of {α : Type} : ∀ {o : Option α}, ¬ o.isSome = true → o = none
  | none, _ => rfl
  | some _, h => absurd rfl h

/-- One head step from a frame that is not stable. -/
def Nxt (y x : PT) : Prop := stableB x.1 = false ∧ Step x.1 y.1

theorem acc_of_reach {t : Term} (h : TopTerm.Reach t) : ∀ ht : PureS t, Acc Nxt ⟨t, ht⟩ := by
  induction h with
  | hnf hu => intro ht; exact ⟨_, fun y hy => (no_step_hnf hu hy.2).elim⟩
  | @bot f w hf hb =>
    intro ht
    refine ⟨_, fun y hy => ?_⟩
    have hb' : (fold f == 36) = true := beq_iff_eq.2 hb
    have h1 : stableB (f ⬝ w) = false := hy.1
    exact Bool.noConfusion (hb'.symm.trans h1)
  | @step t t' s _ ih =>
    intro ht
    refine ⟨_, fun y hy => ?_⟩
    obtain ⟨y, py⟩ := y
    have e : y = t' := Step.det hy.2 s
    subst e
    exact ih py

/-- Head runs through non-stable frames end (`TopTerm.reach_all`). -/
theorem nxt_wf : WellFounded Nxt := ⟨fun x => acc_of_reach (TopTerm.reach_all x.2) x.2⟩

instance : WellFoundedRelation PT := ⟨Nxt, nxt_wf⟩

/-- The end of the head run: the hnf, or the first stable frame. -/
def headEnd (x : PT) : PT :=
  if hs : stableB x.1 = false then
    if hn : (nextOf x.1).isSome = true then
      headEnd ⟨(nextOf x.1).get hn, (wstep_pure (nextOf_step x.2 (get_spec hn)).weak x.2).1⟩
    else x
  else x
termination_by x
decreasing_by exact ⟨hs, nextOf_step x.2 (get_spec hn)⟩

theorem headEnd_spec (x : PT) : Steps x.1 (headEnd x).1 ∧ Terminal (headEnd x).1 := by
  refine nxt_wf.induction (C := fun x => Steps x.1 (headEnd x).1 ∧ Terminal (headEnd x).1) x ?_
  intro x ih
  rw [headEnd]
  by_cases hs : stableB x.1 = false
  · rw [dif_pos hs]
    by_cases hn : (nextOf x.1).isSome = true
    · rw [dif_pos hn]
      have s := nextOf_step x.2 (get_spec hn)
      obtain ⟨h1, h2⟩ := ih ⟨(nextOf x.1).get hn, (wstep_pure s.weak x.2).1⟩ ⟨hs, s⟩
      exact ⟨.step s h1, h2⟩
    · rw [dif_neg hn]
      exact ⟨.refl _, .inl (nextOf_none x.2 (none_of hn))⟩
  · rw [dif_neg hs]
    refine ⟨.refl _, .inr ((stableB_iff x.2).1 ?_)⟩
    cases hb : stableB x.1 with
    | true => rfl
    | false => exact absurd hb hs

/-- The end of the head run of a term with the hnf `S a b` is `S a b`. -/
theorem headEnd_hnf {v : Term} (pv : PureS v) {a b : Term} (h : Steps v (S ⬝ a ⬝ b)) :
    (headEnd ⟨v, pv⟩).1 = S ⬝ a ⬝ b := by
  obtain ⟨hs, ht⟩ := headEnd_spec ⟨v, pv⟩
  rcases ht with hh | ⟨f, w, he, hf⟩
  · exact hnf_unique hs hh h (.inr (.inr ⟨a, b, rfl⟩))
  · exfalso
    have hs2 : Steps v (headEnd ⟨v, pv⟩).1 := hs
    rw [he] at hs2
    have pfw := steps_pure pv hs2
    exact fold_hnf (steps_pure pv h) (.inr (.inr ⟨a, b, rfl⟩))
      ((steps_fold pv h).trans ((steps_fold pv hs2).symm.trans
        (fold_frame pfw.app_inv.2 (bot_of_nohnf pfw.app_inv.1 hf))))

/-- The end of the head run of an hnf-less term is a stable frame. -/
theorem headEnd_stable {v : Term} (pv : PureS v) (hn : ¬ HasHnf v) :
    ∃ f w, (headEnd ⟨v, pv⟩).1 = f ⬝ w ∧ fold f = 36 ∧ Steps v (f ⬝ w) := by
  obtain ⟨hs, ht⟩ := headEnd_spec ⟨v, pv⟩
  rcases ht with hh | ⟨f, w, he, hf⟩
  · exact (hn ⟨_, hs.weak, hh⟩).elim
  · have hs2 : Steps v (headEnd ⟨v, pv⟩).1 := hs
    rw [he] at hs2
    exact ⟨f, w, he, bot_of_nohnf (steps_pure pv hs2).app_inv.1 hf, hs2⟩

/-- Signatures at level `n` (for `≃_{n−1}`): the class of `k`, the value of the core, `Ψ` of the
core if it has no hnf, and from level 1 on the signatures of the two items of its hnf. -/
def SigT (m c : Nat) : Nat → Type
  | 0 => Fin c × Fin m × Option (Fin m × Fin m)
  | n + 1 => (Fin c × Fin m × Option (Fin m × Fin m)) × Option (SigT m c n × SigT m c n)

/-- The class of `k` under `∼`: `k` itself below `N`, else `N + (k − N) mod p`. -/
def kcls (N p k : Nat) : Nat := if k < N then k else N + (k - N) % p

theorem kcls_lt {N p : Nat} (hp : 0 < p) (k : Nat) : kcls N p k < N + p := by
  unfold kcls
  rcases Nat.decLt k N with hk | hk
  · rw [if_neg hk]; exact Nat.add_lt_add_left (Nat.mod_lt _ hp) N
  · rw [if_pos hk]; exact Nat.lt_of_lt_of_le hk (Nat.le_add_right N p)

theorem kcls_tow {N p k k' : Nat} (h : kcls N p k = kcls N p k') : TowRel N p k k' := by
  unfold kcls at h
  rcases Nat.decLt k N with hk | hk
  · rw [if_neg hk] at h
    rcases Nat.decLt k' N with hk' | hk'
    · rw [if_neg hk'] at h
      have hk1 := Nat.le_of_not_lt hk
      have hk1' := Nat.le_of_not_lt hk'
      have hm : (k - N) % p = (k' - N) % p := Nat.add_left_cancel h
      have a1 : k % p = ((k - N) % p + N % p) % p := by
        rw [← Nat.add_mod, Nat.sub_add_cancel hk1]
      have a2 : k' % p = ((k' - N) % p + N % p) % p := by
        rw [← Nat.add_mod, Nat.sub_add_cancel hk1']
      exact .inr ⟨hk1, hk1', by rw [a1, a2, hm]⟩
    · rw [if_pos hk'] at h
      have := Nat.le_add_right N ((k - N) % p)
      rw [h] at this
      exact absurd hk' (Nat.not_lt.mpr this)
  · rw [if_pos hk] at h
    rcases Nat.decLt k' N with hk' | hk'
    · rw [if_neg hk'] at h
      have := Nat.le_add_right N ((k' - N) % p)
      rw [← h] at this
      exact absurd hk (Nat.not_lt.mpr this)
    · rw [if_pos hk'] at h
      exact .inl h

/-- `Ψ` read off the end of the head run. -/
def psiOf (𝔐 : SModel) {m : Nat} (code : 𝔐.M → Fin m) : Term → Option (Fin m × Fin m)
  | .app f w => if fold f = 36 then some (code (𝔐.val f), code (𝔐.val w)) else none
  | _ => none

theorem psiOf_bot (𝔐 : SModel) {m : Nat} (code : 𝔐.M → Fin m) {f w : Term} (hb : fold f = 36) :
    psiOf 𝔐 code (f ⬝ w) = some (code (𝔐.val f), code (𝔐.val w)) := by
  show (if fold f = 36 then some (code (𝔐.val f), code (𝔐.val w)) else none) = _
  rw [if_pos hb]

theorem psiOf_some (𝔐 : SModel) {m : Nat} (code : 𝔐.M → Fin m) : ∀ {e : Term} {c d : Fin m},
    psiOf 𝔐 code e = some (c, d) →
    ∃ f w, e = f ⬝ w ∧ fold f = 36 ∧ c = code (𝔐.val f) ∧ d = code (𝔐.val w)
  | .app f w, c, d, h => by
    have h' : (if fold f = 36 then some (code (𝔐.val f), code (𝔐.val w)) else none) =
        some (c, d) := h
    rcases Nat.decEq (fold f) 36 with hb | hb
    · rw [if_neg hb] at h'; cases h'
    · rw [if_pos hb] at h'
      have e := Option.some.inj h'
      exact ⟨f, w, rfl, hb, (congrArg Prod.fst e).symm, (congrArg Prod.snd e).symm⟩
  | .S, c, d, h => by have h' : (none : Option (Fin m × Fin m)) = some (c, d) := h; cases h'
  | .K, c, d, h => by have h' : (none : Option (Fin m × Fin m)) = some (c, d) := h; cases h'
  | .I, c, d, h => by have h' : (none : Option (Fin m × Fin m)) = some (c, d) := h; cases h'

/-- The two items of an hnf `S a b`. -/
def itemsOf : (e : Term) → PureS e → Option (PT × PT)
  | .app (.app .S a) b, he => some (⟨a, he.app_inv.1.app_inv.2⟩, ⟨b, he.app_inv.2⟩)
  | _, _ => none

theorem itemsOf_eq {e : Term} (he : PureS e) {a b : Term} (h : e = S ⬝ a ⬝ b) :
    ∃ pa pb, itemsOf e he = some (⟨a, pa⟩, ⟨b, pb⟩) := by
  subst h
  exact ⟨_, _, rfl⟩

/-- The level-0 signature. -/
def sig0 (𝔐 : SModel) {m : Nat} (code : 𝔐.M → Fin m) (N p : Nat) (hp : 0 < p) (t : PT) :
    Fin (N + p) × Fin m × Option (Fin m × Fin m) :=
  (⟨kcls N p (coreK t.1), kcls_lt hp _⟩, code (𝔐.val (coreV t.1)),
    psiOf 𝔐 code (headEnd ⟨coreV t.1, coreV_pure t.2⟩).1)

/-- **The signature map.**  `sig n` is computable and takes values in `SigT m (N + p) n`. -/
def sig (𝔐 : SModel) {m : Nat} (code : 𝔐.M → Fin m) (N p : Nat) (hp : 0 < p) :
    (n : Nat) → PT → SigT m (N + p) n
  | 0, t => sig0 𝔐 code N p hp t
  | n + 1, t => (sig0 𝔐 code N p hp t,
      (itemsOf (headEnd ⟨coreV t.1, coreV_pure t.2⟩).1 (headEnd ⟨coreV t.1, coreV_pure t.2⟩).2).map
        fun q => (sig 𝔐 code N p hp n q.1, sig 𝔐 code N p hp n q.2))

theorem sig0_sound (𝔐 : SModel) {m : Nat} (code : 𝔐.M → Fin m)
    (inj : ∀ a b, code a = code b → a = b) (N p : Nat) (hp : 0 < p) {t t' : PT}
    (h : sig0 𝔐 code N p hp t = sig0 𝔐 code N p hp t') :
    TowRel N p (coreK t.1) (coreK t'.1) ∧ Base0 𝔐 (coreV t.1) (coreV t'.1) := by
  have h1 : kcls N p (coreK t.1) = kcls N p (coreK t'.1) := congrArg (fun z => z.1.1) h
  have h2 : code (𝔐.val (coreV t.1)) = code (𝔐.val (coreV t'.1)) :=
    congrArg (fun z => z.2.1) h
  have h3 : psiOf 𝔐 code (headEnd ⟨coreV t.1, coreV_pure t.2⟩).1 =
      psiOf 𝔐 code (headEnd ⟨coreV t'.1, coreV_pure t'.2⟩).1 := congrArg (fun z => z.2.2) h
  refine ⟨kcls_tow h1, inj _ _ h2, fun hn a b => ?_⟩
  obtain ⟨f, w, he, hb, hs⟩ := headEnd_stable (coreV_pure t.2) hn
  have pfw := steps_pure (coreV_pure t.2) hs
  rw [he, psiOf_bot 𝔐 code hb] at h3
  obtain ⟨f', w', he', hb', ec, ed⟩ := psiOf_some 𝔐 code h3.symm
  have hs' : Steps (coreV t'.1) (headEnd ⟨coreV t'.1, coreV_pure t'.2⟩).1 :=
    (headEnd_spec ⟨coreV t'.1, coreV_pure t'.2⟩).1
  rw [he'] at hs'
  have pfw' := steps_pure (coreV_pure t'.2) hs'
  have P1 : Psi 𝔐 (coreV t.1) (𝔐.val f) (𝔐.val w) :=
    ⟨f, w, hs, no_hnf_of_bot pfw.app_inv.1 hb, rfl, rfl⟩
  have P2 : Psi 𝔐 (coreV t'.1) (𝔐.val f) (𝔐.val w) :=
    ⟨f', w', hs', no_hnf_of_bot pfw'.app_inv.1 hb', inj _ _ ec, inj _ _ ed⟩
  constructor
  · intro h
    obtain ⟨e1, e2⟩ := psi_unique 𝔐 (coreV_pure t.2) h P1
    rw [e1, e2]; exact P2
  · intro h
    obtain ⟨e1, e2⟩ := psi_unique 𝔐 (coreV_pure t'.2) h P2
    rw [e1, e2]; exact P1

/-- **Finite index of `≃_{n−1}`, constructively.**  For a model with an injective coding of its
values in `Fin m`, equal signatures at level `n` imply `SimL n`. -/
theorem sig_sound (𝔐 : SModel) {m : Nat} (code : 𝔐.M → Fin m)
    (inj : ∀ a b, code a = code b → a = b) (N p : Nat) (hp : 0 < p) :
    ∀ (n : Nat) (t t' : PT), sig 𝔐 code N p hp n t = sig 𝔐 code N p hp n t' →
      SimL 𝔐 N p n t.1 t'.1
  | 0, _, _, h => sig0_sound 𝔐 code inj N p hp h
  | n + 1, t, t', h => by
    have h1 : sig0 𝔐 code N p hp t = sig0 𝔐 code N p hp t' := congrArg Prod.fst h
    have h2 : (itemsOf (headEnd ⟨coreV t.1, coreV_pure t.2⟩).1
          (headEnd ⟨coreV t.1, coreV_pure t.2⟩).2).map
          (fun q => (sig 𝔐 code N p hp n q.1, sig 𝔐 code N p hp n q.2)) =
        (itemsOf (headEnd ⟨coreV t'.1, coreV_pure t'.2⟩).1
          (headEnd ⟨coreV t'.1, coreV_pure t'.2⟩).2).map
          (fun q => (sig 𝔐 code N p hp n q.1, sig 𝔐 code N p hp n q.2)) := congrArg Prod.snd h
    obtain ⟨hk, hb⟩ := sig0_sound 𝔐 code inj N p hp h1
    refine ⟨hk, hb, fun a b a' b' hs hs' => ?_⟩
    obtain ⟨pa, pb, ei⟩ := itemsOf_eq (headEnd ⟨coreV t.1, coreV_pure t.2⟩).2
      (headEnd_hnf (coreV_pure t.2) hs)
    obtain ⟨pa', pb', ei'⟩ := itemsOf_eq (headEnd ⟨coreV t'.1, coreV_pure t'.2⟩).2
      (headEnd_hnf (coreV_pure t'.2) hs')
    rw [ei, ei'] at h2
    have h3 : (sig 𝔐 code N p hp n ⟨a, pa⟩, sig 𝔐 code N p hp n ⟨b, pb⟩) =
        (sig 𝔐 code N p hp n ⟨a', pa'⟩, sig 𝔐 code N p hp n ⟨b', pb'⟩) := Option.some.inj h2
    exact ⟨sig_sound 𝔐 code inj N p hp n ⟨a, pa⟩ ⟨a', pa'⟩ (congrArg Prod.fst h3),
      sig_sound 𝔐 code inj N p hp n ⟨b, pb⟩ ⟨b', pb'⟩ (congrArg Prod.snd h3)⟩

/-- The number of signatures at level `n`, for `|M| = m` and `c = N + p` classes of `k`. -/
def sigBound (m c : Nat) : Nat → Nat
  | 0 => c * (m * (m * m + 1))
  | n + 1 => (c * (m * (m * m + 1))) * (sigBound m c n * sigBound m c n + 1)

def pairF {a b : Nat} (i : Fin a) (j : Fin b) : Fin (a * b) :=
  ⟨i.1 * b + j.1, Nat.lt_of_lt_of_le (Nat.add_lt_add_left j.2 _)
    (by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right b i.2)⟩

def optF {a : Nat} : Option (Fin a) → Fin (a + 1)
  | none => ⟨a, Nat.lt_succ_self a⟩
  | some i => ⟨i.1, Nat.lt_succ_of_lt i.2⟩

def baseCode {m c : Nat} (x : Fin c × Fin m × Option (Fin m × Fin m)) :
    Fin (c * (m * (m * m + 1))) :=
  pairF x.1 (pairF x.2.1 (optF (x.2.2.map fun q => pairF q.1 q.2)))

/-- Signatures at level `n`, numbered below `sigBound m c n`. -/
def sigCode {m c : Nat} : (n : Nat) → SigT m c n → Fin (sigBound m c n)
  | 0, x => baseCode x
  | n + 1, x => pairF (baseCode x.1)
      (optF (x.2.map fun q => pairF (sigCode n q.1) (sigCode n q.2)))

theorem pairF_inj {a b : Nat} {i i' : Fin a} {j j' : Fin b} (h : pairF i j = pairF i' j') :
    i = i' ∧ j = j' := by
  have hv : i.1 * b + j.1 = i'.1 * b + j'.1 := congrArg Fin.val h
  have hb : 0 < b := Nat.lt_of_le_of_lt (Nat.zero_le _) j.2
  have d : ∀ (x y : Nat), y < b → (x * b + y) / b = x := fun x y hy => by
    rw [Nat.mul_comm, Nat.mul_add_div hb, Nat.div_eq_of_lt hy, Nat.add_zero]
  have r : ∀ (x y : Nat), y < b → (x * b + y) % b = y := fun x y hy => by
    rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hy]
  have e1 : i.1 = i'.1 :=
    (d i.1 j.1 j.2).symm.trans ((congrArg (fun z => z / b) hv).trans (d i'.1 j'.1 j'.2))
  have e2 : j.1 = j'.1 :=
    (r i.1 j.1 j.2).symm.trans ((congrArg (fun z => z % b) hv).trans (r i'.1 j'.1 j'.2))
  exact ⟨Fin.eq_of_val_eq e1, Fin.eq_of_val_eq e2⟩

theorem optF_inj {a : Nat} : ∀ {x y : Option (Fin a)}, optF x = optF y → x = y
  | none, none, _ => rfl
  | none, some i, h => by
    have hv : (optF (none : Option (Fin a))).1 = (optF (some i)).1 := congrArg Fin.val h
    exact absurd (hv : a = i.1) (Nat.ne_of_gt i.2)
  | some i, none, h => by
    have hv : (optF (some i)).1 = (optF (none : Option (Fin a))).1 := congrArg Fin.val h
    exact absurd (hv : i.1 = a) (Nat.ne_of_lt i.2)
  | some i, some i', h => by
    have hv : (optF (some i)).1 = (optF (some i')).1 := congrArg Fin.val h
    exact congrArg some (Fin.eq_of_val_eq (hv : i.1 = i'.1))

theorem optmap_inj {α β : Type} {f : α → β} (hf : ∀ x y, f x = f y → x = y) :
    ∀ {o o' : Option α}, o.map f = o'.map f → o = o'
  | none, none, _ => rfl
  | none, some y, h => by have h' : (none : Option β) = some (f y) := h; cases h'
  | some x, none, h => by have h' : some (f x) = (none : Option β) := h; cases h'
  | some x, some y, h => congrArg some (hf x y (Option.some.inj h))

theorem pair2_inj {a b : Nat} : ∀ (x y : Fin a × Fin b), pairF x.1 x.2 = pairF y.1 y.2 → x = y :=
  fun _ _ h => Prod.ext (pairF_inj h).1 (pairF_inj h).2

theorem baseCode_inj {m c : Nat} (x y : Fin c × Fin m × Option (Fin m × Fin m))
    (h : baseCode x = baseCode y) : x = y := by
  obtain ⟨h1, h2⟩ := pairF_inj h
  obtain ⟨h3, h4⟩ := pairF_inj h2
  exact Prod.ext h1 (Prod.ext h3 (optmap_inj pair2_inj (optF_inj h4)))

/-- **The bound.**  `sigCode` is injective, so there are at most `sigBound m (N + p) n`
signatures at level `n`. -/
theorem sigCode_inj {m c : Nat} : ∀ (n : Nat) (x y : SigT m c n),
    sigCode n x = sigCode n y → x = y
  | 0, x, y, h => baseCode_inj x y h
  | n + 1, x, y, h => by
    have h' : pairF (baseCode x.1)
          (optF (x.2.map fun q => pairF (sigCode n q.1) (sigCode n q.2))) =
        pairF (baseCode y.1)
          (optF (y.2.map fun q => pairF (sigCode n q.1) (sigCode n q.2))) := h
    obtain ⟨h1, h2⟩ := pairF_inj h'
    have e2 : x.2 = y.2 := optmap_inj (fun u v huv =>
      Prod.ext (sigCode_inj n u.1 v.1 (pairF_inj huv).1) (sigCode_inj n u.2 v.2 (pairF_inj huv).2))
      (optF_inj h2)
    exact Prod.ext (baseCode_inj x.1 y.1 h1) e2

/-- Terms with equal signatures at level 78 (for `≃₇₇`) have equal observables in every
context: the syntactic congruence of `O` has at most `sigBound m (N + p) 78` classes. -/
theorem sig_congruence (𝔐 : SModel) {m : Nat} (code : 𝔐.M → Fin m)
    (inj : ∀ a b, code a = code b → a = b) {N p : Nat} (hper : PeriodicF 𝔐 N p) (t t' : PT)
    (h : sig 𝔐 code N p hper.hp 78 t = sig 𝔐 code N p hper.hp 78 t') (C : Ctx) (o : Out 𝔐.M) :
    ObsF 𝔐 (C.plug t.1) o ↔ ObsF 𝔐 (C.plug t'.1) o :=
  theorem_six 𝔐 hper t.2 t'.2 (sig_sound 𝔐 code inj N p hper.hp 78 t t' h) C o

/-! ## Sanity: the hypotheses are satisfiable -/

theorem apx_refl (𝔐 : SModel) (N p : Nat) : ∀ (n : Nat) (v : Term), Apx 𝔐 N p n v v
  | 0, _ => ⟨rfl, fun _ _ _ => Iff.rfl⟩
  | n + 1, v => ⟨⟨rfl, fun _ _ _ => Iff.rfl⟩, fun a b a' b' hs hs' => by
      have e := hnf_unique hs (.inr (.inr ⟨a, b, rfl⟩)) hs' (.inr (.inr ⟨a', b', rfl⟩))
      injection e with e1 e2
      injection e1 with _ e1
      subst e1; subst e2
      exact ⟨⟨.inl rfl, apx_refl 𝔐 N p n _⟩, ⟨.inl rfl, apx_refl 𝔐 N p n _⟩⟩⟩

/-- `≃_g` is reflexive, so the hypothesis of Theorem 9 is not vacuous. -/
theorem simL_refl (𝔐 : SModel) (N p n : Nat) (t : Term) : SimL 𝔐 N p n t t :=
  ⟨.inl rfl, apx_refl 𝔐 N p n _⟩

/-- Eight iterations of `σ` on blocks. -/
def sit8 (m : Nat) : Nat := β 0 (β 0 (β 0 (β 0 (β 0 (β 0 (β 0 (β 0 m)))))))

def sitB : Bool := r38.all fun m => β 0 (sit8 m) == sit8 m
theorem sitB_eq : sitB = true := by decide +kernel

/-- `σ^k` on blocks. -/
def sitN : Nat → Nat → Nat
  | 0, m => m
  | k + 1, m => β 0 (sitN k m)

theorem s1_sIter : ∀ (k : Nat) (m : Fin 38), (s1Model.sIter k m).1 = sitN k m.1
  | 0, _ => rfl
  | k + 1, m => congrArg (β 0) (s1_sIter k m)

theorem sitN_const {m : Nat} (hm : m < 38) : ∀ j : Nat, sitN (j + 8) m = sit8 m
  | 0 => rfl
  | j + 1 => by
    have h := sitB_eq
    simp only [sitB, r38, List.all_eq_true, List.mem_range, beq_iff_eq] at h
    show β 0 (sitN (j + 8) m) = sit8 m
    rw [sitN_const hm j]; exact h m hm

/-- **S1 satisfies the hypotheses with `N = 10`, `p = 1`**: `σ^j` is constant from `j = 8` on
(`sitB_eq`), and so is `φ^j` (`fib8B_eq`). -/
theorem s1_periodicF : PeriodicF s1Model 10 1 := by
  have sit : ∀ (k : Nat), 8 ≤ k → ∀ m : Fin 38, (s1Model.sIter k m).1 = sit8 m.1 := by
    intro k hk m
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 8 := ⟨k - 8, by omega⟩
    rw [s1_sIter, sitN_const m.2 j]
  have dead : ∀ (k : Nat), 8 ≤ k → ∀ q : Fin 38 × Fin 38,
      ((s1Model.fibM k q).1.1, (s1Model.fibM k q).2.1) = (36, 36) := by
    intro k hk q
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 8 := ⟨k - 8, by omega⟩
    rw [s1_fib, fibB_dead j q.1.2 q.2.2]
  refine ⟨by decide, by decide, fun k k' hk hk' _ m => ?_, fun k k' hk hk' _ q => ?_⟩
  · exact Fin.eq_of_val_eq ((sit k hk m).trans (sit k' hk' m).symm)
  · have e := dead k hk q
    have e' := dead k' hk' q
    exact Prod.ext (Fin.eq_of_val_eq ((congrArg Prod.fst e).trans (congrArg Prod.fst e').symm))
      (Fin.eq_of_val_eq ((congrArg Prod.snd e).trans (congrArg Prod.snd e').symm))

/-- Theorem 9 for S1's own labels (`N = 10`, `p = 1`), from signatures: equal signatures at
level 78 give equal observables in every context; there are at most `sigBound 38 11 78`
signatures. -/
theorem sig_congruence_s1 (t t' : PT)
    (h : sig s1Model id 10 1 s1_periodicF.hp 78 t = sig s1Model id 10 1 s1_periodicF.hp 78 t')
    (C : Ctx) (o : Out (Fin 38)) : ObsF s1Model (C.plug t.1) o ↔ ObsF s1Model (C.plug t'.1) o :=
  sig_congruence s1Model id (fun _ _ h => h) s1_periodicF t t' h C o

end Full
