import Ski.TopTermMain
open Term

/-!
# Every infinite reduction of a finite S-term converges (S2, Thm. 6)

`WStepD e t u`: a contraction at depth `e`.  A *reduction* `σ : ℕ → Term` may stutter
(`σ n = σ (n+1)`), so that its projections to subterms are reductions again.  `WeakInf D σ`:
steps at depth `≤ D` occur arbitrarily late, in the doubly negated form
`∀ N, ¬¬ ∃ n ≥ N, …`, which is stronger as a hypothesis-to-refute than `∀ N, ∃ n ≥ N, …`.

* `hrun_bound`: the head path of a closed S-term has a bound on its root steps (from
  `TopTerm.reach_all`), so every reduction does (`root_bound`, by `TopTerm.bridge`);
* `not_weakInf`: no reduction from a finite closed S-term makes steps at depth `≤ D` arbitrarily
  late, by induction on `D`: after the last root step the reduction projects to the two halves.
  The proof stays inside the double-negation monad, so it needs no classical logic.
-/

namespace InfSN
open HnfS TopTerm

inductive WStepD : Nat → Term → Term → Prop
  | S (f g x : Term) : WStepD 0 (S ⬝ f ⬝ g ⬝ x) (f ⬝ x ⬝ (g ⬝ x))
  | left {e : Nat} {f f' : Term} (x : Term) : WStepD e f f' → WStepD (e + 1) (f ⬝ x) (f' ⬝ x)
  | right {e : Nat} {x x' : Term} (f : Term) : WStepD e x x' → WStepD (e + 1) (f ⬝ x) (f ⬝ x')

theorem WStepD.weak {e : Nat} {t u : Term} (h : WStepD e t u) : WStep t u := by
  induction h with
  | S f g x => exact .S f g x
  | left x _ ih => exact .left x ih
  | right f _ ih => exact .right f ih

/-- Every weak step of a pure term has a depth. -/
theorem wstep_depth {t u : Term} (ht : PureS t) (h : WStep t u) : ∃ e, WStepD e t u := by
  induction h with
  | S f g x => exact ⟨0, .S f g x⟩
  | K => cases ht with | app h _ => cases h with | app h _ => cases h
  | I => cases ht with | app h _ => cases h
  | left x _ ih => obtain ⟨e, he⟩ := ih ht.app_inv.1; exact ⟨e + 1, .left x he⟩
  | right f _ ih => obtain ⟨e, he⟩ := ih ht.app_inv.2; exact ⟨e + 1, .right f he⟩

/-- A reduction sequence, possibly stuttering. -/
def Red (σ : Nat → Term) : Prop := ∀ n, σ n = σ (n + 1) ∨ ∃ e, WStepD e (σ n) (σ (n + 1))

def StepLe (D : Nat) (t u : Term) : Prop := ∃ e, e ≤ D ∧ WStepD e t u

/-- Steps at depth `≤ D` occur arbitrarily late (doubly negated). -/
def WeakInf (D : Nat) (σ : Nat → Term) : Prop := ∀ N, ¬¬ ∃ n, N ≤ n ∧ StepLe D (σ n) (σ (n + 1))

/-! ## A bound on root steps -/

theorem hrun_hnf {u v : Term} (hu : IsHnf u) : ∀ {k : Nat}, HRun k u v → k = 0 := by
  intro k h
  cases h with
  | refl => rfl
  | head s _ => exact absurd s (fun s => no_step_hnf hu s)
  | root _ => rcases hu with h | ⟨x, h⟩ | ⟨x, y, h⟩ <;> cases h

theorem hrun_bound {t : Term} (h : Reach t) : ∃ B, ∀ k v, HRun k t v → k ≤ B := by
  induction h with
  | hnf hu => exact ⟨0, fun k v h => Nat.le_of_eq (hrun_hnf hu h)⟩
  | bot hf hb => exact ⟨0, fun k v h => Nat.le_of_eq (hrun_bot_fun h rfl hf hb)⟩
  | step s _ ih =>
    obtain ⟨B, hB⟩ := ih
    refine ⟨B + 1, fun k v h => ?_⟩
    cases k with
    | zero => exact Nat.zero_le _
    | succ k =>
      obtain ⟨v', hv'⟩ := HRun.step s h
      exact Nat.succ_le_succ (hB k v' hv')

theorem root_bound {t : Term} (ht : PureS t) : ∃ B, ∀ k u, RSteps k t u → k ≤ B := by
  obtain ⟨B, hB⟩ := hrun_bound (reach_all ht)
  exact ⟨B, fun k u h => by obtain ⟨v, hv⟩ := bridge k h; exact hB k v hv⟩

/-! ## Reductions -/

theorem red_wsteps {σ : Nat → Term} (hr : Red σ) (m : Nat) : ∀ d, WSteps (σ m) (σ (m + d)) := by
  intro d
  induction d with
  | zero => exact .refl _
  | succ d ih =>
    rcases hr (m + d) with e | ⟨_, he⟩
    · rw [← Nat.add_assoc, ← e]; exact ih
    · rw [← Nat.add_assoc]; exact ih.trans (.single he.weak)

theorem red_le {σ : Nat → Term} (hr : Red σ) {m n : Nat} (h : m ≤ n) : WSteps (σ m) (σ n) := by
  have := red_wsteps hr m (n - m)
  rwa [Nat.add_sub_cancel' h] at this

theorem red_pure {σ : Nat → Term} (hr : Red σ) (h0 : PureS (σ 0)) (n : Nat) : PureS (σ n) := by
  have := red_le hr (Nat.zero_le n)
  exact (HnfS.fold_wsteps this h0).1

/-! ## Depth 0 -/

theorem root_of_stepLe0 {t u : Term} (h : StepLe 0 t u) : ∃ f g x, t = S ⬝ f ⬝ g ⬝ x ∧ u = f ⬝ x ⬝ (g ⬝ x) := by
  obtain ⟨e, he, hs⟩ := h
  have : e = 0 := Nat.le_zero.mp he
  subst this
  cases hs with
  | S f g x => exact ⟨f, g, x, rfl, rfl⟩

theorem weakInf0_rsteps {σ : Nat → Term} (hr : Red σ) (hw : WeakInf 0 σ) :
    ∀ k m, ¬¬ ∃ u, RSteps k (σ m) u := by
  intro k
  induction k with
  | zero => intro m h; exact h ⟨σ m, .refl _⟩
  | succ k ih =>
    intro m hneg
    apply hw m
    rintro ⟨n, hmn, hs⟩
    apply ih (n + 1)
    rintro ⟨u, hu⟩
    obtain ⟨f, g, x, e1, e2⟩ := root_of_stepLe0 hs
    apply hneg
    refine ⟨u, RSteps.of_wsteps (red_le hr hmn) ?_⟩
    rw [e1]; rw [e2] at hu
    exact .root hu

theorem not_weakInf0 {σ : Nat → Term} (hr : Red σ) (h0 : PureS (σ 0)) : ¬ WeakInf 0 σ := by
  intro hw
  obtain ⟨B, hB⟩ := root_bound h0
  apply weakInf0_rsteps hr hw (B + 1) 0
  rintro ⟨u, hu⟩
  exact absurd (hB _ u hu) (Nat.not_succ_le_self B)

/-- From `¬ WeakInf D σ`: not never, eventually no step at depth `≤ D`. -/
theorem eventually_none {D : Nat} {σ : Nat → Term} (h : ¬ WeakInf D σ) :
    ¬¬ ∃ N, ∀ n, N ≤ n → ¬ StepLe D (σ n) (σ (n + 1)) := by
  intro hn
  apply h
  intro N hN
  exact hn ⟨N, fun n hn' hs => hN ⟨n, hn', hs⟩⟩

/-! ## Projection after the last root step -/

def fnPart : Term → Term
  | .app f _ => f
  | t => t

def argPart : Term → Term
  | .app _ x => x
  | t => t

theorem stepLe_succ_inv {D : Nat} {a b v : Term} (h : StepLe (D + 1) (a ⬝ b) v)
    (hr : ¬ StepLe 0 (a ⬝ b) v) :
    (∃ a', v = a' ⬝ b ∧ StepLe D a a') ∨ (∃ b', v = a ⬝ b' ∧ StepLe D b b') := by
  obtain ⟨e, he, hs⟩ := h
  cases e with
  | zero => exact absurd ⟨0, Nat.le_refl 0, hs⟩ hr
  | succ e =>
    cases hs with
    | left _ h => exact .inl ⟨_, rfl, e, Nat.le_of_succ_le_succ he, h⟩
    | right _ h => exact .inr ⟨_, rfl, e, Nat.le_of_succ_le_succ he, h⟩

theorem wstepD_app {e : Nat} {t v : Term} (h : WStepD e t v) : ∃ c d, v = c ⬝ d := by
  cases h with
  | S f g x => exact ⟨_, _, rfl⟩
  | left x _ => exact ⟨_, _, rfl⟩
  | right f _ => exact ⟨_, _, rfl⟩

theorem wstepD_app_inv {e : Nat} {a b c d : Term} (h : WStepD (e + 1) (a ⬝ b) (c ⬝ d)) :
    (WStepD e a c ∧ d = b) ∨ (WStepD e b d ∧ c = a) := by
  cases h with
  | left _ h => exact .inl ⟨h, rfl⟩
  | right _ h => exact .inr ⟨h, rfl⟩

/-- A reduction from `S` stays at `S` and makes no step. -/
theorem red_S {σ : Nat → Term} (hr : Red σ) {N : Nat} (hS : σ N = S) : ∀ k, σ (N + k) = S := by
  intro k
  induction k with
  | zero => exact hS
  | succ k ih =>
    rcases hr (N + k) with e | ⟨e, hs⟩
    · rw [← Nat.add_assoc, ← e, ih]
    · rw [ih] at hs; cases hs

/-- **Every infinite reduction from a finite closed S-term converges** (S2, Thm. 6): steps at
depth `≤ D` do not occur arbitrarily late. -/
theorem not_weakInf : ∀ (D : Nat) {σ : Nat → Term}, Red σ → PureS (σ 0) → ¬ WeakInf D σ := by
  intro D
  induction D with
  | zero => intro σ hr h0; exact not_weakInf0 hr h0
  | succ D ih =>
    intro σ hr h0 hw
    -- not never: from some `N` on, no root step
    apply eventually_none (not_weakInf0 hr h0)
    rintro ⟨N, hN⟩
    have hp := red_pure hr h0
    let τ : Nat → Term := fun m => σ (N + m)
    have hrτ : ∀ m, τ m = τ (m + 1) ∨ ∃ e, WStepD e (τ m) (τ (m + 1)) := by
      intro m; simp only [τ]; rw [← Nat.add_assoc]; exact hr (N + m)
    have hnr : ∀ m, ¬ StepLe 0 (τ m) (τ (m + 1)) := by
      intro m; simp only [τ]; rw [← Nat.add_assoc]; exact hN _ (Nat.le_add_right N m)
    match hσN : σ N with
    | .S =>
      apply hw N
      rintro ⟨n, hn, hs⟩
      obtain ⟨k, rfl⟩ : ∃ k, n = N + k := ⟨n - N, by omega⟩
      have h1 := red_S hr hσN k
      rw [h1] at hs
      obtain ⟨e, _, hs⟩ := hs
      cases hs
    | .K => have := hp N; rw [hσN] at this; cases this
    | .I => have := hp N; rw [hσN] at this; cases this
    | .app a0 b0 =>
      have shape : ∀ m, ∃ a b, τ m = a ⬝ b := by
        intro m
        induction m with
        | zero => exact ⟨a0, b0, hσN⟩
        | succ m ihm =>
          rcases hrτ m with e | ⟨e, hs⟩
          · obtain ⟨a, b, h⟩ := ihm; exact ⟨a, b, e ▸ h⟩
          · exact wstepD_app hs
      let L : Nat → Term := fun m => fnPart (τ m)
      let R : Nat → Term := fun m => argPart (τ m)
      have hLR : ∀ m, τ m = L m ⬝ R m := by
        intro m
        obtain ⟨a, b, h⟩ := shape m
        simp only [L, R, h, fnPart, argPart]
      -- each step after `N` is a step of the left part or of the right part
      have split : ∀ m, τ m = τ (m + 1) ∨
          (∃ e, WStepD e (L m) (L (m + 1)) ∧ R (m + 1) = R m) ∨
          (∃ e, WStepD e (R m) (R (m + 1)) ∧ L (m + 1) = L m) := by
        intro m
        rcases hrτ m with e | ⟨e, hs⟩
        · exact .inl e
        · have hs' := hs
          rw [hLR m, hLR (m + 1)] at hs'
          cases e with
          | zero => exact absurd ⟨0, Nat.le_refl 0, hs⟩ (hnr m)
          | succ e =>
            rcases wstepD_app_inv hs' with ⟨h, e2⟩ | ⟨h, e2⟩
            · exact .inr (.inl ⟨e, h, e2⟩)
            · exact .inr (.inr ⟨e, h, e2⟩)
      have hL : Red L := by
        intro m
        rcases split m with e | ⟨e, h, _⟩ | ⟨_, _, e2⟩
        · exact .inl (by simp only [L]; rw [e])
        · exact .inr ⟨e, h⟩
        · exact .inl e2.symm
      have hR : Red R := by
        intro m
        rcases split m with e | ⟨_, _, e2⟩ | ⟨e, h, _⟩
        · exact .inl (by simp only [R]; rw [e])
        · exact .inl e2.symm
        · exact .inr ⟨e, h⟩
      have hτ0 : PureS (τ 0) := hp (N + 0)
      rw [hLR 0] at hτ0
      apply eventually_none (ih hL hτ0.app_inv.1)
      rintro ⟨NL, hNL⟩
      apply eventually_none (ih hR hτ0.app_inv.2)
      rintro ⟨NR, hNR⟩
      apply hw (N + (NL + NR))
      rintro ⟨n, hn, hs⟩
      obtain ⟨m, rfl⟩ : ∃ m, n = N + m := ⟨n - N, by omega⟩
      have hs' : StepLe (D + 1) (τ m) (τ (m + 1)) := by
        simp only [τ]; rw [← Nat.add_assoc]; exact hs
      obtain ⟨e, he, hst⟩ := hs'
      have hst' := hst
      rw [hLR m, hLR (m + 1)] at hst'
      cases e with
      | zero => exact hnr m ⟨0, Nat.le_refl 0, hst⟩
      | succ e =>
        rcases wstepD_app_inv hst' with ⟨h, _⟩ | ⟨h, _⟩
        · exact hNL m (by omega) ⟨e, Nat.le_of_succ_le_succ he, h⟩
        · exact hNR m (by omega) ⟨e, Nat.le_of_succ_le_succ he, h⟩

end InfSN
