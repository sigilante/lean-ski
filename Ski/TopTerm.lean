import Ski.HnfQ5
open Term

/-!
# Top-termination of pure S: definitions and the reduction to head reduction

A *root step* contracts the redex `S f g x` at the root of the term.  A reduction is
*perpetual* if it makes root steps at unboundedly late positions; Waldmann (thesis, 1998,
ch. 7) proved that no reduction of closed S-terms is perpetual (*top-termination*).

This module reduces the question to head reduction:

* `RSteps k t u`: a weak reduction from `t` to `u` with at least `k` root steps;
* `HRun k t u`: a head reduction from `t` to `u` with at least `k` root steps;
* `bridge`: `RSteps k t u → ∃ v, HRun k t v` (standardization, `Ski/Weak.lean`, up to each
  root redex: internal steps keep the spine, so the head path meets that redex's shape);
* `perpetual_rsteps`: a perpetual reduction from `t` gives `RSteps k t _` for every `k`.

Top-termination then follows from: the head path of a closed S-term has boundedly many root
steps, i.e. `¬ ∀ k, ∃ v, HRun k t v`.
-/

namespace TopTerm

/-- A weak reduction with at least `k` root steps. -/
inductive RSteps : Nat → Term → Term → Prop
  | refl (t : Term) : RSteps 0 t t
  | weak {k : Nat} {t t' u : Term} (h : WStep t t') (hs : RSteps k t' u) : RSteps k t u
  | root {k : Nat} {f g x u : Term} (hs : RSteps k (f ⬝ x ⬝ (g ⬝ x)) u) :
      RSteps (k + 1) (S ⬝ f ⬝ g ⬝ x) u

/-- A head reduction with at least `k` root steps. -/
inductive HRun : Nat → Term → Term → Prop
  | refl (t : Term) : HRun 0 t t
  | head {k : Nat} {t t' u : Term} (h : Step t t') (hs : HRun k t' u) : HRun k t u
  | root {k : Nat} {f g x u : Term} (hs : HRun k (f ⬝ x ⬝ (g ⬝ x)) u) :
      HRun (k + 1) (S ⬝ f ⬝ g ⬝ x) u

theorem RSteps.of_wsteps {k : Nat} {t t' u : Term} (h : WSteps t t') (hs : RSteps k t' u) :
    RSteps k t u := by
  induction h with
  | refl => exact hs
  | step s _ ih => exact .weak s (ih hs)

theorem HRun.of_steps {k : Nat} {t t' u : Term} (h : Steps t t') (hs : HRun k t' u) :
    HRun k t u := by
  induction h with
  | refl => exact hs
  | step s _ ih => exact .head s (ih hs)

/-- Split off the first root step. -/
theorem RSteps.first : ∀ {k : Nat} {t u : Term}, RSteps (k + 1) t u →
    ∃ f g x, WSteps t (S ⬝ f ⬝ g ⬝ x) ∧ RSteps k (f ⬝ x ⬝ (g ⬝ x)) u := by
  intro k t u h
  generalize hk : k + 1 = m at h
  induction h generalizing k with
  | refl => cases hk
  | weak s _ ih =>
    obtain ⟨f, g, x, hw, hr⟩ := ih hk
    exact ⟨f, g, x, .step s hw, hr⟩
  | @root k' f g x u hs _ =>
    have : k' = k := by injection hk with h; exact h.symm
    subst this
    exact ⟨f, g, x, .refl _, hs⟩

/-- Internal steps keep a spine `S f g x`. -/
theorem parI_S3 : ∀ {t f g x : Term}, ParI t (S ⬝ f ⬝ g ⬝ x) →
    ∃ f' g' x', t = S ⬝ f' ⬝ g' ⬝ x' ∧ WSteps f' f ∧ WSteps g' g ∧ WSteps x' x := by
  intro t f g x h
  cases h with
  | app h₁ hx =>
    cases h₁ with
    | app h₂ hg =>
      cases h₂ with
      | app h₃ hf =>
        cases h₃
        exact ⟨_, _, _, rfl, hf.wsteps, hg.wsteps, hx.wsteps⟩

theorem parIs_S3 : ∀ {t f g x : Term}, ParIs t (S ⬝ f ⬝ g ⬝ x) →
    ∃ f' g' x', t = S ⬝ f' ⬝ g' ⬝ x' ∧ WSteps f' f ∧ WSteps g' g ∧ WSteps x' x := by
  intro t f g x h
  generalize hv : S ⬝ f ⬝ g ⬝ x = v at h
  induction h generalizing f g x with
  | refl => subst hv; exact ⟨f, g, x, rfl, .refl _, .refl _, .refl _⟩
  | step h₁ _ ih =>
    obtain ⟨f₁, g₁, x₁, rfl, hf, hg, hx⟩ := ih hv
    obtain ⟨f', g', x', rfl, hf', hg', hx'⟩ := parI_S3 h₁
    exact ⟨f', g', x', rfl, hf'.trans hf, hg'.trans hg, hx'.trans hx⟩

/-- **Bridge.**  A weak reduction with `k` root steps gives a head reduction from the same
term with at least `k` root steps. -/
theorem bridge : ∀ (k : Nat) {t u : Term}, RSteps k t u → ∃ v, HRun k t v := by
  intro k
  induction k with
  | zero => intro t _ _; exact ⟨t, .refl t⟩
  | succ k ih =>
    intro t u h
    obtain ⟨f, g, x, hw, hr⟩ := RSteps.first h
    obtain ⟨t₁, hs, hp⟩ := wsteps_split hw
    obtain ⟨f', g', x', rfl, hf, hg, hx⟩ := parIs_S3 hp
    have hr' : RSteps k (f' ⬝ x' ⬝ (g' ⬝ x')) u :=
      RSteps.of_wsteps (WSteps.app (WSteps.app hf hx) (WSteps.app hg hx)) hr
    obtain ⟨v, hv⟩ := ih hr'
    exact ⟨v, HRun.of_steps hs (.root hv)⟩

/-- A root step. -/
def IsRoot (t u : Term) : Prop := ∃ f g x, t = S ⬝ f ⬝ g ⬝ x ∧ u = f ⬝ x ⬝ (g ⬝ x)

/-- A reduction sequence is perpetual if it makes root steps at unboundedly late positions. -/
def Perpetual (σ : Nat → Term) : Prop :=
  (∀ n, WStep (σ n) (σ (n + 1))) ∧ ∀ N, ∃ n, N ≤ n ∧ IsRoot (σ n) (σ (n + 1))

/-- From position `m`, a perpetual reduction has a reduction with `k` root steps. -/
theorem perpetual_from {σ : Nat → Term} (hp : Perpetual σ) :
    ∀ (k m : Nat), ∃ u, RSteps k (σ m) u := by
  intro k
  induction k with
  | zero => intro m; exact ⟨σ m, .refl _⟩
  | succ k ih =>
    intro m
    obtain ⟨n, hmn, f, g, x, h1, h2⟩ := hp.2 m
    obtain ⟨u, hu⟩ := ih (n + 1)
    -- σ m ↠ σ n by the steps in between
    have hw : ∀ d, WSteps (σ m) (σ (m + d)) := by
      intro d
      induction d with
      | zero => exact .refl _
      | succ d ihd =>
        exact ihd.trans (.single (by rw [← Nat.add_assoc]; exact hp.1 (m + d)))
    have hmn' : σ n = σ (m + (n - m)) := by rw [Nat.add_sub_cancel' hmn]
    refine ⟨u, RSteps.of_wsteps (hmn' ▸ hw (n - m)) ?_⟩
    rw [h1]; rw [h2] at hu
    exact .root hu

theorem perpetual_rsteps {σ : Nat → Term} (hp : Perpetual σ) : ∀ k, ∃ u, RSteps k (σ 0) u :=
  fun k => perpetual_from hp k 0

/-- **Reduction to head reduction.**  If the head path of `t` has boundedly many root steps,
no reduction from `t` is perpetual. -/
theorem not_perpetual {σ : Nat → Term} (hb : ¬ ∀ k, ∃ v, HRun k (σ 0) v) : ¬ Perpetual σ :=
  fun hp => hb fun k => by
    obtain ⟨u, hu⟩ := perpetual_rsteps hp k
    exact bridge k hu

end TopTerm
