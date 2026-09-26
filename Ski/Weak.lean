import Ski.Basic
open Term

/-!
# Weak reduction: standardization and confluence

`Step` contracts only at the head of the spine.  Bracket abstraction's
output reaches the terms it abstracts only up to contractions pending
inside arguments, so reasoning about compiled source (`PLAN.md` §3) needs
weak reduction, `WStep`: a contraction anywhere.  This module relates the
two.

**Standardization** (`standardization`).  If `t` weakly reduces to `u` and
`u` head-reduces to `w`, then `t` head-reduces to some `w'` that weakly
reduces to `w`: head reduction can be done first.  The proof is
Takahashi's, over parallel reduction `Par`: a parallel step splits into
head steps followed by an internal one, `ParI`, which contracts nothing on
the spine (`par_split`); an internal step commutes with a head step
(`parI_step`); and the two iterate (`par_steps`).

**Normalization transfers backward** (`eval_back`).  If `u` reaches a weak
head normal form and `t` weakly reduces to `u`, then `t` reaches one too,
weakly reducing to `u`'s.  So divergence transfers forward
(`diverges_of_wsteps`).

**Confluence** (`church_rosser`).  Weak reduction is Church–Rosser, by the
diamond property of `Par` through complete development `dev`
(`par_dev`).
-/

-- ---------------------------------------------------------------------------
-- Weak reduction
-- ---------------------------------------------------------------------------

/-- One contraction, anywhere in the term. -/
inductive WStep : Term → Term → Prop
  | S (f g x : Term) : WStep (S ⬝ f ⬝ g ⬝ x) (f ⬝ x ⬝ (g ⬝ x))
  | K (x y : Term) : WStep (K ⬝ x ⬝ y) x
  | I (x : Term) : WStep (I ⬝ x) x
  | left {f f' : Term} (x : Term) (h : WStep f f') : WStep (f ⬝ x) (f' ⬝ x)
  | right (f : Term) {x x' : Term} (h : WStep x x') : WStep (f ⬝ x) (f ⬝ x')

/-- Zero or more weak contractions. -/
inductive WSteps : Term → Term → Prop
  | refl (t : Term) : WSteps t t
  | step {t t' u : Term} (h : WStep t t') (hs : WSteps t' u) : WSteps t u

theorem WSteps.single {t u : Term} (h : WStep t u) : WSteps t u := .step h (.refl u)

theorem WSteps.trans {t u v : Term} (h₁ : WSteps t u) (h₂ : WSteps u v) : WSteps t v := by
  induction h₁ with
  | refl _ => exact h₂
  | step h _ ih => exact .step h (ih h₂)

theorem WSteps.left {f f' : Term} (x : Term) (h : WSteps f f') : WSteps (f ⬝ x) (f' ⬝ x) := by
  induction h with
  | refl _ => exact .refl _
  | step h _ ih => exact .step (.left x h) ih

theorem WSteps.right (f : Term) {x x' : Term} (h : WSteps x x') : WSteps (f ⬝ x) (f ⬝ x') := by
  induction h with
  | refl _ => exact .refl _
  | step h _ ih => exact .step (.right f h) ih

theorem WSteps.app {f f' x x' : Term} (hf : WSteps f f') (hx : WSteps x x') :
    WSteps (f ⬝ x) (f' ⬝ x') :=
  (WSteps.left x hf).trans (WSteps.right f' hx)

/-- A head step is a weak step. -/
theorem Step.weak {t u : Term} (h : Step t u) : WStep t u := by
  induction h with
  | S f g x => exact .S f g x
  | K x y => exact .K x y
  | I x => exact .I x
  | left x _ ih => exact .left x ih

theorem Steps.weak {t u : Term} (h : Steps t u) : WSteps t u := by
  induction h with
  | refl t => exact .refl t
  | step h _ ih => exact .step h.weak ih

-- ---------------------------------------------------------------------------
-- Parallel reduction
-- ---------------------------------------------------------------------------

/-- Contract any set of redexes at once, including redexes inside the
    fields of a contracted one. -/
inductive Par : Term → Term → Prop
  | S : Par S S
  | K : Par K K
  | I : Par I I
  | app {f f' x x' : Term} : Par f f' → Par x x' → Par (f ⬝ x) (f' ⬝ x')
  | K2 {x x' : Term} (y : Term) : Par x x' → Par (K ⬝ x ⬝ y) x'
  | I1 {x x' : Term} : Par x x' → Par (I ⬝ x) x'
  | S3 {f f' g g' x x' : Term} : Par f f' → Par g g' → Par x x' →
      Par (S ⬝ f ⬝ g ⬝ x) (f' ⬝ x' ⬝ (g' ⬝ x'))

theorem Par.refl : ∀ t : Term, Par t t
  | .S => .S
  | .K => .K
  | .I => .I
  | .app f x => .app (Par.refl f) (Par.refl x)

theorem WStep.par {t u : Term} (h : WStep t u) : Par t u := by
  induction h with
  | S f g x => exact .S3 (.refl f) (.refl g) (.refl x)
  | K x y => exact .K2 y (.refl x)
  | I x => exact .I1 (.refl x)
  | left x _ ih => exact .app ih (.refl x)
  | right f _ ih => exact .app (.refl f) ih

theorem Par.wsteps {t u : Term} (h : Par t u) : WSteps t u := by
  induction h with
  | S => exact .refl _
  | K => exact .refl _
  | I => exact .refl _
  | app _ _ ihf ihx => exact WSteps.app ihf ihx
  | K2 y _ ih => exact .step (.K _ y) ih
  | I1 _ ih => exact .step (.I _) ih
  | S3 _ _ _ ihf ihg ihx =>
    exact .step (.S _ _ _) (WSteps.app (WSteps.app ihf ihx) (WSteps.app ihg ihx))

/-- Parallel reduction that contracts nothing on the spine: the head
    combinator and the number of arguments are kept, and only the arguments
    reduce. -/
inductive ParI : Term → Term → Prop
  | S : ParI S S
  | K : ParI K K
  | I : ParI I I
  | app {f f' x x' : Term} : ParI f f' → Par x x' → ParI (f ⬝ x) (f' ⬝ x')

theorem ParI.par {t u : Term} (h : ParI t u) : Par t u := by
  induction h with
  | S => exact .S
  | K => exact .K
  | I => exact .I
  | app _ hx ih => exact .app ih hx

-- ---------------------------------------------------------------------------
-- Standardization
-- ---------------------------------------------------------------------------

/-- A parallel step is head steps followed by an internal parallel step. -/
theorem par_split {t u : Term} (h : Par t u) : ∃ t', Steps t t' ∧ ParI t' u := by
  induction h with
  | S => exact ⟨_, .refl _, .S⟩
  | K => exact ⟨_, .refl _, .K⟩
  | I => exact ⟨_, .refl _, .I⟩
  | @app f f' x x' _ hx ihf _ =>
    cases ihf with
    | intro f1 h1 => exact ⟨f1 ⬝ x, Steps.left x h1.1, .app h1.2 hx⟩
  | @K2 x x' y _ ih =>
    cases ih with
    | intro x1 h1 => exact ⟨x1, .step (.K x y) h1.1, h1.2⟩
  | @I1 x x' _ ih =>
    cases ih with
    | intro x1 h1 => exact ⟨x1, .step (.I x) h1.1, h1.2⟩
  | @S3 f f' g g' x x' _ hg hx ihf _ _ =>
    cases ihf with
    | intro f1 h1 =>
      exact ⟨f1 ⬝ x ⬝ (g ⬝ x), .step (.S f g x) (Steps.left (g ⬝ x) (Steps.left x h1.1)),
        .app (.app h1.2 hx) (.app hg hx)⟩

/-- An internal parallel step commutes with a head step. -/
theorem parI_step {u w : Term} (hs : Step u w) :
    ∀ {t : Term}, ParI t u → ∃ w', Step t w' ∧ Par w' w := by
  induction hs with
  | S f g x =>
    intro t hi
    cases hi with
    | app h1 hx =>
      cases h1 with
      | app h2 hg =>
        cases h2 with
        | app h3 hf =>
          cases h3
          exact ⟨_, .S _ _ _, .app (.app hf hx) (.app hg hx)⟩
  | K x y =>
    intro t hi
    cases hi with
    | app h1 _ =>
      cases h1 with
      | app h2 hx =>
        cases h2
        exact ⟨_, .K _ _, hx⟩
  | I x =>
    intro t hi
    cases hi with
    | app h1 hx =>
      cases h1
      exact ⟨_, .I _, hx⟩
  | left x _ ih =>
    intro t hi
    cases hi with
    | app hf hx =>
      cases ih hf with
      | intro w0 h0 => exact ⟨_, .left _ h0.1, .app h0.2 hx⟩

/-- A parallel step, then a head step: head steps first, then a parallel step. -/
theorem par_step {t u w : Term} (hp : Par t u) (hs : Step u w) :
    ∃ w', Steps t w' ∧ Par w' w := by
  cases par_split hp with
  | intro t1 h1 =>
    cases parI_step hs h1.2 with
    | intro w0 h0 => exact ⟨w0, h1.1.trans (.single h0.1), h0.2⟩

theorem par_steps {u w : Term} (hs : Steps u w) :
    ∀ {t : Term}, Par t u → ∃ w', Steps t w' ∧ Par w' w := by
  induction hs with
  | refl _ => exact fun hp => ⟨_, .refl _, hp⟩
  | step h _ ih =>
    intro t hp
    cases par_step hp h with
    | intro a ha =>
      cases ih ha.2 with
      | intro w' hw => exact ⟨w', ha.1.trans hw.1, hw.2⟩

/-- **Standardization.**  Head reduction can be done first: if `t` weakly
    reduces to `u` and `u` head-reduces to `w`, then `t` head-reduces to a
    term that weakly reduces to `w`. -/
theorem standardization {t u w : Term} (htu : WSteps t u) (huw : Steps u w) :
    ∃ w', Steps t w' ∧ WSteps w' w := by
  induction htu with
  | refl _ => exact ⟨w, huw, .refl w⟩
  | step h _ ih =>
    cases ih huw with
    | intro w1 h1 =>
      cases par_steps h1.1 h.par with
      | intro w' hw => exact ⟨w', hw.1, hw.2.wsteps.trans h1.2⟩

-- ---------------------------------------------------------------------------
-- Normalization transfers backward
-- ---------------------------------------------------------------------------

/-- Zero or more internal parallel steps. -/
inductive ParIs : Term → Term → Prop
  | refl (t : Term) : ParIs t t
  | step {t t' u : Term} (h : ParI t t') (hs : ParIs t' u) : ParIs t u

theorem ParIs.wsteps {t u : Term} (h : ParIs t u) : WSteps t u := by
  induction h with
  | refl t => exact .refl t
  | step h _ ih => exact h.par.wsteps.trans ih

/-- Any weak reduction is head steps followed by internal parallel steps. -/
theorem wsteps_split {t v : Term} (h : WSteps t v) : ∃ t', Steps t t' ∧ ParIs t' v := by
  induction h with
  | refl t => exact ⟨t, .refl t, .refl t⟩
  | step s _ ih =>
    cases ih with
    | intro t1 h1 =>
      cases par_steps h1.1 s.par with
      | intro w hw =>
        cases par_split hw.2 with
        | intro w0 h0 => exact ⟨w0, hw.1.trans h0.1, .step h0.2 h1.2⟩

/-- An internal step keeps the spine, so it reflects weak head normal forms. -/
theorem ParI.whnf {t u : Term} (h : ParI t u) (hw : Whnf u) : Whnf t := by
  cases hw with
  | S => cases h; exact .S
  | K => cases h; exact .K
  | I => cases h; exact .I
  | S1 x =>
    cases h with
    | app h1 _ => cases h1; exact .S1 _
  | S2 x y =>
    cases h with
    | app h1 _ =>
      cases h1 with
      | app h2 _ => cases h2; exact .S2 _ _
  | K1 x =>
    cases h with
    | app h1 _ => cases h1; exact .K1 _

theorem ParIs.whnf {t u : Term} (h : ParIs t u) (hw : Whnf u) : Whnf t := by
  induction h with
  | refl _ => exact hw
  | step h _ ih => exact h.whnf (ih hw)

/-- **Normalization transfers backward.**  If `t` weakly reduces to `u` and
    `u` reaches a weak head normal form, so does `t`, and `t`'s weakly
    reduces to `u`'s. -/
theorem eval_back {t u v : Term} (htu : WSteps t u) (hv : Eval u v) :
    ∃ v', Eval t v' ∧ WSteps v' v := by
  cases wsteps_split (htu.trans hv.1.weak) with
  | intro t' h => exact ⟨t', ⟨h.1, h.2.whnf hv.2⟩, h.2.wsteps⟩

/-- Divergence transfers forward along weak reduction. -/
theorem diverges_of_wsteps {t u : Term} (htu : WSteps t u) (hd : Diverges t) : Diverges u :=
  fun _ hv => match eval_back htu hv with
    | ⟨v', he, _⟩ => hd v' he

-- ---------------------------------------------------------------------------
-- Confluence
-- ---------------------------------------------------------------------------

/-- Complete development: contract every redex of the term at once. -/
def dev : Term → Term
  | app (app K x) _ => dev x
  | app I x => dev x
  | app (app (app S f) g) x => app (app (dev f) (dev x)) (app (dev g) (dev x))
  | app f x => app (dev f) (dev x)
  | t => t

/-- Every parallel step from `t` can be completed to `dev t`. -/
theorem par_dev {t u : Term} (h : Par t u) : Par u (dev t) := by
  induction h with
  | S => exact .S
  | K => exact .K
  | I => exact .I
  | K2 y _ ih => exact ih
  | I1 _ ih => exact ih
  | S3 _ _ _ ihf ihg ihx => exact .app (.app ihf ihx) (.app ihg ihx)
  | @app f f' x x' hf hx ihf ihx =>
    cases f with
    | S => exact .app ihf ihx
    | K => exact .app ihf ihx
    | I =>
      cases hf
      exact .I1 ihx
    | app f1 f2 =>
      cases f1 with
      | S => exact .app ihf ihx
      | I => exact .app ihf ihx
      | K =>
        cases hf with
        | app hK hx2 =>
          cases hK
          cases ihf with
          | app _ hd => exact .K2 _ hd
      | app a f0 =>
        cases a with
        | K => exact .app ihf ihx
        | I => exact .app ihf ihx
        | app b c => exact .app ihf ihx
        | S =>
          cases hf with
          | app h1 hg =>
            cases h1 with
            | app hS hf0 =>
              cases hS
              cases ihf with
              | app h3 hgd =>
                cases h3 with
                | app _ hfd => exact .S3 hfd hgd ihx

/-- Zero or more parallel steps. -/
inductive Pars : Term → Term → Prop
  | refl (t : Term) : Pars t t
  | step {t t' u : Term} (h : Par t t') (hs : Pars t' u) : Pars t u

theorem Pars.trans {t u v : Term} (h₁ : Pars t u) (h₂ : Pars u v) : Pars t v := by
  induction h₁ with
  | refl _ => exact h₂
  | step h _ ih => exact .step h (ih h₂)

theorem WSteps.pars {t u : Term} (h : WSteps t u) : Pars t u := by
  induction h with
  | refl t => exact .refl t
  | step h _ ih => exact .step h.par ih

theorem Pars.wsteps {t u : Term} (h : Pars t u) : WSteps t u := by
  induction h with
  | refl t => exact .refl t
  | step h _ ih => exact h.wsteps.trans ih

/-- One parallel step against many: they close in one more parallel step. -/
theorem par_strip {t v : Term} (hv : Pars t v) :
    ∀ {u : Term}, Par t u → ∃ w, Pars u w ∧ Par v w := by
  induction hv with
  | refl t => exact fun hu => ⟨_, .refl _, hu⟩
  | step h _ ih =>
    intro u hu
    cases ih (par_dev h) with
    | intro w hw => exact ⟨w, .step (par_dev hu) hw.1, hw.2⟩

theorem pars_confluent {t u : Term} (hu : Pars t u) :
    ∀ {v : Term}, Pars t v → ∃ w, Pars u w ∧ Pars v w := by
  induction hu with
  | refl t => exact fun hv => ⟨_, hv, .refl _⟩
  | step h _ ih =>
    intro v hv
    cases par_strip hv h with
    | intro w1 h1 =>
      cases ih h1.1 with
      | intro w hw => exact ⟨w, hw.1, .step h1.2 hw.2⟩

/-- **Church–Rosser.**  Weak reduction is confluent. -/
theorem church_rosser {t u v : Term} (hu : WSteps t u) (hv : WSteps t v) :
    ∃ w, WSteps u w ∧ WSteps v w := by
  cases pars_confluent hu.pars hv.pars with
  | intro w hw => exact ⟨w, hw.1.wsteps, hw.2.wsteps⟩
