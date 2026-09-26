/-!
# SKI: terms and normal-order weak head reduction

The instruction set is three combinators and application.  Reduction is
normal order to weak head normal form: the redex is always at the head of
the spine, so `Step` has one congruence rule, `left`, and no others.

## Outcomes

A reduction produces a weak head normal form or diverges.  There is no
deterministic crash at this level: the calculus has no ill-formed terms.
Crashes enter one level up, as data (SKIlark's `RErr`, the object
language's `Err` leaf), which is why the three-valued jet contract of the
companion paper is stated over the language and not over the ISA.
Divergence is the absence of an `Eval` derivation (see `Ski.Fuel`).
-/

inductive Term
  | S | K | I
  | app : Term → Term → Term
  deriving Inhabited, DecidableEq, Repr

infixl:70 " ⬝ " => Term.app

open Term

/-- Weak head normal forms: a combinator short of its arguments. -/
inductive Whnf : Term → Prop
  | S : Whnf S
  | K : Whnf K
  | I : Whnf I
  | S1 (x : Term) : Whnf (S ⬝ x)
  | S2 (x y : Term) : Whnf (S ⬝ x ⬝ y)
  | K1 (x : Term) : Whnf (K ⬝ x)

/-- One contraction, at the head of the spine. -/
inductive Step : Term → Term → Prop
  | S (f g x : Term) : Step (S ⬝ f ⬝ g ⬝ x) (f ⬝ x ⬝ (g ⬝ x))
  | K (x y : Term) : Step (K ⬝ x ⬝ y) x
  | I (x : Term) : Step (I ⬝ x) x
  | left {f f' : Term} (x : Term) (h : Step f f') : Step (f ⬝ x) (f' ⬝ x)

theorem Whnf.no_step {t u : Term} (hw : Whnf t) (hs : Step t u) : False := by
  induction hs with
  | S f g x => cases hw
  | K x y => cases hw
  | I x => cases hw
  | left x h _ =>
    cases hw with
    | S1 _ => cases h
    | K1 _ => cases h
    | S2 _ _ => cases h with | left _ h' => cases h'

/-- Normal order is deterministic. -/
theorem Step.det {t u v : Term} (h₁ : Step t u) (h₂ : Step t v) : u = v := by
  induction h₁ generalizing v with
  | S f g x =>
    cases h₂ with
    | S => rfl
    | left _ h => exact (Whnf.no_step (Whnf.S2 f g) h).elim
  | K x y =>
    cases h₂ with
    | K => rfl
    | left _ h => exact (Whnf.no_step (Whnf.K1 x) h).elim
  | I x =>
    cases h₂ with
    | I => rfl
    | left _ h => exact (Whnf.no_step Whnf.I h).elim
  | left x h ih =>
    cases h₂ with
    | S => exact (Whnf.no_step (Whnf.S2 _ _) h).elim
    | K => exact (Whnf.no_step (Whnf.K1 _) h).elim
    | I => exact (Whnf.no_step Whnf.I h).elim
    | left _ h' => rw [ih h']

/-- Every term is a weak head normal form or has a contraction. -/
theorem progress (t : Term) : Whnf t ∨ ∃ u, Step t u := by
  induction t with
  | S => exact .inl .S
  | K => exact .inl .K
  | I => exact .inl .I
  | app f x ihf _ =>
    cases ihf with
    | inl hw =>
      cases hw with
      | S => exact .inl (.S1 x)
      | K => exact .inl (.K1 x)
      | I => exact .inr ⟨x, .I x⟩
      | S1 y => exact .inl (.S2 y x)
      | S2 y z => exact .inr ⟨_, .S y z x⟩
      | K1 y => exact .inr ⟨y, .K y x⟩
    | inr h =>
      cases h with
      | intro f' hs => exact .inr ⟨_, .left x hs⟩

/-- Zero or more contractions. -/
inductive Steps : Term → Term → Prop
  | refl (t : Term) : Steps t t
  | step {t t' u : Term} (h : Step t t') (hs : Steps t' u) : Steps t u

theorem Steps.single {t u : Term} (h : Step t u) : Steps t u := .step h (.refl u)

theorem Steps.trans {t u v : Term} (h₁ : Steps t u) (h₂ : Steps u v) : Steps t v := by
  induction h₁ with
  | refl _ => exact h₂
  | step h _ ih => exact .step h (ih h₂)

/-- Reduction at the head is preserved by application on the right. -/
theorem Steps.left {f f' : Term} (x : Term) (h : Steps f f') : Steps (f ⬝ x) (f' ⬝ x) := by
  induction h with
  | refl _ => exact .refl _
  | step h _ ih => exact .step (.left x h) ih

/-- `Eval t u`: `t` reduces to the weak head normal form `u`. -/
def Eval (t u : Term) : Prop := Steps t u ∧ Whnf u

theorem steps_whnf_det {t u v : Term} (hu : Steps t u) (wu : Whnf u)
    (hv : Steps t v) (wv : Whnf v) : u = v := by
  induction hu generalizing v with
  | refl t =>
    cases hv with
    | refl => rfl
    | step h _ => exact (wu.no_step h).elim
  | step h _ ih =>
    cases hv with
    | refl => exact (wv.no_step h).elim
    | step h' hs' =>
      apply ih wu _ wv
      rw [Step.det h h']
      exact hs'

theorem Eval.deterministic {t u v : Term} (h₁ : Eval t u) (h₂ : Eval t v) : u = v :=
  steps_whnf_det h₁.1 h₁.2 h₂.1 h₂.2

/-- Divergence is the absence of a derivation. -/
def Diverges (t : Term) : Prop := ∀ u, ¬ Eval t u
