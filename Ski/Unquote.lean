import Ski.Requote

open Term

/-!
# The unquoter, and the comonad laws up to conversion

`Requote.R` is the comonad's comultiplication `δ : □A → □□A`.  This module
gives its counit `ε : □A → A`, the unquoter, as one closed term `E` with
`E ⟨t⟩ ↠ t` for every `t`: the fixpoint of `λ e q. q S K I (λ f a. e f (e a))`,
which reads an encoding back into the term it encodes.  The proof is induction
on `t`, as for `requote`.

Of the comonad's counit laws, `ε ∘ δ = id` holds outright (`counit_delta`):
`E (R ⟨t⟩) ↠ ⟨t⟩`.  The other, `□ε ∘ δ = id`, holds only up to conversion
under the box (`box_counit_delta`): `□ε (δ ⟨t⟩)` reduces to the code of
`E ⟨t⟩`, a term that reduces to `t`, not to the code `⟨t⟩` itself.  This is
the same gap as the second coalgebra law's (`Coalgebra.coalg2`).
-/

namespace Unquote

open Requote

/-- The application case's body, over `e` (0), `f` (2) and `a` (3):
    `e f (e a)`. -/
def appBody : OTerm := (.var 0 ⬝ₒ .var 2) ⬝ₒ (.var 0 ⬝ₒ .var 3)

/-- The step function's body, over `e` (0) and `q` (1). -/
def stepBody : OTerm :=
  .var 1 ⬝ₒ Term.S.toO ⬝ₒ Term.K.toO ⬝ₒ Term.I.toO ⬝ₒ absN [2, 3] appBody

/-- `λ e q. q S K I (λ f a. e f (e a))`. -/
def stepF : Term := toTerm (absN [0, 1] stepBody)

/-- **The unquoter** `ε`, the fixpoint of `stepF`. -/
def E : Term := fixSelf stepF (fixB stepF)

/-- `E` unrolls once. -/
theorem E_unroll : WSteps E (stepF ⬝ E) := by
  have h := (fixSelf_unroll (F := stepF) (Steps.refl (fixB stepF))).weak
  have hI : WSteps (fixSelf stepF (I ⬝ fixB stepF)) E :=
    WSteps.right _ (.single (.I _))
  exact h.trans (WSteps.right _ hI)

/-- One unrolling and the step function's β: `E q` cases on `q`. -/
theorem E_case (q : Term) :
    WSteps (E ⬝ q) (q ⬝ Term.S ⬝ Term.K ⬝ Term.I
      ⬝ (absN [2, 3] appBody).close (overrideC (fun _ => K) [0, 1] [E, q])) := by
  have h := absN_beta_close [0, 1] stepBody (fun _ => K) [E, q] rfl
  simp only [stepBody, OTerm.close, close_toO] at h
  exact (WSteps.left q E_unroll).trans h

/-- The application case's function, applied to two encodings. -/
theorem appCase (q f x : Term) :
    WSteps ((absN [2, 3] appBody).close (overrideC (fun _ => K) [0, 1] [E, q]) ⬝ f ⬝ x)
      ((E ⬝ f) ⬝ (E ⬝ x)) := by
  have h := absN_beta_close [2, 3] appBody (overrideC (fun _ => K) [0, 1] [E, q]) [f, x] rfl
  simp only [appBody, OTerm.close] at h
  exact h

/-- **Unquoting is definable**: `E ⟨t⟩ ↠ t` for every term `t`. -/
theorem unquote : ∀ t : Term, WSteps (E ⬝ quoteT t) t
  | .S => (E_case _).trans (quoteS_elim _ _ _ _)
  | .K => (E_case _).trans (quoteK_elim _ _ _ _)
  | .I => (E_case _).trans (quoteI_elim _ _ _ _)
  | .app f x => by
    have h1 := (E_case (quoteT (f ⬝ x))).trans (quoteApp_elim f x _ _ _ _)
    exact (h1.trans (appCase _ _ _)).trans (WSteps.app (unquote f) (unquote x))

/-- **The counit law `ε ∘ δ = id`**, outright: `E (R ⟨t⟩) ↠ ⟨t⟩`. -/
theorem counit_delta (t : Term) : WSteps (E ⬝ (R ⬝ quoteT t)) (quoteT t) :=
  (WSteps.right E (requote t)).trans (unquote (quoteT t))

/-- **The counit law `□ε ∘ δ = id`, up to conversion under the box.**  With
    `□ε` acting on a code `u` as `App ⟨E⟩ u`, `□ε (R ⟨t⟩)` reduces to the code
    of `E ⟨t⟩`, and `E ⟨t⟩ ↠ t`. -/
theorem box_counit_delta (t : Term) :
    WSteps (appC ⬝ quoteT E ⬝ (R ⬝ quoteT t)) (quoteT (E ⬝ quoteT t)) ∧
      WSteps (E ⬝ quoteT t) t :=
  ⟨WSteps.right _ (requote t), unquote t⟩

end Unquote
