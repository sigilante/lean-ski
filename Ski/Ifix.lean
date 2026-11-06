import Ski.Requote

open Term

/-!
# Intensional fixed points and a quine

Kleene's second recursion theorem for `{S, K, I}`, as a corollary of
`Requote.requote`.  For every closed `g` there is a term `fixQ g` that
reduces to `g` applied to *its own encoding*: `fixQ g ↠ g ⟨fixQ g⟩`.  The
ordinary fixed point combinator gives `Y g ↠ g (Y g)`, handing `g` the live
term; here `g` receives the data `⟨fixQ g⟩`, which it can inspect.

`no_quote` says no program reaches `⟨M⟩` from a live `M`.  The construction
never does: it starts from data.  Let `h = λy. g (App y (R y))`, with `App`
the constructor `appC` and `R` the re-encoder.  Put `fixQ g = h ⟨h⟩`.  Then

    fixQ g ↠ g (App ⟨h⟩ (R ⟨h⟩)) ↠ g (App ⟨h⟩ ⟨⟨h⟩⟩) = g ⟨h ⟨h⟩⟩,

the middle step by `requote` and the last by `quoteT_app`, which is `rfl`.
The self-reference is diagonal: `h` is given its own encoding as an
argument, and `R` supplies the encoding of that argument.  Dropping `g`
from `h` gives a quine, `quineT ↠ ⟨quineT⟩`.

Contrast: whether pure `S` has any fixed point, combinatory or pointwise, is
open and conjectured not (question A6 in `OPEN-QUESTIONS.md`).  With `K` and
`I` alongside, the calculus has intensional ones.
This is theorem 4 of the B2 working note, `notes/B2-staging-modality.md`.
-/

namespace Ifix

open Requote

/-- The diagonal's body, over `y` (0): `g (App y (R y))`, `g` closed in. -/
def hBody (g : Term) : OTerm :=
  g.toO ⬝ₒ (appC.toO ⬝ₒ .var 0 ⬝ₒ (R.toO ⬝ₒ .var 0))

/-- `h_g = λy. g (App y (R y))`. -/
def hG (g : Term) : Term := toTerm (absN [0] (hBody g))

/-- **The intensional fixed point** of `g`: `h_g ⟨h_g⟩`. -/
def fixQ (g : Term) : Term := hG g ⬝ quoteT (hG g)

/-- `h_g` applied to any `y` takes one β. -/
theorem hG_beta (g y : Term) : WSteps (hG g ⬝ y) (g ⬝ (appC ⬝ y ⬝ (R ⬝ y))) := by
  have h := absN_beta_close [0] (hBody g) (fun _ => K) [y] rfl
  simp only [hBody, OTerm.close, close_toO] at h
  exact h

/-- **Intensional fixed points** (Kleene's second recursion theorem): for
    every closed `g`, `fixQ g ↠ g ⟨fixQ g⟩`. -/
theorem ifix (g : Term) : WSteps (fixQ g) (g ⬝ quoteT (fixQ g)) := by
  rw [fixQ, quoteT_app]
  exact (hG_beta g _).trans (WSteps.right g (WSteps.right _ (requote _)))

/-- Every closed `g` has an intensional fixed point. -/
theorem ifix_exists (g : Term) : ∃ t : Term, WSteps t (g ⬝ quoteT t) :=
  ⟨fixQ g, ifix g⟩

/-- The quine's body, over `y` (0): `App y (R y)`. -/
def qBody : OTerm := appC.toO ⬝ₒ .var 0 ⬝ₒ (R.toO ⬝ₒ .var 0)

/-- `h = λy. App y (R y)`. -/
def qH : Term := toTerm (absN [0] qBody)

/-- **The quine**, `h ⟨h⟩`. -/
def quineT : Term := qH ⬝ quoteT qH

/-- `quineT` reduces to its own encoding. -/
theorem quineT_spec : WSteps quineT (quoteT quineT) := by
  have h := absN_beta_close [0] qBody (fun _ => K) [quoteT qH] rfl
  simp only [qBody, OTerm.close, close_toO] at h
  rw [quineT, quoteT_app]
  exact h.trans (WSteps.right _ (requote _))

/-- **A quine exists**: some term reduces to its own encoding. -/
theorem quine : ∃ t : Term, WSteps t (quoteT t) := ⟨quineT, quineT_spec⟩

end Ifix
