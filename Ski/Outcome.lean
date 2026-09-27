import Ski.Realize
import Ski.Converse
import Ski.Stratum3
open Term

/-!
# The three-valued outcome for realizers

A realizer can converge, diverge, or fail.  Which formulas a diverging term
can realize depends on the formula's clause.

**Structured formulas demand a normal form** (`Real.and_converges`,
`Real.or_converges`, `Real.ex_converges`).  A realizer of `∧`, `∨` or `∃`
converges in normal order: its clause makes it weakly reduce, applied to
continuations, to a weak head normal form, and standardization
(`eval_back`) turns that into a normal-order evaluation of its head.

**An atom need not** (`atom_divergent_realizer`).  An atom's realizer is
checked only by its verifier, which may ignore the witness: `K (K K)`
accepts every witness, among them `Y I`, which diverges.
-/

theorem Real.and_converges {A B : Form} {r : Term} (h : Real (.and A B) r) : Converges r := by
  cases h with
  | intro a h => cases h with
    | intro b h =>
      cases eval_back (h.1 S) ⟨.refl _, .S2 a b⟩ with
      | intro v hv => exact Converges.app_left ⟨v, hv.1⟩

theorem Real.or_converges {A B : Form} {r : Term} (h : Real (.or A B) r) : Converges r := by
  cases h with
  | inl h =>
    cases h with
    | intro a h =>
      cases eval_back (h.1 K K) ⟨.refl _, .K1 a⟩ with
      | intro v hv => exact Converges.app_left (Converges.app_left ⟨v, hv.1⟩)
  | inr h =>
    cases h with
    | intro b h =>
      cases eval_back (h.1 K K) ⟨.refl _, .K1 b⟩ with
      | intro v hv => exact Converges.app_left (Converges.app_left ⟨v, hv.1⟩)

theorem Real.ex_converges {φ : Term → Form} {r : Term} (h : Real (.ex φ) r) : Converges r := by
  cases h with
  | intro w h => cases h with
    | intro b h =>
      cases eval_back (h.1 S) ⟨.refl _, .S2 w b⟩ with
      | intro v hv => exact Converges.app_left ⟨v, hv.1⟩

/-- **A diverging term can realize an atom**: the verifier `K (K K)` ignores
    its witness, so it accepts `Y I`, which diverges. -/
theorem atom_divergent_realizer (x : Term) :
    Real (.atom (K ⬝ (K ⬝ K)) x) (Ycomb ⬝ I) ∧ Diverges (Ycomb ⬝ I) :=
  ⟨(WSteps.single (WStep.left _ (.K (K ⬝ K) x))).trans (.single (.K K _)), Y_I_diverges⟩
