import Ski.Witness
import Ski.Compile

open Term

/-!
# Two atoms, each with a hidden realizer

Examples for `Ski/Witness.lean`: NP atoms `atom V x` whose realizers are
terms, not Boolean inputs.  Booleans are Scott's: `T = K`, `F = K I`, so
`and a b = a b F`, `or a b = a T b`, `not a = a F T`.  Realizing an atom
means `V ⬝ x ⬝ w` evaluates to `K`, which is `T`, and nothing more: **an
atom certifies exactly its verifier's evaluation.**

- **A test of a hidden function** (`negV`): `w` passes the two tests a
  negation of Scott Booleans passes, `(w T) F T (w F) F` evaluating to
  `K`.  The negation `negW = [b] b F T` realizes it (`neg_real`); the
  identity does not (`neg_not_I`).  So does a term that is no negation:
  `K (K (K (K (K K))))` (`neg_fake`), since a verifier applies its witness
  to finitely many arguments and a term can fake any finite behaviour.
- **A test of a hidden triple** (`satV`): `w ([a b c] φ)` evaluates to `K`,
  for `φ = (a ∨ b) ∧ (¬a ∨ c) ∧ ¬c`.  The triple `F T F`, a satisfying
  assignment, realizes it (`sat_real`); the triple `T T T` does not
  (`sat_not_TTT`).  So does `K K`, which is no triple (`sat_fake`).  An
  assignment proved as data must come in as cells the circuit fixes to
  Booleans, as the Sudoku proof's inputs do; a hidden term fits a claim
  about the term itself.

Both verifiers ignore `x`, the public input, which is `I`.
-/

namespace WitEx

/-- Scott Booleans, as open terms. -/
def T : OTerm := .K
def F : OTerm := .K ⬝ₒ .I
def and' (a b : OTerm) : OTerm := a ⬝ₒ b ⬝ₒ F
def or' (a b : OTerm) : OTerm := a ⬝ₒ T ⬝ₒ b
def not' (a : OTerm) : OTerm := a ⬝ₒ F ⬝ₒ T

/-- The public input both examples take, and ignore. -/
def x0 : Term := I

-- ---------------------------------------------------------------------------
-- A hidden function
-- ---------------------------------------------------------------------------

/-- `[x w] and (not (w T)) (w F)`: the tests a negation passes. -/
def negV : Term := toTerm (absN [0, 1] (and' (not' (.var 1 ⬝ₒ T)) (.var 1 ⬝ₒ F)))

/-- `[b] b F T`, a negation. -/
def negW : Term := toTerm (absN [0] (not' (.var 0)))

theorem neg_real : Real (.atom negV x0) negW :=
  real_atom_iff.2 (evalF_sound (k := 64) (by decide))

/-- The identity is no negation: the verifier ends at `F`. -/
theorem neg_not_I : ¬ Real (.atom negV x0) I := by
  intro h
  have e1 := real_atom_iff.1 h
  have e2 : Eval (negV ⬝ x0 ⬝ I) (K ⬝ I) := evalF_sound (k := 64) (by decide)
  cases Eval.deterministic e1 e2

/-- A term that is no negation passes the tests: it ignores its argument and
    consumes the verifier's. -/
theorem neg_fake : Real (.atom negV x0) (K ⬝ (K ⬝ (K ⬝ (K ⬝ (K ⬝ K))))) :=
  real_atom_iff.2 (evalF_sound (k := 64) (by decide))

-- ---------------------------------------------------------------------------
-- A hidden triple
-- ---------------------------------------------------------------------------

/-- The formula `(a ∨ b) ∧ (¬a ∨ c) ∧ ¬c` over the variables 2, 3, 4. -/
def satBody : OTerm :=
  and' (or' (.var 2) (.var 3)) (and' (or' (not' (.var 2)) (.var 4)) (not' (.var 4)))

/-- `[x w] w ([a b c] φ)`: `w`, applied to `φ` as a function of three
    Booleans, gives `T`. -/
def satV : Term := toTerm (absN [0, 1] (.var 1 ⬝ₒ absN [2, 3, 4] satBody))

/-- A Scott triple `[f] f a b c`. -/
def triple (a b c : OTerm) : Term := toTerm (absN [0] (.var 0 ⬝ₒ a ⬝ₒ b ⬝ₒ c))

/-- The satisfying assignment `a = F, b = T, c = F`. -/
def satW : Term := triple F T F

theorem sat_real : Real (.atom satV x0) satW :=
  real_atom_iff.2 (evalF_sound (k := 128) (by decide))

/-- `T T T` fails `¬c`: the verifier ends at `F`. -/
theorem sat_not_TTT : ¬ Real (.atom satV x0) (triple T T T) := by
  intro h
  have e1 := real_atom_iff.1 h
  have e2 : Eval (satV ⬝ x0 ⬝ triple T T T) (K ⬝ I) := evalF_sound (k := 128) (by decide)
  cases Eval.deterministic e1 e2

/-- `K K` is no triple, and realizes the atom: it ignores `φ`. -/
theorem sat_fake : Real (.atom satV x0) (K ⬝ K) :=
  real_atom_iff.2 (evalF_sound (k := 128) (by decide))

end WitEx
