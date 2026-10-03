import Ski.ComposeX
import Ski.WitnessExamples

open Term

/-!
# Composed statements with `∃` and knowledge implication: examples

- **A hidden value two atoms share** (`exEq`): `∃ y. y = w₁ ∧ y = ¬w₂`,
  over Scott Booleans.  Each atom's verifier reads `y` from its input
  `⟨x, y⟩`; the witness holds `y` once, at the `∃` node.  Accepted with
  `y = T`, `w₁ = T`, `w₂ = F` (`exEq_accepts`), read back as a realizer
  (`exEq_real`); refused when `w₂` disagrees (`exEq_refuses`).
- **Knowledge implication through a certified map**: `fst` concludes the
  first atom from a proof of the conjunction of the two atoms of
  `Ski/WitnessExamples.lean` (`fstAnd_real`); `inl` concludes the
  disjunction from a proof of its first side (`inlNeg_real`).  The
  certificates come from the library (`XS.cert`), not from the statement.
-/

namespace ComposeXEx

open Compose WitEx

/-- `[i w] (i (K I)) w (¬w)`: the bound value equals the witness, as
    Booleans. -/
def eqV : Term := toTerm (absN [0, 1] (.var 0 ⬝ₒ F ⬝ₒ .var 1 ⬝ₒ not' (.var 1)))

/-- `[i w] (i (K I)) (¬w) w`: the bound value is the witness's negation. -/
def neqV : Term := toTerm (absN [0, 1] (.var 0 ⬝ₒ F ⬝ₒ not' (.var 1) ⬝ₒ .var 1))

/-- `∃ y. y = w₁ ∧ y = ¬w₂`. -/
def exEq : XS := .ex (.and (.atom eqV x0) (.atom neqV x0))

def exEqBits : BT := .node (.leaf false) (.node (.leaf true) (.leaf true))

/-- `⟨y, ⟨w₁, w₂⟩⟩` with `y = T`, `w₁ = T`, `w₂ = F`. -/
def exEqW : Term := pairT K (pairT K (K ⬝ I))

theorem exEq_accepts : AcceptsX exEq.toXF exEqBits exEqW := by
  refine ⟨(⟨trivial, trivial⟩ : ShapeX (.and (.atom eqV x0) (.atom neqV x0)) (.node (.leaf true) (.leaf true))),
    fun P hP => ?_⟩
  simp [evalStmtOfX, stmtOfX, leavesX, exEq, XS.toXF] at hP
  rcases hP with rfl | rfl | rfl
  · exact evalF_sound (k := 128) (by decide)
  · exact evalF_sound (k := 128) (by decide)
  · exact evalF_sound (k := 128) (by decide)

theorem exEq_real : Real (exEq.toXF.form []) (readBackX exEq.toXF exEqBits exEqW []) :=
  real_of_acceptedXS exEq_accepts rfl

/-- `w₂ = T` disagrees: the second guard ends at `F`. -/
theorem exEq_refuses : ¬ AcceptsX exEq.toXF exEqBits (pairT K (pairT K K)) := by
  intro h
  have hg := h.2 (leafStmtX neqV x0 [[false]] [true, true])
    (by simp [evalStmtOfX, stmtOfX, leavesX, exEq, XS.toXF])
  have e2 : Eval (leafStmtX neqV x0 [[false]] [true, true] ⬝ exEqBits.enc ⬝ pairT K (pairT K K)) (K ⬝ I) :=
    evalF_sound (k := 128) (by decide)
  cases Eval.deterministic hg e2

/-- `fst (neg ∧ sat)`: the first atom, from a proof of the conjunction. -/
def fstAnd : XS := .fst (.and (.atom negV x0) (.atom satV x0))

def fstAndBits : BT := .node (.leaf true) (.leaf true)

theorem fstAnd_accepts : AcceptsX fstAnd.toXF fstAndBits (pairT negW satW) := by
  refine ⟨⟨trivial, trivial⟩, fun P hP => ?_⟩
  simp [evalStmtOfX, stmtOfX, leavesX, fstAnd, XS.toXF] at hP
  rcases hP with rfl | rfl | rfl
  · exact evalF_sound (k := 128) (by decide)
  · exact evalF_sound (k := 128) (by decide)
  · exact evalF_sound (k := 128) (by decide)

/-- The conclusion is the atom alone. -/
theorem fstAnd_form : fstAnd.toXF.form [] = .atom negV x0 := rfl

theorem fstAnd_real : Real (.atom negV x0) (readBackX fstAnd.toXF fstAndBits (pairT negW satW) []) :=
  real_of_acceptedXS fstAnd_accepts rfl

/-- `inl neg sat`: the disjunction, from a proof of its first side. -/
def inlNeg : XS := .inl (.atom negV x0) (.atom satV x0)

theorem inlNeg_accepts : AcceptsX inlNeg.toXF (.leaf true) negW := by
  refine ⟨trivial, fun P hP => ?_⟩
  simp [evalStmtOfX, stmtOfX, leavesX, inlNeg, XS.toXF] at hP
  rcases hP with rfl | rfl
  · exact evalF_sound (k := 128) (by decide)
  · exact evalF_sound (k := 128) (by decide)

theorem inlNeg_form : inlNeg.toXF.form [] = .or (.atom negV x0) (.atom satV x0) := rfl

theorem inlNeg_real :
    Real (.or (.atom negV x0) (.atom satV x0)) (readBackX inlNeg.toXF (.leaf true) negW []) :=
  real_of_acceptedXS inlNeg_accepts rfl

end ComposeXEx
