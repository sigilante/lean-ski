import Ski.Chain
import Ski.WitnessExamples

open Term

/-!
# A chain of two composed statements over a public hand-off

Two stages, two provers, one public value `o`, here the Boolean `F`:

- stage 1 (`stage₁ o`): "I know a satisfying assignment of
  `(a ∨ b) ∧ (¬a ∨ c) ∧ ¬c` whose first variable is `o`";
- stage 2 (`stage₂ o`): "I know a negation that takes `o` to `T`".

Each is a composed statement of its own, accepted with its own witness
(`stage₁_accepts`, `stage₂_accepts`); together they prove the
conjunction, its realizer the pair of the two read-backs (`chain_real`).
Neither prover sees the other's witness.
-/

namespace ChainEx

open Compose Chain WitEx

/-- `a == b` on Booleans. -/
def eqB (a b : OTerm) : OTerm := a ⬝ₒ b ⬝ₒ not' b

/-- `[x w] w ⊨ φ ∧ (first of w) == x`. -/
def satFirstV : Term :=
  toTerm (absN [0, 1] (and' (.var 1 ⬝ₒ absN [2, 3, 4] satBody) (eqB (.var 1 ⬝ₒ absN [2, 3, 4] (.var 2)) (.var 0))))

/-- `[x w] w negates ∧ w x == T`. -/
def negToTV : Term :=
  toTerm (absN [0, 1] (and' (and' (not' (.var 1 ⬝ₒ T)) (.var 1 ⬝ₒ F)) (.var 1 ⬝ₒ .var 0)))

def stage₁ (o : Term) : XS := .atom satFirstV o
def stage₂ (o : Term) : XS := .atom negToTV o

/-- The hand-off: the Boolean `F`. -/
def o : Term := K ⬝ I

theorem stage₁_accepts : AcceptsX (stage₁ o).toXF (.leaf true) satW := by
  refine ⟨trivial, fun P hP => ?_⟩
  simp [evalStmtOfX, stmtOfX, leavesX, stage₁, XS.toXF] at hP
  rcases hP with rfl | rfl
  · exact evalF_sound (k := 128) (by decide)
  · exact evalF_sound (k := 256) (by decide)

theorem stage₂_accepts : AcceptsX (stage₂ o).toXF (.leaf true) negW := by
  refine ⟨trivial, fun P hP => ?_⟩
  simp [evalStmtOfX, stmtOfX, leavesX, stage₂, XS.toXF] at hP
  rcases hP with rfl | rfl
  · exact evalF_sound (k := 128) (by decide)
  · exact evalF_sound (k := 256) (by decide)

/-- **The chain proves the conjunction.** -/
theorem chain_real :
    Real (.and (.atom satFirstV o) (.atom negToTV o))
      (pairT (readBackX (stage₁ o).toXF (.leaf true) satW []) (readBackX (stage₂ o).toXF (.leaf true) negW [])) :=
  chainX_real (F₁ := stage₁) (F₂ := stage₂) rfl rfl stage₁_accepts stage₂_accepts

/-- **The hand-off binds**: the same witness, a satisfying assignment whose
    first variable is `F`, does not prove stage 1 at the hand-off `T`. -/
theorem stage₁_refuses_other : ¬ AcceptsX (stage₁ K).toXF (.leaf true) satW := by
  intro h
  have hg := h.2 (leafStmtX satFirstV K [] []) (by simp [evalStmtOfX, stmtOfX, leavesX, stage₁, XS.toXF])
  have e2 : Eval (leafStmtX satFirstV K [] [] ⬝ (BT.leaf true).enc ⬝ satW) (K ⬝ I) :=
    evalF_sound (k := 256) (by decide)
  cases Eval.deterministic hg e2

end ChainEx
