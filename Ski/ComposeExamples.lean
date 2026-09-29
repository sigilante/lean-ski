import Ski.Compose
import Ski.WitnessExamples

open Term

/-!
# A composed statement, accepted with one side's witness

The `∨` of the two example atoms of `Ski/WitnessExamples.lean`, as the
monolithic statement of `Ski/Compose.lean`: three evaluation statements,
the formula check and a guard per atom.  The prover knows only the first
side's witness, `negW`: its bits set the first atom and clear the second,
and its witness pairs `negW` with `K` (`negOr_accepts`, checked in the
kernel).  The read-back of those bits and that witness is a realizer of
the disjunction (`negOr_real`).  Bits that set neither atom are refused
(`negOr_refuses_clear`), and so are bits that set the first atom with a
witness it rejects (`negOr_refuses_I`).
-/

namespace ComposeEx

open Compose WitEx

/-- `atom negV x0 ∨ atom satV x0`. -/
def negOr : MF := .or (.atom negV x0) (.atom satV x0)

/-- The first side chosen. -/
def bitsL : BT := .node (.leaf true) (.leaf false)

/-- The first side's witness, and nothing for the second. -/
def witL : Term := pairT negW K

theorem negOr_accepts : Accepts negOr bitsL witL := by
  refine ⟨⟨trivial, trivial⟩, fun P hP => ?_⟩
  simp [evalStmtOf, stmtOf, leaves, negOr] at hP
  rcases hP with rfl | rfl | rfl
  · exact evalF_sound (k := 128) (by decide)
  · exact evalF_sound (k := 128) (by decide)
  · exact evalF_sound (k := 128) (by decide)

theorem negOr_real : Real negOr.toForm (readBack negOr bitsL witL []) :=
  real_of_accepted negOr_accepts

/-- The formula check refuses bits that set neither atom. -/
theorem negOr_refuses_clear (w : Term) : ¬ Accepts negOr (.node (.leaf false) (.leaf false)) w := by
  intro h
  have := (phi_iff h.1 w).1 (h.2 _ (List.mem_cons_self))
  cases this

/-- The first atom's guard refuses the identity as its witness. -/
theorem negOr_refuses_I : ¬ Accepts negOr bitsL (pairT I K) := by
  intro h
  have hg := h.2 (leafStmt negV x0 [false]) (by simp [evalStmtOf, stmtOf, leaves, negOr])
  have := (leaf_iff (V := negV) (x := x0) (W := pairT I K) (β := bitsL) (q := [false]) (b := true)
    rfl (pairT_fst _ _)).1 hg rfl
  -- The component `pairT I K ⬝ K` reduces to `I`, and acceptance moves
  -- forward along weak reduction (Church–Rosser).
  exact neg_not_I ((wsteps_K_iff (WSteps.right _ (pairT_fst I K))).1 this)

end ComposeEx
