import Ski.Composed
import Ski.ComposeX

open Term

/-!
# A checked table proves a formula with `∃` and knowledge implication

`CompM.checkC_sound` holds for any evaluation statement: a table the
checker accepts proves the statement's terms for the bits its memory sets
and the witness its region holds.  A formula with `∃` and knowledge
implication compiles to such a statement (`Compose.stmtOfX`), its bits'
shape `Compose.clearX`'s, so the circuit, the prover and the checker apply
as they are.  `checkCX_realizes`: for a named, well-formed formula
(`Compose.XS`), the bits and witness of a checked table are accepted by
the formula's statement and read back as a realizer of the formula it
concludes.
-/

namespace CompM

open Compose

theorem shape_of_sameX : ∀ (M : XF) (β : BT), SameShape (clearX M) β → ShapeX M β
  | .atom _ _, .leaf _, _ => trivial
  | .atom _ _, .node _ _, h => h.elim
  | .and A B, .node l r, h => ⟨shape_of_sameX A l h.1, shape_of_sameX B r h.2⟩
  | .and _ _, .leaf _, h => h.elim
  | .or A B, .node l r, h => ⟨shape_of_sameX A l h.1, shape_of_sameX B r h.2⟩
  | .or _ _, .leaf _, h => h.elim
  | .ex B, .node (.leaf _) r, h => shape_of_sameX B r h.2
  | .ex _, .node (.node _ _) _, h => h.1.elim
  | .ex _, .leaf _, h => h.elim
  | .mp _ _ A, β, h => shape_of_sameX A β h

/-- **A checked table proves a formula with `∃` and knowledge
    implication.** -/
theorem checkCX_realizes {s : XS} {W : Nat} {A : Array Cell} {ends : Array Nat} {R : Array Air.Row}
    (hw : s.wf = true) (h : checkC (clearX s.toXF) W (stmtOfX s.toXF) A ends R = true) :
    ∃ w, cWitness (bitsOf A) (BT.nleaves (clearX s.toXF)) (regionOf A (BT.nleaves (clearX s.toXF)) W) = some w ∧
      AcceptsX s.toXF (fillB (clearX s.toXF) (bitsOf A) 0) w ∧
      Real (s.toXF.form []) (readBackX s.toXF (fillB (clearX s.toXF) (bitsOf A) 0) w []) := by
  obtain ⟨w, hw', hs, hall⟩ := checkC_sound h
  have hacc : AcceptsX s.toXF (fillB (clearX s.toXF) (bitsOf A) 0) w := ⟨shape_of_sameX s.toXF _ hs, hall⟩
  exact ⟨w, hw', hacc, real_of_acceptedXS hacc hw⟩

end CompM
