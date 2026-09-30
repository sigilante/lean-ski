import Ski.Circuit.CompFinal
import Ski.Circuit.CompComplete
import Ski.Predicate
open Term

/-!
# The predicate circuit

The composed circuit of a predicate statement (`Ski/Predicate.lean`): bits
of a comb of `n` and the one term `predStmt V x`.  The bits are the
composed machine's slot cells, which the circuit's witness table constrains
to `K` or `K I`, so the verifier reads a list of Scott Booleans and nothing
a prover can shape.

**`predExport_sound`**: an accepted proof of the predicate circuit
(`predAirs`) has `n` bits `bs` in its memory with `V x (boolsT bs)`
evaluating to `K`.  Its completeness is `comp_completeG_log`, and its zero
knowledge `comp_zk`, both for any evaluation statement.
-/

namespace Circuit

open B Air Compose CompM Stmt Mach Wit

/-- **The composed circuit of a predicate over `n` bits.** -/
def predAirs (V x : Term) (n W : Nat) : List AirD := compAirsG (combBT n) [predStmt V x] W

/-- **Soundness of the predicate circuit**: an accepted proof's memory
    holds `n` literal bits on which the verifier accepts `x`. -/
theorem predExport_sound {V x : Term} {n W : Nat} (hn : 0 < n) {Rs : List AirD} {ts : List Table}
    (hs : sameAirsB Rs (predAirs V x n W) = true) (h : AcceptedP Rs ts) :
    ∃ C Mm Pg Wt Sg, ts = [C, Mm, Pg, Wt, Sg] ∧
      (slotBits (bitsM (memOf Mm)) 0 n).length = n ∧
      Eval (V ⬝ x ⬝ boolsT (slotBits (bitsM (memOf Mm)) 0 n)) K := by
  obtain ⟨C, Mm, Pg, Wt, Sg, rfl, w, _, _, hall⟩ := compExportG_sound (by simp) hs h
  have hP := hall (predStmt V x) List.mem_cons_self
  rw [pred_iff, fillB_combBT _ n 0 hn] at hP
  exact ⟨C, Mm, Pg, Wt, Sg, rfl, slotBits_length _ 0 n, hP⟩

/-- **A checked table proves the predicate**: for a table `checkC` accepts
    for a predicate's statement, the verifier accepts `x` on the bits its
    memory sets. -/
theorem checkPred_sound {V x : Term} {n W : Nat} (hn : 0 < n) {A : Array Cell} {ends : Array Nat}
    {R : Array Air.Row} (h : checkC (combBT n) W [predStmt V x] A ends R = true) :
    Eval (V ⬝ x ⬝ boolsT (slotBits (bitsOf A) 0 n)) K := by
  obtain ⟨w, _, _, hall⟩ := checkC_sound h
  have hP := hall (predStmt V x) List.mem_cons_self
  rwa [pred_iff, fillB_combBT _ n 0 hn] at hP

end Circuit
