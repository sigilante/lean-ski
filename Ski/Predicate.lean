import Ski.Composed
open Term

/-!
# A predicate over literal bits

A formula's atom hands its verifier a component of the hidden witness
term, and a term answers the verifier's case analysis however it likes: a
claim about data does not survive it.  A **predicate statement** hands its
verifier the literal bits instead.  Its shape is a right comb of `n` bits
(`combBT`), and its one term, `predStmt V x = [ρ w] V x ρ`, applies the
public verifier `V` to the public `x` and the bits' encoding, ignoring the
witness (`pred_iff`).  The bits' encoding is a list of Scott Booleans
(`boolsT`, `fillB_combBT`).
-/

namespace CompM

open Mach Compose

/-- The shape of `n` bits: a right comb, the last bit alone. -/
def combBT : Nat → BT
  | 0 => .leaf false
  | 1 => .leaf false
  | n + 2 => .node (.leaf false) (combBT (n + 1))

theorem combBT_nleaves : ∀ n, 0 < n → BT.nleaves (combBT n) = n
  | 1, _ => rfl
  | n + 2, _ => by
    show 1 + BT.nleaves (combBT (n + 1)) = n + 2
    rw [combBT_nleaves (n + 1) (Nat.succ_pos n)]; omega

/-- A list of Booleans as a term: the last alone, each before it paired
    with the rest. -/
def boolsT : List Bool → Term
  | [] => boolT false
  | [b] => boolT b
  | b :: r => pairT (boolT b) (boolsT r)

/-- The bits the machine's slots hold, from `off`, as a list. -/
def slotBits (ρ : Nat → Bool) (off : Nat) : Nat → List Bool
  | 0 => []
  | n + 1 => ρ off :: slotBits ρ (off + 1) n

/-- **The bits of a comb are a list of Scott Booleans.** -/
theorem fillB_combBT (ρ : Nat → Bool) : ∀ (n off : Nat), 0 < n →
    (fillB (combBT n) ρ off).enc = boolsT (slotBits ρ off n)
  | 1, off, _ => rfl
  | n + 2, off, _ => by
    show pairT (boolT (ρ off)) (fillB (combBT (n + 1)) ρ (off + BT.nleaves (.leaf false))).enc =
      boolsT (ρ off :: ρ (off + 1) :: slotBits ρ (off + 2) n)
    rw [show off + BT.nleaves (BT.leaf false) = off + 1 from rfl, fillB_combBT ρ (n + 1) (off + 1) (Nat.succ_pos n)]
    rfl

theorem slotBits_length (ρ : Nat → Bool) : ∀ (off n : Nat), (slotBits ρ off n).length = n
  | _, 0 => rfl
  | off, n + 1 => by simp [slotBits, slotBits_length ρ (off + 1) n]

/-- The predicate's term: `[ρ w] V x ρ`. -/
def predStmt (V x : Term) : Term := toTerm (absN [0, 1] (V.toO ⬝ₒ x.toO ⬝ₒ .var 0))

/-- **The predicate's term accepts exactly when the verifier accepts the
    bits**, whatever the witness. -/
theorem pred_iff (V x B W : Term) : Eval (predStmt V x ⬝ B ⬝ W) K ↔ Eval (V ⬝ x ⬝ B) K := by
  have hred : WSteps (predStmt V x ⬝ B ⬝ W) (V ⬝ x ⬝ B) := by
    have := stmt_beta (V.toO ⬝ₒ x.toO ⬝ₒ .var 0) B W
    rw [show (V.toO ⬝ₒ x.toO ⬝ₒ OTerm.var 0).close (env B W) = V ⬝ x ⬝ B by
      show V.toO.close _ ⬝ x.toO.close _ ⬝ env B W 0 = _
      rw [close_toO, close_toO, env0]] at this
    exact this
  rw [eval_K_iff, eval_K_iff, wsteps_K_iff hred]

end CompM
