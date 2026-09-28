import Ski.SmallLemma
import Ski.HeapOpen

open Term

/-!
# Boolean formulas as combinators, read by a probe

A Boolean is a Scott Boolean: `true` is `K` (`K x y ⟶ x`) and `false` is
`K I` (`K I x y ⟶ I y ⟶ y`).  A formula over Boolean inputs compiles to a
term that selects between two continuations:

- `a ∧ b` is `a b F`, `a ∨ b` is `a T b`, `¬ a` is `a F T`.

Every input and constant of the compiled term is a **slot**: a variable
that a statement fills with a shared cell (`Ski/Statement.lean`), so an
input read many times is one cell.  `fill ρ` fills the input slots with the
Booleans `ρ` gives and the constant slots with `K` and `K I`.

**The theorems.**
- `bool_reduce`: the filled formula, applied to `x` and `y`, reduces by
  open head reduction to `x` when the formula is true under `ρ` and to `y`
  when it is false.
- `probe_true`: so applied to two distinct markers, if it reaches the
  first marker at the head, the formula is true.  Head reduction is
  deterministic, and the other marker's spine cannot be reached as well
  (`osteps_neutral_det`).
-/

/-- Boolean formulas over numbered inputs. -/
inductive BExpr where
  | var (n : Nat)
  | tt
  | ff
  | and (a b : BExpr)
  | or (a b : BExpr)
  | not (a : BExpr)
  deriving Repr

namespace BExpr

def eval (ρ : Nat → Bool) : BExpr → Bool
  | var n => ρ n
  | tt => true
  | ff => false
  | and a b => eval ρ a && eval ρ b
  | or a b => eval ρ a || eval ρ b
  | not a => !eval ρ a

/-- The slot of the constant `true`; `false` is the next.  Inputs are
    shifted past them. -/
def TT : Nat := 0
def FF : Nat := 1
def inSlot (n : Nat) : Nat := n + 2

/-- The formula as a selector over slots. -/
def compile : BExpr → OTerm
  | var n => .var (inSlot n)
  | tt => .var TT
  | ff => .var FF
  | and a b => compile a ⬝ₒ compile b ⬝ₒ .var FF
  | or a b => compile a ⬝ₒ .var TT ⬝ₒ compile b
  | not a => compile a ⬝ₒ .var FF ⬝ₒ .var TT

/-- A Scott Boolean. -/
def sbool : Bool → OTerm
  | true => .K
  | false => .K ⬝ₒ .I

/-- What a slot holds under the inputs `ρ`. -/
def slotVal (ρ : Nat → Bool) : Nat → OTerm
  | 0 => .K
  | 1 => .K ⬝ₒ .I
  | n + 2 => sbool (ρ n)

/-- The formula with its slots filled. -/
def fill (ρ : Nat → Bool) (e : BExpr) : OTerm := (compile e).subst (slotVal ρ)

theorem sbool_sel (b : Bool) (x y : OTerm) : OSteps (sbool b ⬝ₒ x ⬝ₒ y) (if b then x else y) := by
  cases b with
  | true => exact OSteps.single (.K x y)
  | false =>
    show OSteps (.K ⬝ₒ .I ⬝ₒ x ⬝ₒ y) y
    exact .step (.left y (.K .I x)) (OSteps.single (.I y))

theorem fill_tt (ρ : Nat → Bool) : fill ρ tt = sbool true := rfl
theorem fill_ff (ρ : Nat → Bool) : fill ρ ff = sbool false := rfl

/-- **Boolean reduction.**  The filled formula selects `x` when true and `y`
    when false. -/
theorem bool_reduce (ρ : Nat → Bool) : ∀ (e : BExpr) (x y : OTerm),
    OSteps (fill ρ e ⬝ₒ x ⬝ₒ y) (if eval ρ e then x else y)
  | var n, x, y => sbool_sel (ρ n) x y
  | tt, x, y => sbool_sel true x y
  | ff, x, y => sbool_sel false x y
  | and a b, x, y => by
    show OSteps (fill ρ a ⬝ₒ fill ρ b ⬝ₒ sbool false ⬝ₒ x ⬝ₒ y)
      (if (eval ρ a && eval ρ b) = true then x else y)
    have ha := (bool_reduce ρ a (fill ρ b) (sbool false)).left x |>.left y
    refine ha.trans ?_
    cases eval ρ a with
    | true =>
      rw [if_pos rfl, Bool.true_and]
      exact bool_reduce ρ b x y
    | false =>
      rw [if_neg Bool.false_ne_true, Bool.false_and, if_neg Bool.false_ne_true]
      have h := sbool_sel false x y
      rw [if_neg Bool.false_ne_true] at h
      exact h
  | or a b, x, y => by
    show OSteps (fill ρ a ⬝ₒ sbool true ⬝ₒ fill ρ b ⬝ₒ x ⬝ₒ y)
      (if (eval ρ a || eval ρ b) = true then x else y)
    have ha := (bool_reduce ρ a (sbool true) (fill ρ b)).left x |>.left y
    refine ha.trans ?_
    cases eval ρ a with
    | true =>
      rw [if_pos rfl, Bool.true_or, if_pos rfl]
      have h := sbool_sel true x y
      rw [if_pos rfl] at h
      exact h
    | false =>
      rw [if_neg Bool.false_ne_true, Bool.false_or]
      exact bool_reduce ρ b x y
  | not a, x, y => by
    show OSteps (fill ρ a ⬝ₒ sbool false ⬝ₒ sbool true ⬝ₒ x ⬝ₒ y)
      (if (!eval ρ a) = true then x else y)
    have ha := (bool_reduce ρ a (sbool false) (sbool true)).left x |>.left y
    refine ha.trans ?_
    cases eval ρ a with
    | true =>
      rw [if_pos rfl, Bool.not_true, if_neg Bool.false_ne_true]
      have h := sbool_sel false x y
      rw [if_neg Bool.false_ne_true] at h
      exact h
    | false =>
      rw [if_neg Bool.false_ne_true, Bool.not_false, if_pos rfl]
      have h := sbool_sel true x y
      rw [if_pos rfl] at h
      exact h

/-- **The probe reads the formula.**  Applied to two distinct markers, if
    the filled formula reaches the first marker at the head, it is true. -/
theorem probe_true {ρ : Nat → Bool} {e : BExpr} {acc rej : Nat} (hne : acc ≠ rej)
    {args : List OTerm} (h : OSteps (fill ρ e ⬝ₒ .var acc ⬝ₒ .var rej) (appL (.var acc) args)) :
    eval ρ e = true := by
  cases hv : eval ρ e with
  | true => rfl
  | false =>
    have hr := bool_reduce ρ e (.var acc) (.var rej)
    rw [hv] at hr
    have e1 := osteps_neutral_det h (Mach.ONeutral.appL args (.var acc)) hr (.var rej)
    have n1 : nhead (appL (.var acc) args) = some (acc, 0 + args.length) := nhead_appL args rfl
    rw [e1] at n1
    simp [nhead] at n1
    exact absurd n1.1.symm hne

-- ---------------------------------------------------------------------------
-- Big conjunctions and disjunctions
-- ---------------------------------------------------------------------------

/-- The conjunction of a list, `tt` when empty. -/
def all : List BExpr → BExpr
  | [] => tt
  | [a] => a
  | a :: as => and a (all as)

/-- The disjunction of a list, `ff` when empty. -/
def any : List BExpr → BExpr
  | [] => ff
  | [a] => a
  | a :: as => or a (any as)

theorem eval_all (ρ : Nat → Bool) : ∀ l : List BExpr, eval ρ (all l) = l.all (eval ρ)
  | [] => rfl
  | [a] => by simp [all]
  | a :: b :: as => by
    show (eval ρ a && eval ρ (all (b :: as))) = _
    rw [eval_all ρ (b :: as)]
    simp

theorem eval_any (ρ : Nat → Bool) : ∀ l : List BExpr, eval ρ (any l) = l.any (eval ρ)
  | [] => rfl
  | [a] => by simp [any]
  | a :: b :: as => by
    show (eval ρ a || eval ρ (any (b :: as))) = _
    rw [eval_any ρ (b :: as)]
    simp

end BExpr
