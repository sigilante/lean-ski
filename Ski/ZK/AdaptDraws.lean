import Ski.ZK.FSMultiAdapt

/-!
# A picked statement's draw-only bad events cost one statement's

`zkbT_adaptive` charges an adaptively picked statement the sum of the
statements' errors, and `zkbT_adaptive_tight` shows that sum is tight for
per-statement bounds.  `zkbT_adaptive_joint` charges once a bad event
shared by every statement, which no component supplies.  Here the shared
event is not needed: when the pick reads the tables alone and each
statement's bad event is a function of the draws alone, each statement's
own, the picked statement's bad event has mass at most `β` at every table,
so it is charged once (`zkbT_adaptive_draws`).

What this asks of a component: its real count, away from a bad event that
reads the draws but not the tables, at most its simulation, with no other
error.  Not shown: such a decomposition of any composite here.  Their
errors are counts (the PCS's), or collisions read at the simulator's
challenges or at reads computed from the tables, so none is yet of this
form.
-/

set_option autoImplicit false

namespace Circuit
open ZKF

/-- **A tables-only pick pays a draw-only bad event once**: statement `j`'s
    real count away from its own bad event `bad j`, a function of the draws
    alone, is at most its simulation (`h`); each `bad j` has mass at most
    `β` (`hbad`).  A pick `ix` reading the tables alone then sees its real
    count at most the statements' simulations, each kept where the pick
    confirms it, plus `K β` per table: the bad events are charged once, not
    once per statement. -/
theorem zkbT_adaptive_draws {T X C V : Type} {K S β : Nat} {ST : (T → Nat) → Nat} (hST : Lin ST)
    {sm : (X → Nat) → Nat} (hsm : Lin sm) {SC : (C → Nat) → Nat}
    (rv : Nat → T → X → V) (pg : Nat → T → C → X → T) (sv : Nat → T → C → X → V) (bad : Nat → X → Bool)
    (h : ∀ j, j < S → ∀ E : T → V → Bool, K * ST (fun H => sm (fun x => indB (E H (rv j H x) && !bad j x))) ≤
      ST (fun H => SC (fun c => sm (fun x => indB (E (pg j H c x) (sv j H c x))))))
    (hbad : ∀ j, j < S → sm (fun x => indB (bad j x)) ≤ β)
    (ix : T → Nat) (hix : ∀ H, ix H < S) (E : T → Nat × V → Bool) :
    K * ST (fun H => sm (fun x => indB (E H (ix H, rv (ix H) H x)))) ≤
      sumTo S (fun j => ST (fun H => SC (fun c => sm (fun x =>
        indB (E (pg j H c x) (j, sv j H c x) && decide (ix (pg j H c x) = j)))))) + K * ST (fun _ => β) := by
  have split : ∀ H x, indB (E H (ix H, rv (ix H) H x) && !bad (ix H) x) =
      sumTo S (fun j => indB ((E H (j, rv j H x) && decide (ix H = j)) && !bad j x)) := by
    intro H x
    have key : ∀ n, ix H < n → sumTo n (fun j => indB ((E H (j, rv j H x) && decide (ix H = j)) && !bad j x)) =
        indB (E H (ix H, rv (ix H) H x) && !bad (ix H) x) := by
      intro n
      induction n with
      | zero => intro hn; exact absurd hn (Nat.not_lt_zero _)
      | succ n ih =>
        intro hn
        show sumTo n _ + indB ((E H (n, rv n H x) && decide (ix H = n)) && !bad n x) = _
        rcases Nat.lt_or_ge (ix H) n with hl | hl
        · rw [ih hl, decide_eq_false (Nat.ne_of_lt hl), Bool.and_false, Bool.false_and]; rfl
        · have he : ix H = n := Nat.le_antisymm (Nat.le_of_lt_succ hn) hl
          have z : ∀ m, m ≤ n → sumTo m (fun j => indB ((E H (j, rv j H x) && decide (ix H = j)) && !bad j x)) = 0 := by
            intro m
            induction m with
            | zero => intro _; rfl
            | succ m ihm =>
              intro hm
              have hne : ix H ≠ m := by rw [he]; exact Nat.ne_of_gt hm
              show sumTo m _ + indB ((E H (m, rv m H x) && decide (ix H = m)) && !bad m x) = 0
              rw [ihm (Nat.le_of_succ_le hm), decide_eq_false hne, Bool.and_false, Bool.false_and]; rfl
          rw [z n (Nat.le_refl n), Nat.zero_add, he, decide_eq_true rfl, Bool.and_true]
    exact (key S (hix H)).symm
  have pt : ∀ H x, indB (E H (ix H, rv (ix H) H x)) ≤
      indB (E H (ix H, rv (ix H) H x) && !bad (ix H) x) + indB (bad (ix H) x) :=
    fun H x => by cases E H (ix H, rv (ix H) H x) <;> cases bad (ix H) x <;> decide
  have each : ∀ j, j < S → K * ST (fun H => sm (fun x => indB ((E H (j, rv j H x) && decide (ix H = j)) && !bad j x))) ≤
      ST (fun H => SC (fun c => sm (fun x =>
        indB (E (pg j H c x) (j, sv j H c x) && decide (ix (pg j H c x) = j))))) :=
    fun j hj => h j hj (fun H v => E H (j, v) && decide (ix H = j))
  have hb : ST (fun H => sm (fun x => indB (bad (ix H) x))) ≤ ST (fun _ => β) :=
    sm_mono ST hST (fun H => hbad (ix H) (hix H))
  calc K * ST (fun H => sm (fun x => indB (E H (ix H, rv (ix H) H x))))
      ≤ K * ST (fun H => sm (fun x => indB (E H (ix H, rv (ix H) H x) && !bad (ix H) x) + indB (bad (ix H) x))) :=
        Nat.mul_le_mul_left _ (sm_mono ST hST (fun H => sm_mono sm hsm (fun x => pt H x)))
    _ = K * ST (fun H => sm (fun x => sumTo S (fun j => indB ((E H (j, rv j H x) && decide (ix H = j)) && !bad j x)))) +
        K * ST (fun H => sm (fun x => indB (bad (ix H) x))) := by
        rw [← Nat.mul_add]; congr 1
        rw [← sm_add ST hST]; congr 1; funext H
        rw [← sm_add sm hsm]; congr 1; funext x
        rw [split]
    _ = sumTo S (fun j => K * ST (fun H => sm (fun x => indB ((E H (j, rv j H x) && decide (ix H = j)) && !bad j x)))) +
        K * ST (fun H => sm (fun x => indB (bad (ix H) x))) := by
        congr 1
        rw [show (fun H => sm (fun x => sumTo S (fun j => indB ((E H (j, rv j H x) && decide (ix H = j)) && !bad j x)))) =
            fun H => sumTo S (fun j => sm (fun x => indB ((E H (j, rv j H x) && decide (ix H = j)) && !bad j x))) from
          funext fun H => hsm S _, hST S _, sumTo_mul]
    _ ≤ _ := Nat.add_le_add (sumTo_mono _ each) (Nat.mul_le_mul_left _ hb)

end Circuit
