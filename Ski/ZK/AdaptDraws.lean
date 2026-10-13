import Ski.ZK.FSMultiAdapt

/-!
# A picked statement's bad events, bounded at every table, cost one statement's

`zkbT_adaptive` charges an adaptively picked statement the sum of the
statements' errors, and `zkbT_adaptive_tight` shows that sum is tight for
per-statement bounds.  `zkbT_adaptive_joint` charges once a bad event
shared by every statement.  Here each statement may have its own bad event:
when the pick reads the tables alone and each statement's bad event has
mass at most `β` at every table, the picked statement's bad event costs
`β`, charged once (`zkbT_adaptive_tbl`).  Bad events of the draws alone
meet the per-table bound with their one bound (`zkbT_adaptive_draws`).  A
bound on average over the tables does not suffice: with `bad j H = (H = j)`
and the pick `ix H = H`, each statement's average is `1 / S` and the picked
one's is `1`.

What this asks of a component: its real count, away from a real-side bad
event bounded at every table, at most its simulation, with no other
error.  Not shown: such a decomposition of any composite here.  Their
errors are counts (the PCS's), or collisions with the programmed points
`pts c x`, events indexed by the simulator's challenges rather than of the
real run; and `ROMHide`'s hit event is bounded only on average over the
tables.
-/

set_option autoImplicit false

namespace Circuit
open ZKF

/-- **A tables-only pick pays a per-table-bounded bad event once**:
    statement `j`'s real count away from its own bad event `bad j` is at
    most its simulation (`h`); each `bad j` has mass at most `β` at every
    table (`hbad`).  A pick `ix` reading the tables alone then sees its real
    count at most the statements' simulations, each kept where the pick
    confirms it, plus `K β` per table: the bad events are charged once, not
    once per statement. -/
theorem zkbT_adaptive_tbl {T X C V : Type} {K S β : Nat} {ST : (T → Nat) → Nat} (hST : Lin ST)
    {sm : (X → Nat) → Nat} (hsm : Lin sm) {SC : (C → Nat) → Nat}
    (rv : Nat → T → X → V) (pg : Nat → T → C → X → T) (sv : Nat → T → C → X → V) (bad : Nat → T → X → Bool)
    (h : ∀ j, j < S → ∀ E : T → V → Bool, K * ST (fun H => sm (fun x => indB (E H (rv j H x) && !bad j H x))) ≤
      ST (fun H => SC (fun c => sm (fun x => indB (E (pg j H c x) (sv j H c x))))))
    (hbad : ∀ j, j < S → ∀ H, sm (fun x => indB (bad j H x)) ≤ β)
    (ix : T → Nat) (hix : ∀ H, ix H < S) (E : T → Nat × V → Bool) :
    K * ST (fun H => sm (fun x => indB (E H (ix H, rv (ix H) H x)))) ≤
      sumTo S (fun j => ST (fun H => SC (fun c => sm (fun x =>
        indB (E (pg j H c x) (j, sv j H c x) && decide (ix (pg j H c x) = j)))))) + K * ST (fun _ => β) := by
  have split : ∀ H x, indB (E H (ix H, rv (ix H) H x) && !bad (ix H) H x) =
      sumTo S (fun j => indB ((E H (j, rv j H x) && decide (ix H = j)) && !bad j H x)) := by
    intro H x
    have key : ∀ n, ix H < n → sumTo n (fun j => indB ((E H (j, rv j H x) && decide (ix H = j)) && !bad j H x)) =
        indB (E H (ix H, rv (ix H) H x) && !bad (ix H) H x) := by
      intro n
      induction n with
      | zero => intro hn; exact absurd hn (Nat.not_lt_zero _)
      | succ n ih =>
        intro hn
        show sumTo n _ + indB ((E H (n, rv n H x) && decide (ix H = n)) && !bad n H x) = _
        rcases Nat.lt_or_ge (ix H) n with hl | hl
        · rw [ih hl, decide_eq_false (Nat.ne_of_lt hl), Bool.and_false, Bool.false_and]; rfl
        · have he : ix H = n := Nat.le_antisymm (Nat.le_of_lt_succ hn) hl
          have z : ∀ m, m ≤ n → sumTo m (fun j => indB ((E H (j, rv j H x) && decide (ix H = j)) && !bad j H x)) = 0 := by
            intro m
            induction m with
            | zero => intro _; rfl
            | succ m ihm =>
              intro hm
              have hne : ix H ≠ m := by rw [he]; exact Nat.ne_of_gt hm
              show sumTo m _ + indB ((E H (m, rv m H x) && decide (ix H = m)) && !bad m H x) = 0
              rw [ihm (Nat.le_of_succ_le hm), decide_eq_false hne, Bool.and_false, Bool.false_and]; rfl
          rw [z n (Nat.le_refl n), Nat.zero_add, he, decide_eq_true rfl, Bool.and_true]
    exact (key S (hix H)).symm
  have pt : ∀ H x, indB (E H (ix H, rv (ix H) H x)) ≤
      indB (E H (ix H, rv (ix H) H x) && !bad (ix H) H x) + indB (bad (ix H) H x) :=
    fun H x => by cases E H (ix H, rv (ix H) H x) <;> cases bad (ix H) H x <;> decide
  have each : ∀ j, j < S → K * ST (fun H => sm (fun x => indB ((E H (j, rv j H x) && decide (ix H = j)) && !bad j H x))) ≤
      ST (fun H => SC (fun c => sm (fun x =>
        indB (E (pg j H c x) (j, sv j H c x) && decide (ix (pg j H c x) = j))))) :=
    fun j hj => h j hj (fun H v => E H (j, v) && decide (ix H = j))
  have hb : ST (fun H => sm (fun x => indB (bad (ix H) H x))) ≤ ST (fun _ => β) :=
    sm_mono ST hST (fun H => hbad (ix H) (hix H) H)
  calc K * ST (fun H => sm (fun x => indB (E H (ix H, rv (ix H) H x))))
      ≤ K * ST (fun H => sm (fun x => indB (E H (ix H, rv (ix H) H x) && !bad (ix H) H x) + indB (bad (ix H) H x))) :=
        Nat.mul_le_mul_left _ (sm_mono ST hST (fun H => sm_mono sm hsm (fun x => pt H x)))
    _ = K * ST (fun H => sm (fun x => sumTo S (fun j => indB ((E H (j, rv j H x) && decide (ix H = j)) && !bad j H x)))) +
        K * ST (fun H => sm (fun x => indB (bad (ix H) H x))) := by
        rw [← Nat.mul_add]; congr 1
        rw [← sm_add ST hST]; congr 1; funext H
        rw [← sm_add sm hsm]; congr 1; funext x
        rw [split]
    _ = sumTo S (fun j => K * ST (fun H => sm (fun x => indB ((E H (j, rv j H x) && decide (ix H = j)) && !bad j H x)))) +
        K * ST (fun H => sm (fun x => indB (bad (ix H) H x))) := by
        congr 1
        rw [show (fun H => sm (fun x => sumTo S (fun j => indB ((E H (j, rv j H x) && decide (ix H = j)) && !bad j H x)))) =
            fun H => sumTo S (fun j => sm (fun x => indB ((E H (j, rv j H x) && decide (ix H = j)) && !bad j H x))) from
          funext fun H => hsm S _, hST S _, sumTo_mul]
    _ ≤ _ := Nat.add_le_add (sumTo_mono _ each) (Nat.mul_le_mul_left _ hb)


-- AdaptDraws is the special case

/-- **Bad events of the draws alone** have one bound at every table:
    `zkbT_adaptive_tbl` with `bad j _ x = bad j x`. -/
theorem zkbT_adaptive_draws {T X C V : Type} {K S β : Nat} {ST : (T → Nat) → Nat} (hST : Lin ST)
    {sm : (X → Nat) → Nat} (hsm : Lin sm) {SC : (C → Nat) → Nat}
    (rv : Nat → T → X → V) (pg : Nat → T → C → X → T) (sv : Nat → T → C → X → V) (bad : Nat → X → Bool)
    (h : ∀ j, j < S → ∀ E : T → V → Bool, K * ST (fun H => sm (fun x => indB (E H (rv j H x) && !bad j x))) ≤
      ST (fun H => SC (fun c => sm (fun x => indB (E (pg j H c x) (sv j H c x))))))
    (hbad : ∀ j, j < S → sm (fun x => indB (bad j x)) ≤ β)
    (ix : T → Nat) (hix : ∀ H, ix H < S) (E : T → Nat × V → Bool) :
    K * ST (fun H => sm (fun x => indB (E H (ix H, rv (ix H) H x)))) ≤
      sumTo S (fun j => ST (fun H => SC (fun c => sm (fun x =>
        indB (E (pg j H c x) (j, sv j H c x) && decide (ix (pg j H c x) = j)))))) + K * ST (fun _ => β) :=
  zkbT_adaptive_tbl hST hsm rv pg sv (fun j _ x => bad j x) h (fun j hj _ => hbad j hj) ix hix E

end Circuit
