import Ski.ZK.FSMultiStop

/-!
# Statements chosen after seeing the tables

Every multi-proof theorem fixes each proof's statement before the tables are
drawn.  A distinguisher may instead pick the statement from the tables: `ix
H < S` among `S` statements sharing the draws and challenges.  Split by the
statement picked, the real count is at most the sum, over the statements
`j`, of `j`'s simulated count with the pick re-evaluated at `j`'s programmed
tables and equal to `j` (the simulator guesses `j`, programs, and keeps the
guess the distinguisher's pick confirms), plus every statement's error
(`zkbT_adaptive`).  The right side sums over the `S` guesses: it is `S`
times one uniformly guessing simulator's count of the event with its guess
confirmed, and the error is the sum of the `S` statements' errors.  Its mass
stays bounded: with each statement's counts normalized, a `ZKBT` bound read
backwards bounds the simulation by the real count (`zkbT_rev`), so the
confirmed runs over all guesses number at most `K` times the real draws plus
the errors (`zkbT_adaptive_mass`).  The bounds may be composites
(`fs4_interleave`, `fs4_postInterleave`, `zkbT_pair`), `j` indexing the
statement of one proof in them, the others fixed, all `S` composites
sharing their draws and challenges.  The pick reads only the tables, so
making it between proofs gains nothing over making it first: the real world
programs nothing, and the simulator fixes every programmed point before the
run and answers the pick at the composite's fully programmed tables, the
later proofs' included.  Not shown: a pick reading earlier proofs'
transcripts; several statements picked in turn; a tighter bound.
-/

set_option autoImplicit false

namespace Circuit
open ZKF


theorem indB_add_not (b : Bool) : indB b + indB (!b) = 1 := by cases b <;> rfl

/-- **The simulation is at most the real count**, given the normalization
    that the two sides count the same total (`hnorm`): a `ZKBT` bound at the
    complementary event read backwards. -/
theorem zkbT_rev {T X C V : Type} {K ε : Nat} {ST : (T → Nat) → Nat} (hST : Lin ST) {sm : (X → Nat) → Nat}
    (hsm : Lin sm) {SC : (C → Nat) → Nat} (hSC : Lin SC)
    {rv : T → X → V} {pg : T → C → X → T} {sv : T → C → X → V} (h : ZKBT ST K sm SC rv pg sv ε)
    (hnorm : ST (fun _ => SC (fun _ => sm (fun _ => 1))) = K * ST (fun _ => sm (fun _ => 1)))
    (F : T → V → Bool) :
    ST (fun H => SC (fun c => sm (fun x => indB (F (pg H c x) (sv H c x))))) ≤
      K * ST (fun H => sm (fun x => indB (F H (rv H x)))) + ε := by
  have hc := h (fun H v => !F H v)
  have tsim : ST (fun H => SC (fun c => sm (fun x => indB (F (pg H c x) (sv H c x))))) +
      ST (fun H => SC (fun c => sm (fun x => indB (!F (pg H c x) (sv H c x))))) =
      ST (fun _ => SC (fun _ => sm (fun _ => 1))) := by
    rw [← sm_add ST hST]
    congr 1; funext H
    rw [← sm_add SC hSC]
    congr 1; funext c
    rw [← sm_add sm hsm]
    congr 1; funext x
    exact indB_add_not _
  have treal : ST (fun H => sm (fun x => indB (F H (rv H x)))) + ST (fun H => sm (fun x => indB (!F H (rv H x)))) =
      ST (fun _ => sm (fun _ => 1)) := by
    rw [← sm_add ST hST]
    congr 1; funext H
    rw [← sm_add sm hsm]
    congr 1; funext x
    exact indB_add_not _
  have hc' : K * ST (fun H => sm (fun x => indB (!F H (rv H x)))) ≤
      ST (fun H => SC (fun c => sm (fun x => indB (!F (pg H c x) (sv H c x))))) + ε := hc
  -- sim F = tot − sim ¬F ≤ tot − K real ¬F + ε = K real F + ε
  have e1 := congrArg (K * ·) treal
  simp only [Nat.mul_add] at e1
  rw [hnorm] at tsim
  omega

/-- **A statement picked from the tables.** If each of `S` statements, with
    common draws and challenges, meets a `ZKBT` bound, the view of the
    statement the distinguisher picks from the tables (`ix H < S`), the pick
    shown, is at most the sum of the statements' simulations, each kept
    where the pick at its programmed tables confirms it, plus the errors. -/
theorem zkbT_adaptive {T X C V : Type} {K S : Nat} {ST : (T → Nat) → Nat} (hST : Lin ST) {sm : (X → Nat) → Nat}
    (hsm : Lin sm) {SC : (C → Nat) → Nat}
    (rv : Nat → T → X → V) (pg : Nat → T → C → X → T) (sv : Nat → T → C → X → V) (ε : Nat → Nat)
    (h : ∀ j, j < S → ZKBT ST K sm SC (rv j) (pg j) (sv j) (ε j)) (ix : T → Nat) (hix : ∀ H, ix H < S)
    (E : T → Nat × V → Bool) :
    K * ST (fun H => sm (fun x => indB (E H (ix H, rv (ix H) H x)))) ≤
      sumTo S (fun j => ST (fun H => SC (fun c => sm (fun x =>
        indB (E (pg j H c x) (j, sv j H c x) && decide (ix (pg j H c x) = j)))))) + sumTo S ε := by
  -- the real count splits by the statement picked
  have split : ∀ H x, indB (E H (ix H, rv (ix H) H x)) =
      sumTo S (fun j => indB (E H (j, rv j H x) && decide (ix H = j))) := by
    intro H x
    have key : ∀ n, ix H < n → sumTo n (fun j => indB (E H (j, rv j H x) && decide (ix H = j))) =
        indB (E H (ix H, rv (ix H) H x)) := by
      intro n
      induction n with
      | zero => intro hn; exact absurd hn (Nat.not_lt_zero _)
      | succ n ih =>
        intro hn
        show sumTo n _ + indB (E H (n, rv n H x) && decide (ix H = n)) = _
        rcases Nat.lt_or_ge (ix H) n with hl | hl
        · rw [ih hl]
          have : ix H ≠ n := Nat.ne_of_lt hl
          simp only [decide_eq_false this, Bool.and_false]
          rfl
        · have he : ix H = n := Nat.le_antisymm (Nat.le_of_lt_succ hn) hl
          have h0 : sumTo n (fun j => indB (E H (j, rv j H x) && decide (ix H = j))) = 0 := by
            have z : ∀ m, m ≤ n → sumTo m (fun j => indB (E H (j, rv j H x) && decide (ix H = j))) = 0 := by
              intro m
              induction m with
              | zero => intro _; rfl
              | succ m ihm =>
                intro hm
                show sumTo m _ + _ = 0
                have hne : ix H ≠ m := by rw [he]; exact Nat.ne_of_gt hm
                rw [ihm (Nat.le_of_succ_le hm)]
                simp only [decide_eq_false hne, Bool.and_false]
                rfl
            exact z n (Nat.le_refl n)
          rw [h0, Nat.zero_add, he]
          simp only [decide_true, Bool.and_true]
    exact (key S (hix H)).symm
  -- each statement's share is bounded by its own simulation
  have each : ∀ j, j < S → K * ST (fun H => sm (fun x => indB (E H (j, rv j H x) && decide (ix H = j)))) ≤
      ST (fun H => SC (fun c => sm (fun x => indB (E (pg j H c x) (j, sv j H c x) && decide (ix (pg j H c x) = j))))) + ε j :=
    fun j hj => h j hj (fun H v => E H (j, v) && decide (ix H = j))
  calc K * ST (fun H => sm (fun x => indB (E H (ix H, rv (ix H) H x))))
      = K * ST (fun H => sm (fun x => sumTo S (fun j => indB (E H (j, rv j H x) && decide (ix H = j))))) := by
        simp only [split]
    _ = sumTo S (fun j => K * ST (fun H => sm (fun x => indB (E H (j, rv j H x) && decide (ix H = j))))) := by
        rw [show (fun H => sm (fun x => sumTo S (fun j => indB (E H (j, rv j H x) && decide (ix H = j))))) =
            fun H => sumTo S (fun j => sm (fun x => indB (E H (j, rv j H x) && decide (ix H = j)))) from
          funext fun H => hsm S _, hST S _, sumTo_mul]
    _ ≤ sumTo S (fun j => ST (fun H => SC (fun c => sm (fun x =>
          indB (E (pg j H c x) (j, sv j H c x) && decide (ix (pg j H c x) = j))))) + ε j) := sumTo_mono _ each
    _ = _ := sumTo_add _ _ _

theorem sum_indB_eq (a : Nat) : ∀ S, a < S → sumTo S (fun j => indB (decide (a = j))) = 1
  | 0, h => absurd h (Nat.not_lt_zero _)
  | S + 1, h => by
    show sumTo S _ + indB (decide (a = S)) = 1
    rcases Nat.lt_or_ge a S with hl | hl
    · rw [sum_indB_eq a S hl, decide_eq_false (Nat.ne_of_lt hl)]; rfl
    · have he : a = S := Nat.le_antisymm (Nat.le_of_lt_succ h) hl
      have z : ∀ m, m ≤ S → sumTo m (fun j => indB (decide (a = j))) = 0 := by
        intro m
        induction m with
        | zero => intro _; rfl
        | succ m ihm =>
          intro hm
          have hne : a ≠ m := by rw [he]; exact Nat.ne_of_gt hm
          show sumTo m (fun j => indB (decide (a = j))) + indB (decide (a = m)) = 0
          rw [ihm (Nat.le_of_succ_le hm), decide_eq_false hne]; rfl
      rw [z S (Nat.le_refl S)]
      show 0 + indB (decide (a = S)) = 1
      rw [decide_eq_true he]; rfl

/-- **The guesses' confirmed simulations have bounded mass**: summed over
    the `S` guesses, the simulated runs whose pick confirms the guess number
    at most `K` times the real draws plus the errors, given each statement's
    normalization (`zkbT_rev`).  So `zkbT_adaptive`'s right side is, up to
    the errors, a sub-distribution of the real draws' total, not `S` times
    it. -/
theorem zkbT_adaptive_mass {T X C V : Type} {K S : Nat} {ST : (T → Nat) → Nat} (hST : Lin ST) {sm : (X → Nat) → Nat}
    (hsm : Lin sm) {SC : (C → Nat) → Nat} (hSC : Lin SC)
    (rv : Nat → T → X → V) (pg : Nat → T → C → X → T) (sv : Nat → T → C → X → V) (ε : Nat → Nat)
    (h : ∀ j, j < S → ZKBT ST K sm SC (rv j) (pg j) (sv j) (ε j))
    (hnorm : ST (fun _ => SC (fun _ => sm (fun _ => 1))) = K * ST (fun _ => sm (fun _ => 1)))
    (ix : T → Nat) (hix : ∀ H, ix H < S) :
    sumTo S (fun j => ST (fun H => SC (fun c => sm (fun x => indB (decide (ix (pg j H c x) = j)))))) ≤
      K * ST (fun _ => sm (fun _ => 1)) + sumTo S ε := by
  have each : ∀ j, j < S → ST (fun H => SC (fun c => sm (fun x => indB (decide (ix (pg j H c x) = j))))) ≤
      K * ST (fun H => sm (fun _ => indB (decide (ix H = j)))) + ε j :=
    fun j hj => zkbT_rev hST hsm hSC (h j hj) hnorm (fun H _ => decide (ix H = j))
  refine Nat.le_trans (sumTo_mono _ each) ?_
  rw [sumTo_add, ← sumTo_mul]
  refine Nat.add_le_add_right (Nat.mul_le_mul_left _ (Nat.le_of_eq ?_)) _
  rw [← hST S (fun j H => sm (fun _ => indB (decide (ix H = j))))]
  congr 1; funext H
  rw [← hsm S (fun j _ => indB (decide (ix H = j)))]
  congr 1; funext _
  exact sum_indB_eq (ix H) S (hix H)

end Circuit
