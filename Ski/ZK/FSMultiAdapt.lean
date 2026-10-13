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
statement of one proof in them, the others fixed, all `S` composites sharing
their draws and challenges.  The pick reads only the tables, so making it
between proofs gains nothing over making it first: the real world programs
nothing, and the simulator fixes every programmed point before the run and
answers the pick at the composite's fully programmed tables, the later
proofs' included.  The pick may also read the real view where it agrees
across the `S` statements (`zkbT_adaptiveV`, `hcons`): in a composite
indexed by proof `m`'s statement, every other component's real view, the
earlier proofs' transcripts among them; the simulation reads the pick off
its own simulated view and programmed tables, and the mass bound carries
over (`zkbT_adaptiveV_mass`). The split needs only that the pick read off
statement `j`'s own view confirms `j` exactly at the real pick
(`zkbT_adaptiveF`), which two picks in turn meet, the second read from the
view the first determines (`seqPick_fix`, statements indexed `j1 + S1 j2`);
`k` picks in turn, indexed in mixed radix with each pick reading `rv (j %
(S1⋯S_{i-1}))`, by `k - 1` steps from one pick (`seqPick_one`,
`seqPick_step`, whose conclusions are its own hypotheses over the larger
range).  The statements number `S1 S2` (`S1⋯Sk` for `k` picks), all sharing
their draws and challenges, and so does the error's factor.  Any two
Sudoku puzzles' proofs with the same parameters share their draws
(`SudDraws`'s `sud_sm_eq`).  A pick with
coins of its own sums fixed picks over the coins, the simulator running
the distinguisher on coins it draws: from the tables (`zkbT_adaptiveR`),
from the view or in turn (`zkbT_adaptiveFR`), its mass `R` times one
pick's (`zkbT_adaptiveV_massR`).  A pick
reading the draws beyond the view is no distinguisher's, which sees the
tables and the views alone; this is the model's definition, not a
theorem.  The sum of the statements' errors is tight
for these hypotheses: `S` statements each meeting `ZKBT` with error `1`
can make the picked real count `S` with every confirmed simulation `0`
(`zkbT_adaptive_tight`).  A tighter bound needs a joint hypothesis across
the statements: when every statement's real count is at most its
simulation away from one shared bad event, its mass is charged once
(`zkbT_adaptive_joint`).  No component here supplies that hypothesis yet:
their errors are numbers, or collisions read at the simulator's
challenges, and a hit on a statement's own programmed point is not
shared, so the union of the statements' events costs their sum again.  The
saving needs a bad event independent of the statement.
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

/-- **A pick with coins of its own**: the distinguisher draws `r < R` and
    picks `ix r H`; its count, summed over the coins, is the sum over the
    coins of `zkbT_adaptive`'s bound at each fixed pick, the error `R` times
    each pick's. -/
theorem zkbT_adaptiveR {T X C V : Type} {K S R : Nat} {ST : (T → Nat) → Nat} (hST : Lin ST)
    {sm : (X → Nat) → Nat} (hsm : Lin sm) {SC : (C → Nat) → Nat}
    (rv : Nat → T → X → V) (pg : Nat → T → C → X → T) (sv : Nat → T → C → X → V) (ε : Nat → Nat)
    (h : ∀ j, j < S → ZKBT ST K sm SC (rv j) (pg j) (sv j) (ε j)) (ix : Nat → T → Nat)
    (hix : ∀ r H, ix r H < S) (E : Nat → T → Nat × V → Bool) :
    K * sumTo R (fun r => ST (fun H => sm (fun x => indB (E r H (ix r H, rv (ix r H) H x))))) ≤
      sumTo R (fun r => sumTo S (fun j => ST (fun H => SC (fun c => sm (fun x =>
        indB (E r (pg j H c x) (j, sv j H c x) && decide (ix r (pg j H c x) = j))))))) +
        R * sumTo S ε := by
  rw [sumTo_mul, ← sumTo_const (sumTo S ε) R, ← sumTo_add]
  exact sumTo_mono R (fun r _ => zkbT_adaptive hST hsm rv pg sv ε h (ix r) (hix r) (E r))

/-- **A statement picked from the view**: the pick `ix H v < S` reads the
    tables and the view, but only the part every statement's view shares
    (`hcons`, as the earlier proofs' transcripts in a composite indexed by a
    later proof's statement).  The real pick is then well defined
    (`ix H (rv 0 H x)`), and the same split bounds it: each statement's
    simulation kept where the pick read off its simulated view and
    programmed tables confirms it. -/
theorem zkbT_adaptiveV {T X C V : Type} {K S : Nat} {ST : (T → Nat) → Nat} (hST : Lin ST) {sm : (X → Nat) → Nat}
    (hsm : Lin sm) {SC : (C → Nat) → Nat}
    (rv : Nat → T → X → V) (pg : Nat → T → C → X → T) (sv : Nat → T → C → X → V) (ε : Nat → Nat)
    (h : ∀ j, j < S → ZKBT ST K sm SC (rv j) (pg j) (sv j) (ε j)) (ix : T → V → Nat) (hix : ∀ H v, ix H v < S)
    (hcons : ∀ j H x, ix H (rv j H x) = ix H (rv 0 H x)) (E : T → Nat × V → Bool) :
    K * ST (fun H => sm (fun x => indB (E H (ix H (rv 0 H x), rv (ix H (rv 0 H x)) H x)))) ≤
      sumTo S (fun j => ST (fun H => SC (fun c => sm (fun x =>
        indB (E (pg j H c x) (j, sv j H c x) && decide (ix (pg j H c x) (sv j H c x) = j)))))) + sumTo S ε := by
  have split : ∀ H x, indB (E H (ix H (rv 0 H x), rv (ix H (rv 0 H x)) H x)) =
      sumTo S (fun j => indB (E H (j, rv j H x) && decide (ix H (rv j H x) = j))) := by
    intro H x
    have e : ∀ j, (E H (j, rv j H x) && decide (ix H (rv j H x) = j)) =
        (E H (j, rv j H x) && decide (ix H (rv 0 H x) = j)) := fun j => by rw [hcons j H x]
    simp only [e]
    -- the same split as `zkbT_adaptive`, at the pick `a := ix H (rv 0 H x)`
    generalize ha : ix H (rv 0 H x) = a
    have hal : a < S := ha ▸ hix H (rv 0 H x)
    have key : ∀ n, a < n → sumTo n (fun j => indB (E H (j, rv j H x) && decide (a = j))) =
        indB (E H (a, rv a H x)) := by
      intro n
      induction n with
      | zero => intro hn; exact absurd hn (Nat.not_lt_zero _)
      | succ n ih =>
        intro hn
        show sumTo n _ + indB (E H (n, rv n H x) && decide (a = n)) = _
        rcases Nat.lt_or_ge a n with hl | hl
        · rw [ih hl, decide_eq_false (Nat.ne_of_lt hl), Bool.and_false]; rfl
        · have he : a = n := Nat.le_antisymm (Nat.le_of_lt_succ hn) hl
          have z : ∀ m, m ≤ n → sumTo m (fun j => indB (E H (j, rv j H x) && decide (a = j))) = 0 := by
            intro m
            induction m with
            | zero => intro _; rfl
            | succ m ihm =>
              intro hm
              have hne : a ≠ m := by rw [he]; exact Nat.ne_of_gt hm
              show sumTo m (fun j => indB (E H (j, rv j H x) && decide (a = j))) +
                indB (E H (m, rv m H x) && decide (a = m)) = 0
              rw [ihm (Nat.le_of_succ_le hm), decide_eq_false hne, Bool.and_false]; rfl
          rw [z n (Nat.le_refl n), Nat.zero_add, he, decide_eq_true rfl, Bool.and_true]
    exact (key S hal).symm
  have each : ∀ j, j < S → K * ST (fun H => sm (fun x => indB (E H (j, rv j H x) && decide (ix H (rv j H x) = j)))) ≤
      ST (fun H => SC (fun c => sm (fun x =>
        indB (E (pg j H c x) (j, sv j H c x) && decide (ix (pg j H c x) (sv j H c x) = j))))) + ε j :=
    fun j hj => h j hj (fun H v => E H (j, v) && decide (ix H v = j))
  calc K * ST (fun H => sm (fun x => indB (E H (ix H (rv 0 H x), rv (ix H (rv 0 H x)) H x))))
      = K * ST (fun H => sm (fun x => sumTo S (fun j => indB (E H (j, rv j H x) && decide (ix H (rv j H x) = j))))) := by
        simp only [split]
    _ = sumTo S (fun j => K * ST (fun H => sm (fun x => indB (E H (j, rv j H x) && decide (ix H (rv j H x) = j))))) := by
        rw [show (fun H => sm (fun x => sumTo S (fun j => indB (E H (j, rv j H x) && decide (ix H (rv j H x) = j))))) =
            fun H => sumTo S (fun j => sm (fun x => indB (E H (j, rv j H x) && decide (ix H (rv j H x) = j)))) from
          funext fun H => hsm S _, hST S _, sumTo_mul]
    _ ≤ _ := Nat.le_trans (sumTo_mono _ each) (Nat.le_of_eq (sumTo_add _ _ _))

/-- **`zkbT_adaptive_mass` for a pick read from the view.** -/
theorem zkbT_adaptiveV_mass {T X C V : Type} {K S : Nat} {ST : (T → Nat) → Nat} (hST : Lin ST) {sm : (X → Nat) → Nat}
    (hsm : Lin sm) {SC : (C → Nat) → Nat} (hSC : Lin SC)
    (rv : Nat → T → X → V) (pg : Nat → T → C → X → T) (sv : Nat → T → C → X → V) (ε : Nat → Nat)
    (h : ∀ j, j < S → ZKBT ST K sm SC (rv j) (pg j) (sv j) (ε j))
    (hnorm : ST (fun _ => SC (fun _ => sm (fun _ => 1))) = K * ST (fun _ => sm (fun _ => 1)))
    (ix : T → V → Nat) (hix : ∀ H v, ix H v < S) (hcons : ∀ j H x, ix H (rv j H x) = ix H (rv 0 H x)) :
    sumTo S (fun j => ST (fun H => SC (fun c => sm (fun x => indB (decide (ix (pg j H c x) (sv j H c x) = j)))))) ≤
      K * ST (fun _ => sm (fun _ => 1)) + sumTo S ε := by
  have each : ∀ j, j < S → ST (fun H => SC (fun c => sm (fun x => indB (decide (ix (pg j H c x) (sv j H c x) = j))))) ≤
      K * ST (fun H => sm (fun x => indB (decide (ix H (rv 0 H x) = j)))) + ε j := fun j hj => by
    have r := zkbT_rev hST hsm hSC (h j hj) hnorm (fun H v => decide (ix H v = j))
    simp only [hcons] at r
    exact r
  refine Nat.le_trans (sumTo_mono _ each) ?_
  rw [sumTo_add, ← sumTo_mul]
  refine Nat.add_le_add_right (Nat.mul_le_mul_left _ (Nat.le_of_eq ?_)) _
  rw [← hST S (fun j H => sm (fun x => indB (decide (ix H (rv 0 H x) = j))))]
  congr 1; funext H
  rw [← hsm S (fun j x => indB (decide (ix H (rv 0 H x) = j)))]
  congr 1; funext x
  exact sum_indB_eq (ix H (rv 0 H x)) S (hix H _)

/-- **The pick as a fixed point**: `zkbT_adaptiveV`'s split needs only that
    the pick read off statement `j`'s own view confirms `j` exactly at the
    real pick `r H x < S` (`hfix`). -/
theorem zkbT_adaptiveF {T X C V : Type} {K S : Nat} {ST : (T → Nat) → Nat} (hST : Lin ST) {sm : (X → Nat) → Nat}
    (hsm : Lin sm) {SC : (C → Nat) → Nat}
    (rv : Nat → T → X → V) (pg : Nat → T → C → X → T) (sv : Nat → T → C → X → V) (ε : Nat → Nat)
    (h : ∀ j, j < S → ZKBT ST K sm SC (rv j) (pg j) (sv j) (ε j)) (ix : T → V → Nat)
    (r : T → X → Nat) (hr : ∀ H x, r H x < S) (hfix : ∀ H x j, j < S → (ix H (rv j H x) = j ↔ j = r H x))
    (E : T → Nat × V → Bool) :
    K * ST (fun H => sm (fun x => indB (E H (r H x, rv (r H x) H x)))) ≤
      sumTo S (fun j => ST (fun H => SC (fun c => sm (fun x =>
        indB (E (pg j H c x) (j, sv j H c x) && decide (ix (pg j H c x) (sv j H c x) = j)))))) + sumTo S ε := by
  have split : ∀ H x, indB (E H (r H x, rv (r H x) H x)) =
      sumTo S (fun j => indB (E H (j, rv j H x) && decide (ix H (rv j H x) = j))) := by
    intro H x
    have key : ∀ n, n ≤ S → sumTo n (fun j => indB (E H (j, rv j H x) && decide (ix H (rv j H x) = j))) =
        if r H x < n then indB (E H (r H x, rv (r H x) H x)) else 0 := by
      intro n
      induction n with
      | zero => intro _; simp [sumTo]
      | succ n ih =>
        intro hn
        show sumTo n _ + indB (E H (n, rv n H x) && decide (ix H (rv n H x) = n)) = _
        rw [ih (Nat.le_of_succ_le hn)]
        have hiff := hfix H x n hn
        by_cases hrn : n = r H x
        · rw [decide_eq_true (hiff.2 hrn), Bool.and_true, ← hrn]
          simp only [Nat.lt_irrefl, if_false, Nat.lt_succ_self, if_true, Nat.zero_add]
        · have hne : ix H (rv n H x) ≠ n := fun e => hrn (hiff.1 e)
          rw [decide_eq_false hne, Bool.and_false]
          by_cases hl : r H x < n
          · have : r H x < n + 1 := Nat.lt_succ_of_lt hl
            simp only [hl, if_true, this]; rfl
          · have : ¬ r H x < n + 1 := fun h' => hl (Nat.lt_of_le_of_ne (Nat.le_of_lt_succ h') (fun e => hrn e.symm))
            simp only [hl, if_false, this]; rfl
    rw [key S (Nat.le_refl S), if_pos (hr H x)]
  have each : ∀ j, j < S → K * ST (fun H => sm (fun x => indB (E H (j, rv j H x) && decide (ix H (rv j H x) = j)))) ≤
      ST (fun H => SC (fun c => sm (fun x =>
        indB (E (pg j H c x) (j, sv j H c x) && decide (ix (pg j H c x) (sv j H c x) = j))))) + ε j :=
    fun j hj => h j hj (fun H v => E H (j, v) && decide (ix H v = j))
  calc K * ST (fun H => sm (fun x => indB (E H (r H x, rv (r H x) H x))))
      = K * ST (fun H => sm (fun x => sumTo S (fun j => indB (E H (j, rv j H x) && decide (ix H (rv j H x) = j))))) := by
        simp only [split]
    _ = sumTo S (fun j => K * ST (fun H => sm (fun x => indB (E H (j, rv j H x) && decide (ix H (rv j H x) = j))))) := by
        rw [show (fun H => sm (fun x => sumTo S (fun j => indB (E H (j, rv j H x) && decide (ix H (rv j H x) = j))))) =
            fun H => sumTo S (fun j => sm (fun x => indB (E H (j, rv j H x) && decide (ix H (rv j H x) = j)))) from
          funext fun H => hsm S _, hST S _, sumTo_mul]
    _ ≤ _ := Nat.le_trans (sumTo_mono _ each) (Nat.le_of_eq (sumTo_add _ _ _))

/-- **`zkbT_adaptiveF` with coins**: the distinguisher draws `c0 < R`, its
    pick `ix c0`, real pick `r c0` and event `E c0`; summed over the coins,
    the simulator running the distinguisher on coins of its own.  View picks
    (`hcons`) and picks in turn (`seqPick_one`, `seqPick_step`) meet `hfix`
    at each coin. -/
theorem zkbT_adaptiveFR {T X C V : Type} {K S R : Nat} {ST : (T → Nat) → Nat} (hST : Lin ST)
    {sm : (X → Nat) → Nat} (hsm : Lin sm) {SC : (C → Nat) → Nat}
    (rv : Nat → T → X → V) (pg : Nat → T → C → X → T) (sv : Nat → T → C → X → V) (ε : Nat → Nat)
    (h : ∀ j, j < S → ZKBT ST K sm SC (rv j) (pg j) (sv j) (ε j)) (ix : Nat → T → V → Nat)
    (r : Nat → T → X → Nat) (hr : ∀ c0 H x, r c0 H x < S)
    (hfix : ∀ c0 H x j, j < S → (ix c0 H (rv j H x) = j ↔ j = r c0 H x)) (E : Nat → T → Nat × V → Bool) :
    K * sumTo R (fun c0 => ST (fun H => sm (fun x => indB (E c0 H (r c0 H x, rv (r c0 H x) H x))))) ≤
      sumTo R (fun c0 => sumTo S (fun j => ST (fun H => SC (fun c => sm (fun x =>
        indB (E c0 (pg j H c x) (j, sv j H c x) && decide (ix c0 (pg j H c x) (sv j H c x) = j))))))) +
        R * sumTo S ε := by
  rw [sumTo_mul, ← sumTo_const (sumTo S ε) R, ← sumTo_add]
  exact sumTo_mono R (fun c0 _ =>
    zkbT_adaptiveF hST hsm rv pg sv ε h (ix c0) (r c0) (hr c0) (hfix c0) (E c0))

/-- **`zkbT_adaptiveV_mass` with coins**: summed over the coins, the
    confirmed simulations number at most `R` times the real draws plus the
    errors; a pick reading the tables alone ignores `v`. -/
theorem zkbT_adaptiveV_massR {T X C V : Type} {K S R : Nat} {ST : (T → Nat) → Nat} (hST : Lin ST)
    {sm : (X → Nat) → Nat} (hsm : Lin sm) {SC : (C → Nat) → Nat} (hSC : Lin SC)
    (rv : Nat → T → X → V) (pg : Nat → T → C → X → T) (sv : Nat → T → C → X → V) (ε : Nat → Nat)
    (h : ∀ j, j < S → ZKBT ST K sm SC (rv j) (pg j) (sv j) (ε j))
    (hnorm : ST (fun _ => SC (fun _ => sm (fun _ => 1))) = K * ST (fun _ => sm (fun _ => 1)))
    (ix : Nat → T → V → Nat) (hix : ∀ c0 H v, ix c0 H v < S)
    (hcons : ∀ c0 j H x, ix c0 H (rv j H x) = ix c0 H (rv 0 H x)) :
    sumTo R (fun c0 => sumTo S (fun j => ST (fun H => SC (fun c => sm (fun x =>
        indB (decide (ix c0 (pg j H c x) (sv j H c x) = j))))))) ≤
      R * (K * ST (fun _ => sm (fun _ => 1)) + sumTo S ε) := by
  rw [← sumTo_const]
  exact sumTo_mono R (fun c0 _ =>
    zkbT_adaptiveV_mass hST hsm hSC rv pg sv ε h hnorm (ix c0) (hix c0) (hcons c0))

/-- **The sum of the errors is tight**: `S` statements over `S` tables,
    statement `j`'s real view flagging table `j` and its simulation never,
    each meet `ZKBT` with error `1`; the pick `ix H = H % S` then makes the
    real count `S`, while every confirmed simulation counts `0`, so
    `zkbT_adaptive`'s bound `sumTo S ε = S` is met with equality (its
    remaining hypotheses: the pick below `S`, the last conjunct; `ST`,
    `sm` linear sums).  From
    per-statement bounds no single statement's error can replace the
    sum. -/
theorem zkbT_adaptive_tight (S : Nat) (hS : 0 < S) :
    (∀ j, j < S → ZKBT (fun f : Nat → Nat => sumTo S f) 1 (fun f : Unit → Nat => f ()) (fun g : Unit → Nat => g ())
      (fun H _ => decide (H = j)) (fun H _ _ => H) (fun _ _ _ => false) 1) ∧
    1 * sumTo S (fun H => indB ((fun _ (p : Nat × Bool) => p.2) H (H % S, decide (H = H % S)))) = sumTo S (fun _ => 1) ∧
    sumTo S (fun j => sumTo S (fun H => indB ((fun _ (p : Nat × Bool) => p.2) H (j, false) && decide (H % S = j)))) = 0 ∧
    (∀ H, H % S < S) := by
  refine ⟨fun j hj E => ?_, ?_, ?_, fun H => Nat.mod_lt H hS⟩
  · show 1 * sumTo S (fun H => indB (E H (decide (H = j)))) ≤ sumTo S (fun H => indB (E H false)) + 1
    rw [Nat.one_mul]
    have key : ∀ n, sumTo n (fun H => indB (E H (decide (H = j)))) ≤
        sumTo n (fun H => indB (E H false)) + indB (decide (j < n)) := by
      intro n
      induction n with
      | zero => exact Nat.zero_le _
      | succ n ih =>
        show sumTo n _ + indB (E n (decide (n = j))) ≤ sumTo n _ + indB (E n false) + indB (decide (j < n + 1))
        by_cases e : n = j
        · subst e
          have h1 : indB (decide (n < n)) = 0 := by simp [indB]
          rw [h1, Nat.add_zero] at ih
          have h2 : indB (decide (n < n + 1)) = 1 := by simp [indB]
          rw [h2]
          have := indB_le (E n (decide (n = n)))
          omega
        · have h1 : decide (n = j) = false := decide_eq_false e
          rw [h1]
          have h2 : indB (decide (j < n)) ≤ indB (decide (j < n + 1)) := by
            by_cases hj' : j < n
            · simp [indB, hj', Nat.lt_succ_of_lt hj']
            · simp [indB, hj']
          omega
    refine Nat.le_trans (key S) (Nat.add_le_add_left ?_ _)
    exact indB_le _
  · rw [Nat.one_mul]
    refine sumTo_congr _ (fun H hH => ?_)
    show indB (decide (H = H % S)) = 1
    rw [Nat.mod_eq_of_lt hH]; simp [indB]
  · have z : ∀ n, sumTo n (fun _ : Nat => (0 : Nat)) = 0 := fun n => by rw [sumTo_const, Nat.mul_zero]
    rw [← z S]
    refine sumTo_congr _ (fun j _ => ?_)
    rw [← z S]
    refine sumTo_congr _ (fun H _ => ?_)
    rfl

/-- **One shared error for a picked statement**: when every statement's
    real count is at most its simulation away from one bad event (`h`, error
    `0` there), the bad event's mass `β` (`hbad`) is charged once, not once
    per statement as `zkbT_adaptive`'s per-statement errors are. -/
theorem zkbT_adaptive_joint {T X C V : Type} {K S β : Nat} {ST : (T → Nat) → Nat} (hST : Lin ST)
    {sm : (X → Nat) → Nat} (hsm : Lin sm) {SC : (C → Nat) → Nat}
    (rv : Nat → T → X → V) (pg : Nat → T → C → X → T) (sv : Nat → T → C → X → V) (bad : T → X → Bool)
    (h : ∀ j, j < S → ∀ E : T → V → Bool, K * ST (fun H => sm (fun x => indB (E H (rv j H x) && !bad H x))) ≤
      ST (fun H => SC (fun c => sm (fun x => indB (E (pg j H c x) (sv j H c x))))))
    (hbad : K * ST (fun H => sm (fun x => indB (bad H x))) ≤ β)
    (ix : T → Nat) (hix : ∀ H, ix H < S) (E : T → Nat × V → Bool) :
    K * ST (fun H => sm (fun x => indB (E H (ix H, rv (ix H) H x)))) ≤
      sumTo S (fun j => ST (fun H => SC (fun c => sm (fun x =>
        indB (E (pg j H c x) (j, sv j H c x) && decide (ix (pg j H c x) = j)))))) + β := by
  -- off the bad event, the real count splits by the statement picked
  have split : ∀ H x, indB (E H (ix H, rv (ix H) H x) && !bad H x) =
      sumTo S (fun j => indB ((E H (j, rv j H x) && decide (ix H = j)) && !bad H x)) := by
    intro H x
    have key : ∀ n, ix H < n → sumTo n (fun j => indB ((E H (j, rv j H x) && decide (ix H = j)) && !bad H x)) =
        indB (E H (ix H, rv (ix H) H x) && !bad H x) := by
      intro n
      induction n with
      | zero => intro hn; exact absurd hn (Nat.not_lt_zero _)
      | succ n ih =>
        intro hn
        show sumTo n _ + indB ((E H (n, rv n H x) && decide (ix H = n)) && !bad H x) = _
        rcases Nat.lt_or_ge (ix H) n with hl | hl
        · rw [ih hl, decide_eq_false (Nat.ne_of_lt hl), Bool.and_false, Bool.false_and]; rfl
        · have he : ix H = n := Nat.le_antisymm (Nat.le_of_lt_succ hn) hl
          have z : ∀ m, m ≤ n → sumTo m (fun j => indB ((E H (j, rv j H x) && decide (ix H = j)) && !bad H x)) = 0 := by
            intro m
            induction m with
            | zero => intro _; rfl
            | succ m ihm =>
              intro hm
              have hne : ix H ≠ m := by rw [he]; exact Nat.ne_of_gt hm
              show sumTo m _ + indB ((E H (m, rv m H x) && decide (ix H = m)) && !bad H x) = 0
              rw [ihm (Nat.le_of_succ_le hm), decide_eq_false hne, Bool.and_false, Bool.false_and]; rfl
          rw [z n (Nat.le_refl n), Nat.zero_add, he, decide_eq_true rfl, Bool.and_true]
    exact (key S (hix H)).symm
  have pt : ∀ H x, indB (E H (ix H, rv (ix H) H x)) ≤ indB (E H (ix H, rv (ix H) H x) && !bad H x) + indB (bad H x) :=
    fun H x => by cases E H (ix H, rv (ix H) H x) <;> cases bad H x <;> decide
  have each : ∀ j, j < S → K * ST (fun H => sm (fun x => indB ((E H (j, rv j H x) && decide (ix H = j)) && !bad H x))) ≤
      ST (fun H => SC (fun c => sm (fun x =>
        indB (E (pg j H c x) (j, sv j H c x) && decide (ix (pg j H c x) = j))))) :=
    fun j hj => h j hj (fun H v => E H (j, v) && decide (ix H = j))
  calc K * ST (fun H => sm (fun x => indB (E H (ix H, rv (ix H) H x))))
      ≤ K * ST (fun H => sm (fun x => indB (E H (ix H, rv (ix H) H x) && !bad H x) + indB (bad H x))) :=
        Nat.mul_le_mul_left _ (sm_mono ST hST (fun H => sm_mono sm hsm (fun x => pt H x)))
    _ = K * ST (fun H => sm (fun x => sumTo S (fun j => indB ((E H (j, rv j H x) && decide (ix H = j)) && !bad H x)))) +
        K * ST (fun H => sm (fun x => indB (bad H x))) := by
        rw [← Nat.mul_add]; congr 1
        rw [← sm_add ST hST]; congr 1; funext H
        rw [← sm_add sm hsm]; congr 1; funext x
        rw [split]
    _ = sumTo S (fun j => K * ST (fun H => sm (fun x => indB ((E H (j, rv j H x) && decide (ix H = j)) && !bad H x)))) +
        K * ST (fun H => sm (fun x => indB (bad H x))) := by
        congr 1
        rw [show (fun H => sm (fun x => sumTo S (fun j => indB ((E H (j, rv j H x) && decide (ix H = j)) && !bad H x)))) =
            fun H => sumTo S (fun j => sm (fun x => indB ((E H (j, rv j H x) && decide (ix H = j)) && !bad H x))) from
          funext fun H => hsm S _, hST S _, sumTo_mul]
    _ ≤ _ := Nat.add_le_add (sumTo_mono _ each) hbad

/-- **Two statements picked in turn** meet `zkbT_adaptiveF`'s `hfix`: the
    statements indexed `j1 + S1 j2`, the first pick read from the view every
    statement shares (`hc1`), the second from the view the first pick's
    index determines (`hc2`, reading `rv (j % S1)`). -/
theorem seqPick_fix {T X V : Type} {S1 S2 : Nat} (rv : Nat → T → X → V) (ix1 ix2 : T → V → Nat)
    (h1 : ∀ H v, ix1 H v < S1) (h2 : ∀ H v, ix2 H v < S2)
    (hc1 : ∀ j H x, ix1 H (rv j H x) = ix1 H (rv 0 H x)) (hc2 : ∀ j H x, ix2 H (rv j H x) = ix2 H (rv (j % S1) H x)) :
    (∀ H x, ix1 H (rv 0 H x) + S1 * ix2 H (rv (ix1 H (rv 0 H x)) H x) < S1 * S2) ∧
    ∀ H x j, j < S1 * S2 → (ix1 H (rv j H x) + S1 * ix2 H (rv j H x) = j ↔
      j = ix1 H (rv 0 H x) + S1 * ix2 H (rv (ix1 H (rv 0 H x)) H x)) := by
  have hmod : ∀ a b, a < S1 → (a + S1 * b) % S1 = a := fun a b ha => by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha]
  refine ⟨fun H x => ?_, fun H x j _ => ?_⟩
  · have ha := h1 H (rv 0 H x)
    have hb := h2 H (rv (ix1 H (rv 0 H x)) H x)
    calc ix1 H (rv 0 H x) + S1 * ix2 H (rv (ix1 H (rv 0 H x)) H x)
        < S1 + S1 * ix2 H (rv (ix1 H (rv 0 H x)) H x) := Nat.add_lt_add_right ha _
      _ = S1 * (ix2 H (rv (ix1 H (rv 0 H x)) H x) + 1) := by rw [Nat.mul_succ, Nat.add_comm]
      _ ≤ S1 * S2 := Nat.mul_le_mul_left _ hb
  · rw [hc1 j H x, hc2 j H x]
    have ha := h1 H (rv 0 H x)
    constructor
    · intro e
      have hj : j % S1 = ix1 H (rv 0 H x) := by rw [← e, hmod _ _ ha]
      rw [hj] at e
      exact e.symm
    · intro e
      have hj : j % S1 = ix1 H (rv 0 H x) := by rw [e, hmod _ _ ha]
      rw [hj, ← e]

theorem digits_eq {S a b c d : Nat} (ha : a < S) (hc : c < S) (e : a + S * b = c + S * d) : a = c ∧ b = d := by
  have hS : 0 < S := Nat.lt_of_le_of_lt (Nat.zero_le _) ha
  have e1 := congrArg (· % S) e
  simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hc] at e1
  have e2 := congrArg (· / S) e
  simp only [Nat.add_mul_div_left _ _ hS, Nat.div_eq_of_lt ha, Nat.div_eq_of_lt hc, Nat.zero_add] at e2
  exact ⟨e1, e2⟩

/-- **One more pick in turn**: a stage of picks `ixA` over `SA` statements
    meeting the fixed-point condition (`hfixA`, real pick `rA`) and reading
    its views only through `j % SA` (`hcA`), followed by a pick `ix2 < S2`
    read from the view the stage determines (`hc2`), is again such a stage
    over `SA S2` statements (`j % SA + SA (j / SA)`).  From one pick reading
    the shared view (`seqPick_one`), `k` picks in turn by `k - 1` steps. -/
theorem seqPick_step {T X V : Type} {SA S2 : Nat} (rv : Nat → T → X → V) (ixA ix2 : T → V → Nat) (rA : T → X → Nat)
    (hA : ∀ H v, ixA H v < SA) (h2 : ∀ H v, ix2 H v < S2) (hrA : ∀ H x, rA H x < SA)
    (hfixA : ∀ H x j, j < SA → (ixA H (rv j H x) = j ↔ j = rA H x))
    (hcA : ∀ j H x, ixA H (rv j H x) = ixA H (rv (j % SA) H x))
    (hc2 : ∀ j H x, ix2 H (rv j H x) = ix2 H (rv (j % SA) H x)) :
    (∀ H x, rA H x + SA * ix2 H (rv (rA H x) H x) < SA * S2) ∧
    (∀ H x j, j < SA * S2 → (ixA H (rv j H x) + SA * ix2 H (rv j H x) = j ↔
      j = rA H x + SA * ix2 H (rv (rA H x) H x))) ∧
    (∀ j H x, ixA H (rv j H x) + SA * ix2 H (rv j H x) =
      ixA H (rv (j % (SA * S2)) H x) + SA * ix2 H (rv (j % (SA * S2)) H x)) ∧
    (∀ H v, ixA H v + SA * ix2 H v < SA * S2) := by
  refine ⟨fun H x => ?_, fun H x j _ => ?_, fun j H x => ?_, fun H v => ?_⟩
  · calc rA H x + SA * ix2 H (rv (rA H x) H x) < SA + SA * ix2 H (rv (rA H x) H x) := Nat.add_lt_add_right (hrA H x) _
      _ = SA * (ix2 H (rv (rA H x) H x) + 1) := by rw [Nat.mul_succ, Nat.add_comm]
      _ ≤ SA * S2 := Nat.mul_le_mul_left _ (h2 _ _)
  · have hS : 0 < SA := Nat.lt_of_le_of_lt (Nat.zero_le _) (hrA H x)
    have ja : j % SA < SA := Nat.mod_lt _ hS
    have jd : j = j % SA + SA * (j / SA) := (Nat.mod_add_div j SA).symm
    rw [hcA j H x, hc2 j H x]
    constructor
    · intro e
      have e' : ixA H (rv (j % SA) H x) + SA * ix2 H (rv (j % SA) H x) = j % SA + SA * (j / SA) := e.trans jd
      obtain ⟨d1, d2⟩ := digits_eq (hA H _) ja e'
      have hra : j % SA = rA H x := (hfixA H x (j % SA) ja).1 d1
      calc j = j % SA + SA * (j / SA) := jd
        _ = rA H x + SA * ix2 H (rv (rA H x) H x) := by rw [← d2, hra]
    · intro e
      have hjm : j % SA = rA H x := by rw [e, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (hrA H x)]
      have hfa : ixA H (rv (j % SA) H x) = j % SA := (hfixA H x (j % SA) ja).2 hjm
      rw [hfa, hjm]
      exact e.symm
  · have hm : j % (SA * S2) % SA = j % SA := Nat.mod_mul_right_mod j SA S2
    rw [hcA j H x, hc2 j H x, hcA (j % (SA * S2)) H x, hc2 (j % (SA * S2)) H x, hm]
  · calc ixA H v + SA * ix2 H v < SA + SA * ix2 H v := Nat.add_lt_add_right (hA H v) _
      _ = SA * (ix2 H v + 1) := by rw [Nat.mul_succ, Nat.add_comm]
      _ ≤ SA * S2 := Nat.mul_le_mul_left _ (h2 H v)

/-- One pick reading the view every statement shares starts the stages. -/
theorem seqPick_one {T X V : Type} {S1 : Nat} (rv : Nat → T → X → V) (ix1 : T → V → Nat)
    (hc1 : ∀ j H x, ix1 H (rv j H x) = ix1 H (rv 0 H x)) :
    (∀ H x j, j < S1 → (ix1 H (rv j H x) = j ↔ j = ix1 H (rv 0 H x))) ∧
    (∀ j H x, ix1 H (rv j H x) = ix1 H (rv (j % S1) H x)) :=
  ⟨fun H x j _ => by rw [hc1 j H x]; exact ⟨fun e => e.symm, fun e => e.symm⟩,
   fun j H x => by rw [hc1 j H x, hc1 (j % S1) H x]⟩

end Circuit
