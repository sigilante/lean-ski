import Ski.Stratum2
import Ski.BridgeA
open Term

/-!
# Stratum 2 on the compiled trace: no elementary bound

`Ski/Stratum2.lean` proves that call-by-name evaluation of the family
`evalT k` takes at least `2↑↑(k+1)` steps.  This file proves the same bound
for the compiled term, under both compilations, the threaded one being the
term the prover runs.

**The lower bound** (`compiled_evalT_lower`, `compiledA_evalT_lower`):
every normal-order (head) reduction of the compiled `evalT k`, the tower
applied to the toggle and `true`, to a weak head
normal form takes at least `2↑↑(k+1)` steps.  The proof transfers the
source relation `LB` to `SKI` terms (`LBS`).  At `Bool`, `LBS u m` says
that every reduction of `u` to a weak head normal form takes at least `m`
steps.  It is closed under backward steps, because normal order is
deterministic (`Step.det`).  Two facts about head reduction carry the rest:
- an application reaches a normal form only after its head does
  (`head_first`), so a case costs at least its scrutinee (`LBS_case`);
- the compiled toggle takes a step before its case (`LBS_togC`).

The compiled `two` reduces `two h u` to `h (I h u)` in five head steps, and
`I h u` to `h u` in one (`LBS_twoC`).  So the compiled tower's descriptor is
the source's (`LBS_towerC`).

**The bound is not vacuous** (`compiled_evalT_converges`,
`compiledA_evalT_converges`): the compiled term converges when the Boolean
witness does, by `compiled_converges`.

**No elementary bound** (`compiled_no_elementary_bound`, and
`compiledA_no_elementary_bound` stated on the threaded compilation): the
compiled term has `6k + 39` combinators plus the Boolean witness's.  For
every height `j` of exponentials and every constant `c`, some member's
compiled term takes more than `exp_j (c · leaves)` steps.
-/

theorem Whnf.app_fun {u a : Term} (h : Whnf (u ⬝ a)) : Whnf u := by
  cases h with
  | S1 _ => exact .S
  | S2 x _ => exact .S1 x
  | K1 _ => exact .K

namespace Rz

open Tm

-- ---------------------------------------------------------------------------
-- The lower-bound relation on SKI terms
-- ---------------------------------------------------------------------------

/-- `LBS A u d`: `u` behaves at `A` at least as slowly as `d`.  At `Bool`,
    every reduction to a weak head normal form takes at least `d` steps. -/
def LBS : (A : BT) → Term → Desc A → Prop
  | .bool, u, m => ∀ n v, StepsN n u v → Whnf v → m ≤ n
  | .arr A B, F, E => ∀ u d, LBS A u d → LBS B (F ⬝ u) (E d)

/-- **Backward closure.** -/
theorem LBS.back : ∀ (A : BT) {t t' : Term} {d : Desc A}, Step t t' → LBS A t' d → LBS A t d
  | .bool, _, _, _, s, h => by
    intro n v hn hv
    cases hn with
    | refl => exact (hv.no_step s).elim
    | step s1 rest =>
      rw [Step.det s1 s] at rest
      exact Nat.le_succ_of_le (h _ v rest hv)
  | .arr _ B, _, _, _, s, h => fun u d hu => LBS.back B (.left u s) (h u d hu)

/-- At `Bool`, a step before a slow term adds one. -/
theorem LBS.back_succ {t t' : Term} {m : Nat} (s : Step t t') (h : LBS .bool t' m) :
    LBS .bool t (m + 1) := by
  intro n v hn hv
  cases hn with
  | refl => exact (hv.no_step s).elim
  | step s1 rest =>
    rw [Step.det s1 s] at rest
    exact Nat.succ_le_succ (h _ v rest hv)

/-- **The head first**: an application reaches a weak head normal form only
    after its head does, within as many steps. -/
theorem head_first : ∀ {n : Nat} {u a v : Term}, StepsN n (u ⬝ a) v → Whnf v →
    ∃ n₁ u', n₁ ≤ n ∧ StepsN n₁ u u' ∧ Whnf u'
  | 0, u, _, _, h, hv => by
    cases h
    exact ⟨0, u, Nat.le_refl 0, .refl u, hv.app_fun⟩
  | n + 1, u, a, _, h, hv => by
    cases progress u with
    | inl hw => exact ⟨0, u, Nat.zero_le _, .refl u, hw⟩
    | inr hs =>
      cases hs with
      | intro u' s =>
        cases h with
        | step s1 rest =>
          rw [Step.det s1 (.left a s)] at rest
          cases head_first rest hv with
          | intro n₁ h' => cases h' with
            | intro u'' h' => exact ⟨n₁ + 1, u'', Nat.succ_le_succ h'.1, .step s h'.2.1, h'.2.2⟩

/-- A case costs at least its scrutinee. -/
theorem LBS_case {u F G : Term} {m : Nat} (h : LBS .bool u m) : LBS .bool (u ⬝ F ⬝ G) m := by
  intro n v hn hv
  cases head_first hn hv with
  | intro n₁ h1 => cases h1 with
    | intro w h1 =>
      cases head_first h1.2.1 h1.2.2 with
      | intro n₂ h2 => cases h2 with
        | intro w' h2 => exact Nat.le_trans (h n₂ w' h2.2.1 h2.2.2) (Nat.le_trans h2.1 h1.1)

-- ---------------------------------------------------------------------------
-- The compiled toggle and two
-- ---------------------------------------------------------------------------

/-- The compiled branch `λ a. inr a`. -/
def togF : Term := S ⬝ (K ⬝ K) ⬝ (S ⬝ (K ⬝ (S ⬝ I)) ⬝ K)

/-- The compiled branch `λ a. inl a`. -/
def togG : Term := S ⬝ (K ⬝ (S ⬝ (K ⬝ K))) ⬝ (S ⬝ (K ⬝ (S ⬝ I)) ⬝ K)

/-- The compiled toggle. -/
def togC : Term := S ⬝ (S ⬝ I ⬝ (K ⬝ togF)) ⬝ (K ⬝ togG)

/-- The compiled `two`. -/
def twoC : Term := S ⬝ (S ⬝ (K ⬝ S) ⬝ K) ⬝ I

theorem compiled_togT (ι : Unit → Term) : compiled ι (togT : Tm Unit) = togC := rfl
-- The threaded case computes `sharedS` by filtering `downFrom`; the elaborator's
-- `rfl` check unfolds it slowly, so the default heartbeat budget is too small.
set_option maxHeartbeats 2000000 in
theorem compiledA_togT (ι : Unit → Term) : compiledA ι (togT : Tm Unit) = togC := rfl
theorem compiled_twoT (ι : Unit → Term) : compiled ι (twoT : Tm Unit) = twoC := rfl
theorem compiledA_twoT (ι : Unit → Term) : compiledA ι (twoT : Tm Unit) = twoC := rfl

/-- Each use of the compiled toggle takes a step, then a case. -/
theorem LBS_togC : LBS (.arr .bool .bool) togC (fun m => m + 1) := by
  intro u m hu
  have s1 : Step (togC ⬝ u) (S ⬝ I ⬝ (K ⬝ togF) ⬝ u ⬝ (K ⬝ togG ⬝ u)) := .S _ _ u
  have s2 : Step (S ⬝ I ⬝ (K ⬝ togF) ⬝ u ⬝ (K ⬝ togG ⬝ u))
      (I ⬝ u ⬝ (K ⬝ togF ⬝ u) ⬝ (K ⬝ togG ⬝ u)) := .left _ (.S _ _ u)
  have s3 : Step (I ⬝ u ⬝ (K ⬝ togF ⬝ u) ⬝ (K ⬝ togG ⬝ u))
      (u ⬝ (K ⬝ togF ⬝ u) ⬝ (K ⬝ togG ⬝ u)) := .left _ (.left _ (.I u))
  exact LBS.back_succ s1 (LBS.back .bool s2 (LBS.back .bool s3 (LBS_case hu)))

/-- The compiled `two` composes its argument's descriptor with itself. -/
theorem LBS_twoC (A : BT) : LBS (.arr (.arr A A) (.arr A A)) twoC (fun f d => f (f d)) := by
  intro h f hh u d hu
  -- `two h u ⟶ S (K S) K h (I h) u ⟶ K S h (K h) (I h) u ⟶ S (K h) (I h) u
  --   ⟶ K h u (I h u) ⟶ h (I h u)`, and `I h u ⟶ h u`
  have s1 : Step (twoC ⬝ h ⬝ u) (S ⬝ (K ⬝ S) ⬝ K ⬝ h ⬝ (I ⬝ h) ⬝ u) := .left u (.S _ _ h)
  have s2 : Step (S ⬝ (K ⬝ S) ⬝ K ⬝ h ⬝ (I ⬝ h) ⬝ u) (K ⬝ S ⬝ h ⬝ (K ⬝ h) ⬝ (I ⬝ h) ⬝ u) :=
    .left u (.left _ (.S _ _ h))
  have s3 : Step (K ⬝ S ⬝ h ⬝ (K ⬝ h) ⬝ (I ⬝ h) ⬝ u) (S ⬝ (K ⬝ h) ⬝ (I ⬝ h) ⬝ u) :=
    .left u (.left _ (.left _ (.K S h)))
  have s4 : Step (S ⬝ (K ⬝ h) ⬝ (I ⬝ h) ⬝ u) (K ⬝ h ⬝ u ⬝ (I ⬝ h ⬝ u)) := .S _ _ u
  have s5 : Step (K ⬝ h ⬝ u ⬝ (I ⬝ h ⬝ u)) (h ⬝ (I ⬝ h ⬝ u)) := .left _ (.K h u)
  have hin : LBS A (I ⬝ h ⬝ u) (f d) := LBS.back A (.left u (.I h)) (hh u d hu)
  exact LBS.back A s1 (LBS.back A s2 (LBS.back A s3 (LBS.back A s4 (LBS.back A s5
    (hh _ _ hin)))))

-- ---------------------------------------------------------------------------
-- The compiled tower
-- ---------------------------------------------------------------------------

/-- `twoC twoC ⋯ twoC`, `k + 1` copies, associated to the left. -/
def towerC : Nat → Term
  | 0 => twoC
  | k + 1 => towerC k ⬝ twoC

theorem compiled_towerT (ι : Unit → Term) : ∀ k, compiled ι (towerT k : Tm Unit) = towerC k
  | 0 => compiled_twoT ι
  | k + 1 => by
    show compiled ι (towerT k : Tm Unit) ⬝ compiled ι (twoT : Tm Unit) = towerC k ⬝ twoC
    rw [compiled_towerT ι k, compiled_twoT]

theorem compiledA_towerT (ι : Unit → Term) : ∀ k, compiledA ι (towerT k : Tm Unit) = towerC k
  | 0 => compiledA_twoT ι
  | k + 1 => by
    show compiledA ι (towerT k : Tm Unit) ⬝ compiledA ι (twoT : Tm Unit) = towerC k ⬝ twoC
    rw [compiledA_towerT ι k, compiledA_twoT]

/-- The compiled `evalT k trueT`. -/
def evalC (ι : Unit → Term) (k : Nat) : Term := towerC k ⬝ togC ⬝ (inlG ⬝ ι ())

theorem compiled_trueT (ι : Unit → Term) : compiled ι trueT = inlG ⬝ ι () := by
  show inlG.toO.close _ ⬝ (ι ()).toO.close _ = _
  rw [close_toO, close_toO]

theorem compiledA_trueT (ι : Unit → Term) : compiledA ι trueT = inlG ⬝ ι () := by
  show inlG.toO.close _ ⬝ (ι ()).toO.close _ = _
  rw [close_toO, close_toO]

theorem compiled_evalT (ι : Unit → Term) (k : Nat) : compiled ι (evalT k trueT) = evalC ι k := by
  show compiled ι (towerT k : Tm Unit) ⬝ compiled ι (togT : Tm Unit) ⬝ compiled ι trueT = _
  rw [compiled_towerT, compiled_togT, compiled_trueT]
  rfl

theorem compiledA_evalT (ι : Unit → Term) (k : Nat) : compiledA ι (evalT k trueT) = evalC ι k := by
  show compiledA ι (towerT k : Tm Unit) ⬝ compiledA ι (togT : Tm Unit) ⬝ compiledA ι trueT = _
  rw [compiledA_towerT, compiledA_togT, compiledA_trueT]
  rfl

/-- **The compiled tower's descriptor** is the `2↑↑(k+1)`-fold iterate. -/
theorem LBS_towerC : ∀ (k : Nat) (A : BT), LBS (NT A) (towerC k) (fun f => iterN f (tw (k + 1)))
  | 0, A => by
    have e : (fun (f : Desc (.arr A A)) => iterN f (tw 1)) = fun f d => f (f d) := by
      funext f d; rfl
    show LBS (NT A) twoC (fun f => iterN f (tw 1))
    rw [e]
    exact LBS_twoC A
  | k + 1, A => by
    have ih := LBS_towerC k (.arr A A)
    have h := ih twoC (fun f d => f (f d)) (LBS_twoC A)
    have e : (fun (f : Desc (.arr A A)) => iterN f (tw (k + 2))) =
        iterN (fun (g : Desc (.arr A A)) (x : Desc A) => g (g x)) (tw (k + 1)) := by
      funext f d
      rw [iterN_sq]
      rfl
    show LBS (NT A) (towerC k ⬝ twoC) _
    rw [e]
    exact h

/-- **The compiled lower bound**: every normal-order reduction of the
    compiled `evalT k trueT` to a weak head normal form takes at least
    `2↑↑(k+1)` steps. -/
theorem evalC_lower (ι : Unit → Term) (k : Nat) {n : Nat} {v : Term}
    (h : StepsN n (evalC ι k) v) (hv : Whnf v) : tw (k + 1) ≤ n := by
  have hb : LBS .bool (inlG ⬝ ι ()) 0 := fun _ _ _ _ => Nat.zero_le _
  have := LBS_towerC k .bool togC (fun m => m + 1) LBS_togC (inlG ⬝ ι ()) 0 hb n v h hv
  dsimp only at this
  rw [iterN_succ_zero] at this
  exact this

theorem compiled_evalT_lower (ι : Unit → Term) (k : Nat) {n : Nat} {v : Term}
    (h : StepsN n (compiled ι (evalT k trueT)) v) (hv : Whnf v) : tw (k + 1) ≤ n := by
  rw [compiled_evalT] at h
  exact evalC_lower ι k h hv

/-- **The lower bound, threaded**: the same for the compilation the prover
    runs. -/
theorem compiledA_evalT_lower (ι : Unit → Term) (k : Nat) {n : Nat} {v : Term}
    (h : StepsN n (compiledA ι (evalT k trueT)) v) (hv : Whnf v) : tw (k + 1) ≤ n := by
  rw [compiledA_evalT] at h
  exact evalC_lower ι k h hv

/-- **The compiled family converges**, when the Boolean witness does, so the
    bound is not vacuous. -/
theorem evalC_converges (ι : Unit → Term) (hι : Converges (ι ())) (k : Nat) :
    ∃ n v, StepsN n (evalC ι k) v ∧ Whnf v := by
  have hc := compiled_converges (sig := sigU) ι (evalT_typed (fun _ => boolTy) k)
    (fun _ => hι) (closedAt_evalT k)
  rw [compiled_evalT] at hc
  cases hc with
  | intro v hv =>
    cases hv.1.counted with
    | intro n hn => exact ⟨n, v, hn, hv.2⟩

theorem leaves_towerC : ∀ k : Nat, (towerC k).leaves = 6 * k + 6
  | 0 => rfl
  | k + 1 => by
    show (towerC k).leaves + 6 = 6 * (k + 1) + 6
    rw [leaves_towerC k]
    omega

theorem leaves_evalC (ι : Unit → Term) (k : Nat) :
    (evalC ι k).leaves = 6 * k + 39 + (ι ()).leaves := by
  show (towerC k).leaves + 23 + (10 + (ι ()).leaves) = _
  rw [leaves_towerC]
  omega

/-- **No elementary bound on the compiled trace.**  For every height `j` of
    exponentials and every constant `c`, some member of the compiled family
    converges, and every normal-order reduction of it to a weak head normal
    form takes more than `expT j (c · leaves)` steps. -/
theorem compiled_no_elementary_bound (ι : Unit → Term) (hι : Converges (ι ())) (j c : Nat) :
    ∃ k, (∃ n v, StepsN n (evalC ι k) v ∧ Whnf v) ∧
      ∀ n v, StepsN n (evalC ι k) v → Whnf v → expT j (c * (evalC ι k).leaves) < n := by
  cases tw_beats_linear (c * 6) (c * (6 * j + 39 + (ι ()).leaves)) with
  | intro m hm =>
    refine ⟨m + j - 1, evalC_converges ι hι _, fun n v hn hv => ?_⟩
    have hlow := evalC_lower ι (m + j - 1) hn hv
    rw [show m + j - 1 + 1 = m + j by omega, tw_add] at hlow
    rw [leaves_evalC]
    have hsz : c * (6 * (m + j - 1) + 39 + (ι ()).leaves) ≤
        c * 6 * m + c * (6 * j + 39 + (ι ()).leaves) := by
      have h1 : 6 * (m + j - 1) + 39 + (ι ()).leaves ≤ 6 * m + (6 * j + 39 + (ι ()).leaves) := by
        omega
      have h2 := Nat.mul_le_mul_left c h1
      have h3 : c * (6 * m + (6 * j + 39 + (ι ()).leaves)) =
          c * 6 * m + c * (6 * j + 39 + (ι ()).leaves) := by
        rw [Nat.mul_add, Nat.mul_assoc]
      exact Nat.le_trans h2 (Nat.le_of_eq h3)
    exact Nat.lt_of_lt_of_le (expT_lt j (Nat.lt_of_le_of_lt hsz hm.2)) hlow

theorem compiled_evalT_converges (ι : Unit → Term) (hι : Converges (ι ())) (k : Nat) :
    Converges (compiled ι (evalT k trueT)) := by
  rw [compiled_evalT]
  cases evalC_converges ι hι k with
  | intro n h => cases h with
    | intro v h => exact ⟨v, h.1.steps, h.2⟩

theorem compiledA_evalT_converges (ι : Unit → Term) (hι : Converges (ι ())) (k : Nat) :
    Converges (compiledA ι (evalT k trueT)) := by
  rw [compiledA_evalT]
  cases evalC_converges ι hι k with
  | intro n h => cases h with
    | intro v h => exact ⟨v, h.1.steps, h.2⟩

/-- **No elementary bound on the trace the prover runs**: the same, stated on
    the threaded compilation of `evalT k trueT`. -/
theorem compiledA_no_elementary_bound (ι : Unit → Term) (hι : Converges (ι ())) (j c : Nat) :
    ∃ k, Converges (compiledA ι (evalT k trueT)) ∧
      ∀ n v, StepsN n (compiledA ι (evalT k trueT)) v → Whnf v →
        expT j (c * (compiledA ι (evalT k trueT)).leaves) < n := by
  cases compiled_no_elementary_bound ι hι j c with
  | intro k h =>
    refine ⟨k, compiledA_evalT_converges ι hι k, fun n v hn hv => ?_⟩
    rw [compiledA_evalT] at hn ⊢
    exact h.2 n v hn hv

end Rz
