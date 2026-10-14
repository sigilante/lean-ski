import Ski.ZK.SpongeOOD

/-!
# Squeezes inside a duplex run

Plonky3's challenger is a duplex: after a squeeze the chain continues from
the squeezed state, so the first three challenges are not the run's last
uses of the permutation, and `zk_squeezeN` does not apply to them.  Here a
run of adaptive forward queries squeezes at `m` times `times j`, and the
table is programmed at the squeezes with uniform states, one squeeze at a
time from the last (`squeeze_seq`): each later position is recomputed on
the table already programmed at the earlier squeezes, as the duplex
continues from the programmed state (`progSeqN`).  `F` sees the final
table only.

- **The cost.** Each squeeze costs the exchanges that change the run up to
  it (`squeeze_swap`), counted on the original table (`badSeq`), so the
  error is `Σ_j B_j / (K · #permutations)` (`badSeq_eq`), each `B_j`
  bounded by `squeeze_bad_run` and `revisit_countP` at `times j`
  (`badAt_bound`, `badAt_bound08`).
- **The reverse.** The programmed world is no likelier than `K` times the
  real one, up to `badAt` (`squeeze_swap_rev`, the exchanges counted by the same `badAt` through
  `vswap_comm`), also when the event reads the states, the real side then
  reading the table's own squeezed answers (`squeeze_seq_rev`, the squeeze
  times increasing).
- **Readback.** The run on the programmed table answers state `j` at
  squeeze `j` for every `j`, except on at most `badSeq` pairs
  (`readback_seq`): the event holds on every real table.  The states'
  collisions fall in `badAt`'s count of exchanges touching the run.
- **A bound transferred.** A bound whose real view reads `m` independent
  uniform challenge states, every distinguisher reading the permutation,
  gives the bound with the challenges read from one duplex run's squeezed
  answers, the run absorbing the transcript and continuing from each
  squeezed state, at twice `badSeq` (`zk_duplex`); the simulated
  distinguisher sees the permutation programmed with the simulated states
  at the squeezes in order.  The real view reads the permutation only
  through the challenges, and the distinguisher must rebuild the
  programming from the view along the runs it visits (`hprog`).
  `zk_duplex_sat08` meets every hypothesis at 0.8's duplex in a degenerate
  instance (no tables, no programming).
- **The rebuild dischargeable.** `zk_duplexC` asks instead that the view's
  run function agree with the real one on the answer lists showing the
  drawn states at the squeezes they reach (`hcons`), as a view carrying the
  actual transcript does: the two then program the same table while every
  stage reads the states back (`progSeqN_agree`), and the stages' failures
  cost `Σ_{j<m} K^(m-j) badSeq j` more (`stage_count`).

Not shown: a composite's first three challenges in `zk_duplex`'s form.  The
composites read `H1`–`H3` at transcript prefixes from tables shared by the
interleaved proofs; for one proof those entries are independent uniform
challenges, but each is a slice of a squeezed state (0.8 pops several
challenges from one state) and the composite's challenge spaces are not
full states.
-/

set_option autoImplicit false

namespace Circuit
open ZKF

/-- The run's position at time `t`. -/
def posAt (K : Nat) (nxt : List Nat → Nat) (t Q : Nat) : Nat := nxt ((runAdp K nxt Q t).map Prod.snd)

/-- The table with its answer at the time-`t` position exchanged for `w`. -/
def swAt (K : Nat) (nxt : List Nat → Nat) (t w Q : Nat) : Nat := vswap K (rget K (posAt K nxt t Q) Q) w Q

/-- The table programmed at the first `m` squeezes in order, squeeze `j`
    at time `times j` with the state `rget K j W`, each position computed on
    the table programmed so far. -/
def progSeqN (K : Nat) (nxt : List Nat → Nat) (times : Nat → Nat) : Nat → Nat → Nat → Nat
  | 0, _, Q => Q
  | m + 1, W, Q => swAt K nxt (times m) (rget K m W) (progSeqN K nxt times m W Q)

theorem progSeqN_congr (K : Nat) (nxt : List Nat → Nat) (times : Nat → Nat) (Q : Nat) :
    ∀ m (W W' : Nat), (∀ j, j < m → rget K j W = rget K j W') → progSeqN K nxt times m W Q = progSeqN K nxt times m W' Q
  | 0, _, _, _ => rfl
  | m + 1, W, W', h => by
    show swAt K nxt (times m) (rget K m W) (progSeqN K nxt times m W Q) =
      swAt K nxt (times m) (rget K m W') (progSeqN K nxt times m W' Q)
    rw [h m (Nat.lt_succ_self m), progSeqN_congr K nxt times Q m W W' (fun j hj => h j (Nat.lt_succ_of_lt hj))]

/-- The exchanges at the squeeze at time `t` that change the run up to it. -/
def badAt (K : Nat) (nxt : List Nat → Nat) (t : Nat) : Nat :=
  sumTo (K ^ K) (fun H => sumTo K (fun u =>
    indB (permB K H && !decide (runAdp K nxt (vswap K u (rget K (posAt K nxt t H) H) H) t = runAdp K nxt H t))))

/-- The error of `m` squeezes, as the induction accrues it. -/
def badSeq (K : Nat) (nxt : List Nat → Nat) (times : Nat → Nat) : Nat → Nat
  | 0 => 0
  | m + 1 => K * badSeq K nxt times m + K ^ m * badAt K nxt (times m)

theorem badSeq_eq (K : Nat) (nxt : List Nat → Nat) (times : Nat → Nat) :
    ∀ m, K * badSeq K nxt times m = K ^ m * sumTo m (fun j => badAt K nxt (times j))
  | 0 => by show K * 0 = 1 * 0; rw [Nat.mul_zero, Nat.mul_zero]
  | m + 1 => by
    show K * (K * badSeq K nxt times m + K ^ m * badAt K nxt (times m)) =
      K ^ (m + 1) * (sumTo m (fun j => badAt K nxt (times j)) + badAt K nxt (times m))
    rw [Nat.mul_add, badSeq_eq K nxt times m, Nat.mul_add, Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_comm K (K ^ m),
      Nat.mul_assoc (K ^ m) K, Nat.mul_assoc (K ^ m) K, Nat.mul_left_comm K (K ^ m)]

theorem rget_add_high {K j m W w : Nat} (hK : 0 < K) (hj : j < m) :
    rget K j (W + K ^ m * w) = rget K j W := by
  unfold rget
  have e : K ^ m = K ^ j * (K * K ^ (m - j - 1)) := by
    rw [← Nat.pow_succ', ← Nat.pow_add]; congr 1; omega
  rw [e, Nat.mul_assoc, Nat.add_mul_div_left _ _ (Nat.pow_pos hK), Nat.mul_assoc, Nat.add_mul_mod_self_left]

theorem rget_add_top {K m W w : Nat} (hW : W < K ^ m) (hw : w < K) : rget K m (W + K ^ m * w) = w := by
  unfold rget
  have hp : 0 < K ^ m := Nat.lt_of_le_of_lt (Nat.zero_le _) hW
  rw [Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt hW, Nat.zero_add, Nat.mod_eq_of_lt hw]

/-- **Squeezes inside a duplex run traded for independent states, the last
    first.**  `K^m` times the permutation tables where `F` holds is at most
    the pairs `(W, P)` where `F` holds at `P` programmed at the `m` squeezes
    with `W`'s states, each position on the table programmed so far, plus
    `badSeq`. -/
theorem squeeze_seq {K : Nat} (hK : 0 < K) (nxt : List Nat → Nat) (hnx : ∀ l, nxt l < K) (times : Nat → Nat) :
    ∀ (m : Nat) (F : Nat → Bool),
      K ^ m * sumTo (K ^ K) (fun P => indB (permB K P && F P)) ≤
        sumTo (K ^ m) (fun W => sumTo (K ^ K) (fun P => indB (permB K P && F (progSeqN K nxt times m W P)))) +
        badSeq K nxt times m
  | 0, F => by
    show 1 * _ ≤ sumTo 1 _ + 0
    rw [Nat.one_mul, Nat.add_zero]
    show _ ≤ 0 + _
    rw [Nat.zero_add]; exact Nat.le_refl _
  | m + 1, F => by
    -- the last squeeze
    have h1 := squeeze_swap hK (fun H => runAdp K nxt H (times m)) (fun c => nxt (c.map Prod.snd)) (fun _ => hnx _)
      (fun _ Q _ => F Q)
    -- the earlier ones, for each state at the last
    have ih := fun w => squeeze_seq hK nxt hnx times m (fun Q => F (swAt K nxt (times m) w Q))
    calc K ^ (m + 1) * sumTo (K ^ K) (fun P => indB (permB K P && F P))
        = K ^ m * (K * sumTo (K ^ K) (fun P => indB (permB K P && F P))) := by rw [Nat.pow_succ, Nat.mul_assoc]
      _ ≤ K ^ m * (sumTo K (fun w => sumTo (K ^ K) (fun P => indB (permB K P && F (swAt K nxt (times m) w P)))) +
            badAt K nxt (times m)) := Nat.mul_le_mul_left _ h1
      _ = sumTo K (fun w => K ^ m * sumTo (K ^ K) (fun P => indB (permB K P && F (swAt K nxt (times m) w P)))) +
            K ^ m * badAt K nxt (times m) := by rw [Nat.mul_add, sumTo_mul]
      _ ≤ sumTo K (fun w => sumTo (K ^ m) (fun W => sumTo (K ^ K) (fun P =>
              indB (permB K P && F (swAt K nxt (times m) w (progSeqN K nxt times m W P))))) +
              badSeq K nxt times m) + K ^ m * badAt K nxt (times m) :=
          Nat.add_le_add_right (sumTo_mono _ (fun w _ => ih w)) _
      _ = sumTo (K ^ (m + 1)) (fun W => sumTo (K ^ K) (fun P => indB (permB K P && F (progSeqN K nxt times (m + 1) W P)))) +
            badSeq K nxt times (m + 1) := by
          rw [sumTo_add, sumTo_const, Nat.add_assoc]
          congr 1
          · rw [Nat.pow_succ, sumTo_split (K ^ m) _ K]
            refine sumTo_congr _ (fun w hw => sumTo_congr _ (fun W hW => sumTo_congr _ (fun P _ => ?_)))
            show indB (permB K P && F (swAt K nxt (times m) w (progSeqN K nxt times m W P))) =
              indB (permB K P && F (swAt K nxt (times m) (rget K m (W + K ^ m * w))
                (progSeqN K nxt times m (W + K ^ m * w) P)))
            rw [rget_add_top hW hw, progSeqN_congr K nxt times P m _ _ (fun j hj => rget_add_high hK hj)]

/-- **A squeeze's cost in a duplex run**: with each position after the first
    keeping `κ` of the answer before it, the exchanges at time `t` that
    change the run are at most `t / K + (0 + ⋯ + t) F / (K - t)` of the
    pairs, as for a run's last squeeze (`squeeze_bad_run`,
    `revisit_countP`). -/
theorem badAt_bound {K F : Nat} (hK : 0 < K) (κ : Nat → Nat) (hF : ∀ v, sumTo K (fun u => indB (decide (κ u = v))) ≤ F)
    (nxt : List Nat → Nat) (hnx : ∀ l, nxt l < K) (hκ : ∀ a l, κ (nxt (a :: l)) = κ a) (t : Nat) :
    (K - t) * badAt K nxt t ≤ (K - t) * t * sumTo (K ^ K) (fun P => indB (permB K P)) +
      K * ((sumTo t (fun j => j) + t) * F * sumTo (K ^ K) (fun P => indB (permB K P))) := by
  have h2 := squeeze_bad_run hK nxt hnx t
  have h3 := revisit_countP hK κ hF nxt hnx hκ t
  refine Nat.le_trans (Nat.mul_le_mul_left _ h2) ?_
  rw [Nat.mul_add, ← Nat.mul_assoc]
  refine Nat.add_le_add_left ?_ _
  rw [Nat.mul_left_comm]
  exact Nat.mul_le_mul_left _ h3

/-- **0.8's duplex meets `badAt_bound`'s hypotheses**: absorptions and
    empty-buffer squeezes alike keep the capacity's tail. -/
theorem badAt_bound08 {R p Q SQ p1 : Nat} (hR : 0 < R) (hp : 0 < p) (hQ : 0 < Q) (h1 : p1 < p ^ R * (p * Q))
    (blk : List Nat → Nat) (t : Nat) :
    let K := p ^ R * (p * Q)
    (K - t) * badAt K (nxt08 R p Q SQ p1 blk) t ≤ (K - t) * t * sumTo (K ^ K) (fun P => indB (permB K P)) +
      K * ((sumTo t (fun j => j) + t) * (p ^ R * p) * sumTo (K ^ K) (fun P => indB (permB K P))) :=
  badAt_bound (Nat.mul_pos (Nat.pow_pos hp) (Nat.mul_pos hp hQ)) (κ08 (p ^ R) p Q)
    (κ08_count (Nat.mul_pos (Nat.pow_pos hp) hp)) _ (nxt08_lt hR hp hQ h1 blk) (nxt08_κ hR hp hQ blk) t

/-! ### The reverse exchange, and the run reading the states back -/

theorem swapV_comm (a b v : Nat) : swapV a b v = swapV b a v := by
  unfold swapV
  by_cases h1 : v = a
  · by_cases h2 : v = b
    · rw [if_pos h1, if_pos h2, ← h1, ← h2]
    · rw [if_pos h1, if_neg h2, if_pos h1]
  · rw [if_neg h1]
    by_cases h2 : v = b
    · rw [if_pos h2, if_pos h2]
    · rw [if_neg h2, if_neg h2, if_neg h1]

theorem vswap_comm (K a b H : Nat) : vswap K a b H = vswap K b a H := by
  unfold vswap; congr 1; funext m; exact swapV_comm a b _

/-- **The exchange reversed**: the pairs `(w, H)` where `f` holds at the
    context, the table with its squeezed answer and `w` exchanged, and `w`
    are at most `K` times the tables where `f` holds at the context, the
    table and its squeezed answer, plus the pairs whose exchange changes the
    context.  So the programmed world is no likelier than the real one. -/
theorem squeeze_swap_rev {α : Type} [DecidableEq α] {K : Nat} (hK : 0 < K) (ctx : Nat → α) (φ : α → Nat)
    (hφ : ∀ c, φ c < K) (f : α → Nat → Nat → Bool) :
    sumTo K (fun w => sumTo (K ^ K) (fun H =>
        indB (permB K H && f (ctx H) (vswap K (rget K (φ (ctx H)) H) w H) w))) ≤
      K * sumTo (K ^ K) (fun H => indB (permB K H && f (ctx H) H (rget K (φ (ctx H)) H))) +
      sumTo (K ^ K) (fun H => sumTo K (fun w =>
        indB (permB K H && !decide (ctx (vswap K (rget K (φ (ctx H)) H) w H) = ctx H)))) := by
  let T := fun (H a w : Nat) => indB (decide (rget K (φ (ctx H)) H = a) &&
    (permB K H && f (ctx H) (vswap K a w H) w && decide (ctx (vswap K a w H) = ctx H)))
  -- split off the exchanges that change the context
  have step1 : ∀ w H, indB (permB K H && f (ctx H) (vswap K (rget K (φ (ctx H)) H) w H) w) ≤
      sumTo K (fun a => T H a w) + indB (permB K H && !decide (ctx (vswap K (rget K (φ (ctx H)) H) w H) = ctx H)) :=
    fun w H => by
    rw [sumTo_pick (fun a => permB K H && f (ctx H) (vswap K a w H) w && decide (ctx (vswap K a w H) = ctx H)) K
      (rget_lt hK _ _)]
    exact indB_split _ _ _
  -- exchanging `a` and `w` back sends a kept pair to a table answering `w`
  have step2 : ∀ a w, a < K → w < K → sumTo (K ^ K) (fun H => T H a w) ≤
      sumTo (K ^ K) (fun H => indB (decide (rget K (φ (ctx H)) H = w) && (permB K H && f (ctx H) H w))) := by
    intro a w ha hw
    rw [← sumTo_perm (fun H => T H a w) (K ^ K) (vswap K a w) (vswap K a w)
      (fun _ _ => vswap_lt hK ha hw _) (fun _ _ => vswap_lt hK ha hw _)
      (fun H hH => vswap_vswap hK ha hw hH) (fun H hH => vswap_vswap hK ha hw hH)]
    refine sumTo_mono _ (fun H hH => ?_)
    cases hs : (decide (rget K (φ (ctx (vswap K a w H))) (vswap K a w H) = a) &&
        (permB K (vswap K a w H) && f (ctx (vswap K a w H)) (vswap K a w (vswap K a w H)) w &&
          decide (ctx (vswap K a w (vswap K a w H)) = ctx (vswap K a w H))))
    · show indB _ ≤ _; rw [hs]; exact Nat.zero_le _
    · show indB _ ≤ _; rw [hs]
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hs
      obtain ⟨hans, ⟨hP, hf⟩, hce⟩ := hs
      rw [vswap_vswap hK ha hw hH] at hce hf
      have hP' : permB K H = true := by
        have := permB_vswap hK ha hw hP; rwa [vswap_vswap hK ha hw hH] at this
      have hans' : rget K (φ (ctx H)) H = w := by
        have e := congrArg (swapV a w) hans
        rw [← rget_vswap hK ha hw (hφ _), vswap_vswap hK ha hw hH, ← hce] at e
        rw [e]; unfold swapV; rw [if_pos rfl]
      rw [← hce] at hf
      rw [hans', hP', hf, decide_eq_true rfl]; exact Nat.le_refl _
  calc sumTo K (fun w => sumTo (K ^ K) (fun H =>
        indB (permB K H && f (ctx H) (vswap K (rget K (φ (ctx H)) H) w H) w)))
      ≤ sumTo K (fun w => sumTo (K ^ K) (fun H => sumTo K (fun a => T H a w) +
          indB (permB K H && !decide (ctx (vswap K (rget K (φ (ctx H)) H) w H) = ctx H)))) :=
        sumTo_mono _ (fun w _ => sumTo_mono _ (fun H _ => step1 w H))
    _ = sumTo K (fun w => sumTo K (fun a => sumTo (K ^ K) (fun H => T H a w))) +
        sumTo (K ^ K) (fun H => sumTo K (fun w =>
          indB (permB K H && !decide (ctx (vswap K (rget K (φ (ctx H)) H) w H) = ctx H)))) := by
        rw [sumTo_congr K (fun w _ => sumTo_add _ _ (K ^ K)), sumTo_add,
          sumTo_exch (fun w H => indB (permB K H && !decide (ctx (vswap K (rget K (φ (ctx H)) H) w H) = ctx H))) (K ^ K) K]
        congr 1
        exact sumTo_congr K (fun w _ => sumTo_exch (fun H a => T H a w) K (K ^ K))
    _ ≤ sumTo K (fun w => sumTo K (fun _ => sumTo (K ^ K) (fun H =>
          indB (decide (rget K (φ (ctx H)) H = w) && (permB K H && f (ctx H) H w))))) + _ :=
        Nat.add_le_add_right (sumTo_mono _ (fun w hw => sumTo_mono _ (fun a ha => step2 a w ha hw))) _
    _ = K * sumTo (K ^ K) (fun H => indB (permB K H && f (ctx H) H (rget K (φ (ctx H)) H))) + _ := by
        congr 1
        rw [sumTo_congr K (fun w _ => sumTo_const _ K), ← sumTo_mul,
          sumTo_exch (fun w H => indB (decide (rget K (φ (ctx H)) H = w) && (permB K H && f (ctx H) H w))) (K ^ K) K]
        congr 1
        exact sumTo_congr _ (fun H _ => sumTo_pick (fun w => permB K H && f (ctx H) H w) K (rget_lt hK _ _))

/-- The run's answer at time `s`. -/
def ansAt (K : Nat) (nxt : List Nat → Nat) (s Q : Nat) : Nat := rget K (posAt K nxt s Q) Q

/-- The answers at the first `m` squeezes, as digits. -/
def WofR (K : Nat) (nxt : List Nat → Nat) (times : Nat → Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | m + 1, H => WofR K nxt times m H + K ^ m * ansAt K nxt (times m) H

/-- A run's answer at time `s`, read off the run, newest first. -/
def ansC (c : List (Nat × Nat)) (s : Nat) : Nat := (c.getD (c.length - 1 - s) (0, 0)).2

/-- The answers at the first `m` squeezes, read off a run. -/
def WCr (K : Nat) (times : Nat → Nat) : Nat → List (Nat × Nat) → Nat
  | 0, _ => 0
  | m + 1, c => WCr K times m c + K ^ m * ansC c (times m)

theorem runAdp_getD {K : Nat} (nxt : List Nat → Nat) (H : Nat) :
    ∀ t s, s < t → (runAdp K nxt H t).getD (t - 1 - s) (0, 0) = (posAt K nxt s H, ansAt K nxt s H)
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | t + 1, s, h => by
    rcases Nat.lt_or_ge s t with hs | hs
    · rw [show t + 1 - 1 - s = (t - 1 - s) + 1 by omega]
      exact runAdp_getD nxt H t s hs
    · have e : s = t := Nat.le_antisymm (Nat.le_of_lt_succ h) hs
      subst e
      rw [show s + 1 - 1 - s = 0 by omega]; rfl

theorem WCr_runAdp {K : Nat} (nxt : List Nat → Nat) (times : Nat → Nat) (H t : Nat) :
    ∀ m, (∀ j, j < m → times j < t) → WCr K times m (runAdp K nxt H t) = WofR K nxt times m H
  | 0, _ => rfl
  | m + 1, h => by
    show WCr K times m (runAdp K nxt H t) + K ^ m * ansC (runAdp K nxt H t) (times m) =
      WofR K nxt times m H + K ^ m * ansAt K nxt (times m) H
    rw [WCr_runAdp nxt times H t m (fun j hj => h j (Nat.lt_succ_of_lt hj))]
    unfold ansC
    rw [runAdp_length, runAdp_getD nxt H t (times m) (h m (Nat.lt_succ_self m))]

theorem badAt_comm (K : Nat) (nxt : List Nat → Nat) (t : Nat) :
    sumTo (K ^ K) (fun H => sumTo K (fun w =>
      indB (permB K H && !decide (runAdp K nxt (vswap K (rget K (posAt K nxt t H) H) w H) t = runAdp K nxt H t)))) =
    badAt K nxt t := by
  unfold badAt
  refine sumTo_congr _ (fun H _ => sumTo_congr _ (fun w _ => ?_))
  rw [vswap_comm]

/-- **The programmed world is no likelier than the real one, its event
    reading the states**: with the squeeze times increasing, the pairs
    `(W, P)` where `F` holds at `W` and `P` programmed at the `m` squeezes
    are at most `K^m` times the tables where `F` holds at the table's own
    squeezed answers and the table, plus `badSeq`. -/
theorem squeeze_seq_rev {K : Nat} (hK : 0 < K) (nxt : List Nat → Nat) (hnx : ∀ l, nxt l < K) (times : Nat → Nat)
    (htimes : ∀ i j, i < j → times i < times j) :
    ∀ (m : Nat) (F : Nat → Nat → Bool),
      sumTo (K ^ m) (fun W => sumTo (K ^ K) (fun P => indB (permB K P && F W (progSeqN K nxt times m W P)))) ≤
        K ^ m * sumTo (K ^ K) (fun P => indB (permB K P && F (WofR K nxt times m P) P)) + badSeq K nxt times m
  | 0, F => by
    show sumTo 1 _ ≤ 1 * _ + 0
    rw [Nat.one_mul, Nat.add_zero]
    show 0 + _ ≤ _
    rw [Nat.zero_add]; exact Nat.le_refl _
  | m + 1, F => by
    have ih := fun w => squeeze_seq_rev hK nxt hnx times htimes m
      (fun W Q => F (W + K ^ m * w) (swAt K nxt (times m) w Q))
    have hr := squeeze_swap_rev hK (fun H => runAdp K nxt H (times m)) (fun c => nxt (c.map Prod.snd)) (fun _ => hnx _)
      (fun c Q w => F (WCr K times m c + K ^ m * w) Q)
    have hr' := Nat.le_trans hr (Nat.add_le_add_left (Nat.le_of_eq (badAt_comm K nxt (times m))) _)
    have hW : ∀ H, WCr K times m (runAdp K nxt H (times m)) = WofR K nxt times m H :=
      fun H => WCr_runAdp nxt times H (times m) m (fun j hj => htimes j m hj)
    calc sumTo (K ^ (m + 1)) (fun W => sumTo (K ^ K) (fun P => indB (permB K P && F W (progSeqN K nxt times (m + 1) W P))))
        = sumTo K (fun w => sumTo (K ^ m) (fun W => sumTo (K ^ K) (fun P =>
            indB (permB K P && F (W + K ^ m * w) (swAt K nxt (times m) w (progSeqN K nxt times m W P)))))) := by
          rw [Nat.pow_succ, sumTo_split (K ^ m) _ K]
          refine sumTo_congr _ (fun w hw => sumTo_congr _ (fun W hW => sumTo_congr _ (fun P _ => ?_)))
          show indB (permB K P && F (W + K ^ m * w) (swAt K nxt (times m) (rget K m (W + K ^ m * w))
              (progSeqN K nxt times m (W + K ^ m * w) P))) = _
          rw [rget_add_top hW hw, progSeqN_congr K nxt times P m _ _ (fun j hj => rget_add_high hK hj)]
      _ ≤ sumTo K (fun w => K ^ m * sumTo (K ^ K) (fun P =>
            indB (permB K P && F (WofR K nxt times m P + K ^ m * w) (swAt K nxt (times m) w P))) +
            badSeq K nxt times m) := sumTo_mono _ (fun w _ => ih w)
      _ = K ^ m * sumTo K (fun w => sumTo (K ^ K) (fun P =>
            indB (permB K P && F (WofR K nxt times m P + K ^ m * w) (swAt K nxt (times m) w P)))) +
            K * badSeq K nxt times m := by
          rw [sumTo_add, sumTo_const, ← sumTo_mul]
      _ ≤ K ^ m * (K * sumTo (K ^ K) (fun P => indB (permB K P && F (WofR K nxt times (m + 1) P) P)) +
            badAt K nxt (times m)) + K * badSeq K nxt times m := by
          refine Nat.add_le_add_right (Nat.mul_le_mul_left _ (Nat.le_trans (Nat.le_of_eq ?_) (Nat.le_trans hr'
            (Nat.le_of_eq ?_)))) _
          · refine sumTo_congr _ (fun w _ => sumTo_congr _ (fun P _ => ?_))
            show _ = indB (permB K P && F (WCr K times m (runAdp K nxt P (times m)) + K ^ m * w)
              (vswap K (rget K (nxt ((runAdp K nxt P (times m)).map Prod.snd)) P) w P))
            rw [hW]; rfl
          · congr 1
            congr 1
            refine sumTo_congr _ (fun P _ => ?_)
            show indB (permB K P && F (WCr K times m (runAdp K nxt P (times m)) + K ^ m *
              rget K (nxt ((runAdp K nxt P (times m)).map Prod.snd)) P) P) = _
            rw [hW]; rfl
      _ = K ^ (m + 1) * sumTo (K ^ K) (fun P => indB (permB K P && F (WofR K nxt times (m + 1) P) P)) +
            badSeq K nxt times (m + 1) := by
          show _ = _ + (K * badSeq K nxt times m + K ^ m * badAt K nxt (times m))
          rw [Nat.mul_add, ← Nat.mul_assoc, ← Nat.pow_succ]
          ac_rfl

theorem WofR_lt {K : Nat} (hK : 0 < K) (nxt : List Nat → Nat) (times : Nat → Nat) (H : Nat) :
    ∀ m, WofR K nxt times m H < K ^ m
  | 0 => Nat.one_pos
  | m + 1 => by
    show WofR K nxt times m H + K ^ m * ansAt K nxt (times m) H < K ^ (m + 1)
    have h1 := WofR_lt hK nxt times H m
    have h2 : ansAt K nxt (times m) H < K := rget_lt hK _ _
    calc WofR K nxt times m H + K ^ m * ansAt K nxt (times m) H
        < K ^ m + K ^ m * ansAt K nxt (times m) H := Nat.add_lt_add_right h1 _
      _ = K ^ m * (ansAt K nxt (times m) H + 1) := by rw [Nat.mul_succ, Nat.add_comm]
      _ ≤ K ^ m * K := Nat.mul_le_mul_left _ h2
      _ = K ^ (m + 1) := (Nat.pow_succ ..).symm

theorem rget_WofR {K : Nat} (hK : 0 < K) (nxt : List Nat → Nat) (times : Nat → Nat) (H : Nat) :
    ∀ m j, j < m → rget K j (WofR K nxt times m H) = ansAt K nxt (times j) H
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | m + 1, j, h => by
    show rget K j (WofR K nxt times m H + K ^ m * ansAt K nxt (times m) H) = _
    rcases Nat.lt_or_ge j m with hj | hj
    · rw [rget_add_high hK hj]; exact rget_WofR hK nxt times H m j hj
    · have e : j = m := Nat.le_antisymm (Nat.le_of_lt_succ h) hj
      subst e
      exact rget_add_top (WofR_lt hK nxt times H _) (rget_lt hK _ _)

/-- **The programmed run reads the states back**: with the squeeze times
    increasing, the pairs `(W, P)` where the run on `P` programmed at the
    `m` squeezes does not answer `rget K j W` at squeeze `j`, for some
    `j < m`, are at most `badSeq`. -/
theorem readback_seq {K : Nat} (hK : 0 < K) (nxt : List Nat → Nat) (hnx : ∀ l, nxt l < K) (times : Nat → Nat)
    (htimes : ∀ i j, i < j → times i < times j) (m : Nat) :
    sumTo (K ^ m) (fun W => sumTo (K ^ K) (fun P => indB (permB K P &&
      !(List.range m).all (fun j => ansAt K nxt (times j) (progSeqN K nxt times m W P) == rget K j W)))) ≤
      badSeq K nxt times m := by
  have h := squeeze_seq_rev hK nxt hnx times htimes m
    (fun W Q => !(List.range m).all (fun j => ansAt K nxt (times j) Q == rget K j W))
  refine Nat.le_trans h (Nat.le_of_eq ?_)
  have z : sumTo (K ^ K) (fun P => indB (permB K P &&
      !(List.range m).all (fun j => ansAt K nxt (times j) P == rget K j (WofR K nxt times m P)))) = 0 := by
    refine Eq.trans (sumTo_congr _ (fun P _ => ?_)) (Eq.trans (sumTo_const 0 _) (Nat.mul_zero _))
    have hall : (List.range m).all (fun j => ansAt K nxt (times j) P == rget K j (WofR K nxt times m P)) = true :=
      List.all_eq_true.2 (fun j hj => by rw [rget_WofR hK nxt times P m j (List.mem_range.1 hj)]; exact beq_iff_eq.2 rfl)
    rw [hall, Bool.not_true, Bool.and_false]; rfl
  rw [z, Nat.mul_zero, Nat.zero_add]

/-! ### A bound with independent challenges, transferred to a duplex run -/

theorem WofR_eq {K : Nat} (hK : 0 < K) (nxt : List Nat → Nat) (times : Nat → Nat) (m Q W : Nat) (hW : W < K ^ m)
    (h : (List.range m).all (fun j => ansAt K nxt (times j) Q == rget K j W) = true) :
    WofR K nxt times m Q = W :=
  digit_ext hK m _ _ (WofR_lt hK nxt times Q m) hW (fun j hj => by
    rw [rget_WofR hK nxt times Q m j hj]
    exact beq_iff_eq.1 (List.all_eq_true.1 h j (List.mem_range.2 hj)))

theorem lin_add2 {Y : Type} (S : (Y → Nat) → Nat) (hS : Lin S) (a b : Y → Nat) :
    S (fun y => a y + 2 * b y) = S a + 2 * S b := by
  rw [sm_add S hS, smK S hS]

/-- **A composite's challenges squeezed from one duplex run.**  The
    hypothesis `hyp` is a bound over a uniform permutation `P`, `m`
    independent uniform challenge states (the digits of `W`) and the other
    tables `H`, every distinguisher reading `P`, `W` and `H`: the real view
    reads its challenges from `W`, and the simulator programs `W` and `H`
    (`pgJ`).  The conclusion is the bound with the challenges read from the
    run's answers at the squeeze times (`WofR`), the run absorbing the
    transcript (`nxt H x`) and continuing from each squeezed state, and the
    simulated distinguisher seeing `P` programmed with the simulated states
    at the squeezes in order (`progSeqN`).  The real view reads the
    permutation only through the challenges.  The distinguisher rebuilds
    the programming from the view (`nxtV`): on the pairs where the honest
    programmed run reads the states back, its rebuilt table must be the
    honest one (`hprog`), which asks the view to fix the run only along the
    runs the programming visits, not the prover's strategy after other
    challenges.  The error gains twice the squeezes'
    `badSeq`, once for the exchange (`squeeze_seq`) and once for the run
    reading the states back (`readback_seq`). -/
theorem zk_duplex {T X C V : Type} {K m K4w ε : Nat} (hK : 0 < K)
    (ST : (T → Nat) → Nat) (hST : Lin ST) (sm : (X → Nat) → Nat) (hsm : Lin sm) (SC : (C → Nat) → Nat)
    (nxt : T → X → List Nat → Nat) (hnx : ∀ H x l, nxt H x l < K) (times : Nat → Nat)
    (htimes : ∀ i j, i < j → times i < times j)
    (rv : T → X → Nat → V) (pgJ : Nat → T → Nat → C → X → T × Nat) (sv : Nat → T → Nat → C → X → V)
    (nxtV : T → V → List Nat → Nat) (G : T → X → Nat → Nat → Bool) (cG : T → X → Nat)
    (hG : ∀ H x, sumTo (K ^ m) (fun W => sumTo (K ^ K) (fun P => indB (permB K P && !G H x W P))) ≤ cG H x)
    (hprog : ∀ H x W P, (List.range m).all (fun j =>
        ansAt K (nxt H x) (times j) (progSeqN K (nxt H x) times m W P) == rget K j W) = true → G H x W P = true →
      progSeqN K (nxtV H (rv H x W)) times m W P = progSeqN K (nxt H x) times m W P)
    (hyp : ∀ D : Nat → Nat → T → V → Bool,
      K4w * ST (fun H => sm (fun x => sumTo (K ^ K) (fun P => indB (permB K P) * sumTo (K ^ m) (fun W =>
        indB (D P W H (rv H x W)))))) ≤
      ST (fun H => SC (fun c => sm (fun x => sumTo (K ^ K) (fun P => indB (permB K P) * sumTo (K ^ m) (fun W =>
        indB (D P (pgJ P H W c x).2 (pgJ P H W c x).1 (sv P H W c x))))))) + ε)
    (E : Nat → T → V → Bool) :
    K4w * (K ^ m * ST (fun H => sm (fun x => sumTo (K ^ K) (fun P => indB (permB K P &&
        E P H (rv H x (WofR K (nxt H x) times m P))))))) ≤
      ST (fun H => SC (fun c => sm (fun x => sumTo (K ^ K) (fun P => indB (permB K P) * sumTo (K ^ m) (fun W =>
        indB (E (progSeqN K (nxtV (pgJ P H W c x).1 (sv P H W c x)) times m (pgJ P H W c x).2 P)
          (pgJ P H W c x).1 (sv P H W c x))))))) + ε +
      K4w * ST (fun H => sm (fun x => 2 * badSeq K (nxt H x) times m + cG H x)) := by
  let DE : Nat → Nat → T → V → Bool := fun P W H' v => E (progSeqN K (nxtV H' v) times m W P) H' v
  have h := hyp DE
  -- per `H` and `x`: the exchange, then the readback
  have hq : ∀ H x, K ^ m * sumTo (K ^ K) (fun P => indB (permB K P && E P H (rv H x (WofR K (nxt H x) times m P)))) ≤
      sumTo (K ^ K) (fun P => indB (permB K P) * sumTo (K ^ m) (fun W => indB (DE P W H (rv H x W)))) +
        (2 * badSeq K (nxt H x) times m + cG H x) := fun H x => by
    have h1 := squeeze_seq hK (nxt H x) (hnx H x) times m (fun Q => E Q H (rv H x (WofR K (nxt H x) times m Q)))
    have h2 := readback_seq hK (nxt H x) (hnx H x) times htimes m
    refine Nat.le_trans h1 ?_
    rw [Nat.two_mul, show ∀ a b c d : Nat, a + (b + c + d) = a + c + d + b from fun a b c d => by omega]
    refine Nat.add_le_add_right (Nat.le_trans ?_ (Nat.add_le_add (Nat.add_le_add_left h2 _) (hG H x))) _
    have e : sumTo (K ^ K) (fun P => indB (permB K P) * sumTo (K ^ m) (fun W => indB (DE P W H (rv H x W)))) =
        sumTo (K ^ m) (fun W => sumTo (K ^ K) (fun P => indB (permB K P && DE P W H (rv H x W)))) := by
      rw [sumTo_exch _ (K ^ K) (K ^ m)]
      refine sumTo_congr _ (fun P _ => ?_)
      rw [sumTo_mul]
      exact sumTo_congr _ (fun W _ => (indB_and _ _).symm)
    rw [e, ← sumTo_add, ← sumTo_add]
    refine sumTo_mono _ (fun W hW => ?_)
    rw [← sumTo_add, ← sumTo_add]
    refine sumTo_mono _ (fun P _ => ?_)
    cases hr : (List.range m).all (fun j => ansAt K (nxt H x) (times j) (progSeqN K (nxt H x) times m W P) == rget K j W)
    · rw [Bool.not_false, Bool.and_true]
      cases permB K P
      · exact Nat.zero_le _
      · exact Nat.le_trans (indB_le_one _) (Nat.le_add_right_of_le (Nat.le_add_left _ _))
    · cases hg : G H x W P
      · rw [Bool.not_false, Bool.and_true]
        cases permB K P
        · exact Nat.zero_le _
        · exact Nat.le_trans (indB_le_one _) (Nat.le_add_left _ _)
      · rw [WofR_eq hK (nxt H x) times m _ W hW hr]
        show indB (permB K P && E (progSeqN K (nxt H x) times m W P) H (rv H x W)) ≤
          indB (permB K P && E (progSeqN K (nxtV H (rv H x W)) times m W P) H (rv H x W)) + _ + _
        rw [hprog H x W P hr hg]; exact Nat.le_add_right_of_le (Nat.le_add_right _ _)
  have smm : ∀ {f g : X → Nat}, (∀ x, f x ≤ g x) → sm f ≤ sm g := fun h => sm_mono sm hsm h
  have stm : ∀ {f g : T → Nat}, (∀ H, f H ≤ g H) → ST f ≤ ST g := fun h => sm_mono ST hST h
  calc K4w * (K ^ m * ST (fun H => sm (fun x => sumTo (K ^ K) (fun P => indB (permB K P &&
        E P H (rv H x (WofR K (nxt H x) times m P)))))))
      = K4w * ST (fun H => sm (fun x => K ^ m * sumTo (K ^ K) (fun P => indB (permB K P &&
          E P H (rv H x (WofR K (nxt H x) times m P)))))) := by
        rw [← smK ST hST]; congr 1; refine congrArg ST (funext fun H => ?_); rw [smK sm hsm]
    _ ≤ K4w * ST (fun H => sm (fun x => sumTo (K ^ K) (fun P => indB (permB K P) * sumTo (K ^ m) (fun W =>
          indB (DE P W H (rv H x W)))) + (2 * badSeq K (nxt H x) times m + cG H x))) :=
        Nat.mul_le_mul_left _ (stm (fun H => smm (fun x => hq H x)))
    _ = K4w * ST (fun H => sm (fun x => sumTo (K ^ K) (fun P => indB (permB K P) * sumTo (K ^ m) (fun W =>
          indB (DE P W H (rv H x W)))))) +
          K4w * ST (fun H => sm (fun x => 2 * badSeq K (nxt H x) times m + cG H x)) := by
        rw [← Nat.mul_add]
        congr 1
        rw [← sm_add ST hST]
        exact congrArg ST (funext fun H => sm_add sm hsm _ _)
    _ ≤ _ := Nat.add_le_add_right h _

/-- **`zk_duplex`'s hypotheses hold together, at 0.8's duplex**: `m`
    squeezes at increasing times in one run of absorptions and empty-buffer
    squeezes, the view the run's next-position function and the challenge
    states, the simulator reading the states as the real view does, so
    `hyp` holds exactly.  The witness is degenerate: no tables, no draws,
    no programming, the view carrying the run's next-position function.
    The conclusion says the permutation and the run's
    squeezed answers look as the permutation programmed at the squeezes
    with uniform states does, up to twice `badSeq`. -/
theorem zk_duplex_sat08 {R p Q SQ p1 : Nat} (hR : 0 < R) (hp : 0 < p) (hQ : 0 < Q) (h1 : p1 < p ^ R * (p * Q))
    (blk : List Nat → Nat) (times : Nat → Nat) (htimes : ∀ i j, i < j → times i < times j) (m : Nat)
    (E : Nat → Unit → (List Nat → Nat) × Nat → Bool) :
    let K := p ^ R * (p * Q)
    let nxt := nxt08 R p Q SQ p1 blk
    1 * (K ^ m * sumTo (K ^ K) (fun P => indB (permB K P && E P () (nxt, WofR K nxt times m P)))) ≤
      sumTo (K ^ K) (fun P => indB (permB K P) * sumTo (K ^ m) (fun W =>
        indB (E (progSeqN K nxt times m W P) () (nxt, W)))) + 0 + 1 * (2 * badSeq K nxt times m + 0) := by
  intro K nxt
  have hK : 0 < K := Nat.mul_pos (Nat.pow_pos hp) (Nat.mul_pos hp hQ)
  exact zk_duplex (T := Unit) (X := Unit) (C := Unit) (K4w := 1) (ε := 0) hK (fun f => f ()) (fun _ _ => rfl)
    (fun f => f ()) (fun _ _ => rfl) (fun f => f ()) (fun _ _ => nxt) (fun _ _ => nxt08_lt hR hp hQ h1 blk) times htimes
    (fun _ _ W => (nxt, W)) (fun _ H W _ _ => (H, W)) (fun _ _ W _ _ => (nxt, W)) (fun _ v => v.1)
    (fun _ _ _ _ => true) (fun _ _ => 0)
    (fun _ _ => Nat.le_of_eq (Eq.trans (sumTo_congr _ (fun _ _ => Eq.trans (sumTo_congr _ (fun P _ => by
      show indB (permB K P && false) = 0; rw [Bool.and_false]; rfl)) (Eq.trans (sumTo_const 0 _) (Nat.mul_zero _))))
      (Eq.trans (sumTo_const 0 _) (Nat.mul_zero _))))
    (fun _ _ _ _ _ _ => rfl)
    (fun D => by rw [Nat.one_mul, Nat.add_zero]; exact Nat.le_refl _) E

/-! ### The distinguisher's run agreeing along the programmed runs -/

/-- The answers `l`, newest first, show the states of `W` at every squeeze
    they reach among the first `m`. -/
def consW (K : Nat) (times : Nat → Nat) (m W : Nat) (l : List Nat) : Bool :=
  (List.range m).all (fun i => !decide (times i < l.length) || (l.getD (l.length - 1 - times i) 0 == rget K i W))

/-- The run on `Q` answers the states of `W` at its first `j` squeezes. -/
def readB (K : Nat) (nxt : List Nat → Nat) (times : Nat → Nat) (j W Q : Nat) : Bool :=
  (List.range j).all (fun i => ansAt K nxt (times i) Q == rget K i W)

theorem runAdp_getD_snd {K : Nat} (nxt : List Nat → Nat) (H t s : Nat) (h : s < t) :
    ((runAdp K nxt H t).map Prod.snd).getD (t - 1 - s) 0 = ansAt K nxt s H := by
  have e := runAdp_getD (K := K) nxt H t s h
  have hlt : t - 1 - s < (runAdp K nxt H t).length := by rw [runAdp_length]; omega
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hlt]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt] at e
  simp only [Option.map_some, Option.getD_some] at e ⊢
  rw [e]

/-- **A run's answers are consistent with `W` up to a stage that reads `W`
    back**: with the squeeze times increasing, the run on `Q` up to time
    `times j` shows `W`'s states at the squeezes it reaches when `Q` answers
    them at its first `j` squeezes. -/
theorem consW_run {K : Nat} (nxt : List Nat → Nat) (times : Nat → Nat) (htimes : ∀ i j, i < j → times i < times j)
    (m j W Q s : Nat) (hs : s ≤ times j) (hr : readB K nxt times j W Q = true) :
    consW K times m W ((runAdp K nxt Q s).map Prod.snd) = true := by
  unfold consW
  refine List.all_eq_true.2 (fun i _ => ?_)
  rw [List.length_map, runAdp_length]
  by_cases hi : times i < s
  · have hij : i < j := by
      rcases Nat.lt_or_ge i j with h | h
      · exact h
      · exfalso
        rcases Nat.lt_or_ge j i with h' | h'
        · exact absurd (Nat.lt_of_lt_of_le hi hs) (Nat.not_lt.2 (Nat.le_of_lt (htimes j i h')))
        · have e : i = j := Nat.le_antisymm h' h
          subst e; exact absurd (Nat.lt_of_lt_of_le hi hs) (Nat.lt_irrefl _)
    rw [decide_eq_true hi, Bool.not_true, Bool.false_or, runAdp_getD_snd nxt Q s (times i) hi]
    exact List.all_eq_true.1 hr i (List.mem_range.2 hij)
  · rw [decide_eq_false hi]; rfl

theorem runAdp_agree {K : Nat} (f1 f2 : List Nat → Nat) (Q : Nat) (cons : List Nat → Bool)
    (hag : ∀ l, cons l = true → f1 l = f2 l) :
    ∀ s, (∀ s', s' ≤ s → cons ((runAdp K f2 Q s').map Prod.snd) = true) → runAdp K f1 Q s = runAdp K f2 Q s
  | 0, _ => rfl
  | s + 1, h => by
    have ih := runAdp_agree f1 f2 Q cons hag s (fun s' hs' => h s' (Nat.le_succ_of_le hs'))
    show (f1 ((runAdp K f1 Q s).map Prod.snd), rget K (f1 ((runAdp K f1 Q s).map Prod.snd)) Q) :: runAdp K f1 Q s =
      (f2 ((runAdp K f2 Q s).map Prod.snd), rget K (f2 ((runAdp K f2 Q s).map Prod.snd)) Q) :: runAdp K f2 Q s
    rw [ih, hag _ (h s (Nat.le_succ s))]

/-- **Two run functions agreeing on the lists consistent with `W` program
    the same table** while every stage reads `W` back. -/
theorem progSeqN_agree {K : Nat} (f1 f2 : List Nat → Nat) (times : Nat → Nat)
    (htimes : ∀ i j, i < j → times i < times j) (m W P : Nat)
    (hag : ∀ l, consW K times m W l = true → f1 l = f2 l) :
    ∀ j, j ≤ m → (∀ i, i < j → readB K f2 times i W (progSeqN K f2 times i W P) = true) →
      progSeqN K f1 times j W P = progSeqN K f2 times j W P
  | 0, _, _ => rfl
  | j + 1, hj, hr => by
    have ih := progSeqN_agree f1 f2 times htimes m W P hag j (Nat.le_of_succ_le hj)
      (fun i hi => hr i (Nat.lt_succ_of_lt hi))
    show swAt K f1 (times j) (rget K j W) (progSeqN K f1 times j W P) =
      swAt K f2 (times j) (rget K j W) (progSeqN K f2 times j W P)
    rw [ih]
    have hrj := hr j (Nat.lt_succ_self j)
    have hrun := runAdp_agree (K := K) f1 f2 (progSeqN K f2 times j W P) (consW K times m W) hag (times j)
      (fun s' hs' => consW_run f2 times htimes m j W _ s' hs' hrj)
    have hpos : posAt K f1 (times j) (progSeqN K f2 times j W P) = posAt K f2 (times j) (progSeqN K f2 times j W P) := by
      unfold posAt
      rw [hrun, hag _ (consW_run f2 times htimes m j W _ (times j) (Nat.le_refl _) hrj)]
    unfold swAt
    rw [hpos]

theorem progSeqN_lt {K : Nat} (hK : 0 < K) (nxt : List Nat → Nat) (times : Nat → Nat) (W P : Nat) (hP : P < K ^ K) :
    ∀ j, progSeqN K nxt times j W P < K ^ K
  | 0 => hP
  | _ + 1 => vswap_lt hK (rget_lt hK _ _) (rget_lt hK _ _) _

theorem all_range_congr (f g : Nat → Bool) (j : Nat) (h : ∀ i, i < j → f i = g i) :
    (List.range j).all f = (List.range j).all g := by
  apply Bool.eq_iff_iff.2
  rw [List.all_eq_true, List.all_eq_true]
  exact ⟨fun hf i hi => by rw [← h i (List.mem_range.1 hi)]; exact hf i hi,
    fun hg i hi => by rw [h i (List.mem_range.1 hi)]; exact hg i hi⟩

theorem readB_congr {K : Nat} (hK : 0 < K) (nxt : List Nat → Nat) (times : Nat → Nat) (j W Q q : Nat) :
    readB K nxt times j (W + K ^ j * q) Q = readB K nxt times j W Q := by
  unfold readB
  exact all_range_congr _ _ j (fun i hi => by rw [rget_add_high hK hi])

/-- **A stage's readback failures over `m` digits** are `K^(m-j)` times
    those over its own `j` digits, at most `K^(m-j) badSeq j`. -/
theorem stage_count {K : Nat} (hK : 0 < K) (nxt : List Nat → Nat) (hnx : ∀ l, nxt l < K) (times : Nat → Nat)
    (htimes : ∀ i j, i < j → times i < times j) (m j : Nat) (hj : j ≤ m) :
    sumTo (K ^ m) (fun W => sumTo (K ^ K) (fun P =>
      indB (permB K P && !readB K nxt times j W (progSeqN K nxt times j W P)))) ≤
      K ^ (m - j) * badSeq K nxt times j := by
  have e : K ^ m = K ^ j * K ^ (m - j) := by rw [← Nat.pow_add]; congr 1; omega
  rw [e, sumTo_split (K ^ j) _ (K ^ (m - j))]
  have each : ∀ q, sumTo (K ^ j) (fun r => sumTo (K ^ K) (fun P =>
      indB (permB K P && !readB K nxt times j (r + K ^ j * q) (progSeqN K nxt times j (r + K ^ j * q) P)))) =
      sumTo (K ^ j) (fun r => sumTo (K ^ K) (fun P =>
        indB (permB K P && !readB K nxt times j r (progSeqN K nxt times j r P)))) := fun q =>
    sumTo_congr _ (fun r _ => sumTo_congr _ (fun P _ => by
      rw [progSeqN_congr K nxt times P j _ r (fun i hi => rget_add_high hK hi), readB_congr hK]))
  rw [sumTo_congr _ (fun q _ => each q), sumTo_const]
  exact Nat.mul_le_mul_left _ (readback_seq hK nxt hnx times htimes j)

theorem indB_not_all (b : Bool) (f : Nat → Bool) :
    ∀ m, indB (b && !(List.range m).all f) ≤ sumTo m (fun j => indB (b && !f j))
  | 0 => by show indB (b && !true) ≤ 0; rw [Bool.not_true, Bool.and_false]; exact Nat.le_refl _
  | m + 1 => by
    rw [List.range_succ, List.all_append]
    show indB (b && !((List.range m).all f && (f m && true))) ≤ sumTo m (fun j => indB (b && !f j)) + indB (b && !f m)
    have ih := indB_not_all b f m
    cases hm : (List.range m).all f <;> cases hf : f m <;> cases b <;> simp only [hm, hf] at ih ⊢ <;>
      first | exact Nat.zero_le _ | exact Nat.le_add_right_of_le ih | exact Nat.le_add_left _ _ | exact ih |
        exact Nat.le_trans ih (Nat.le_add_right _ _)

/-- **`zk_duplex` with the distinguisher's run agreeing on consistent
    answers**: the view's run function need only agree with the real one on
    the answer lists that show the drawn states at the squeezes they reach
    (`hcons`), as a view carrying the actual transcript does.  The two then
    program the same table while every stage reads the states back
    (`progSeqN_agree`), and the stages' failures cost
    `Σ_{j<m} K^(m-j) badSeq j` more (`stage_count`). -/
theorem zk_duplexC {T X C V : Type} {K m K4w ε : Nat} (hK : 0 < K)
    (ST : (T → Nat) → Nat) (hST : Lin ST) (sm : (X → Nat) → Nat) (hsm : Lin sm) (SC : (C → Nat) → Nat)
    (nxt : T → X → List Nat → Nat) (hnx : ∀ H x l, nxt H x l < K) (times : Nat → Nat)
    (htimes : ∀ i j, i < j → times i < times j)
    (rv : T → X → Nat → V) (pgJ : Nat → T → Nat → C → X → T × Nat) (sv : Nat → T → Nat → C → X → V)
    (nxtV : T → V → List Nat → Nat)
    (hcons : ∀ H x W l, consW K times m W l = true → nxtV H (rv H x W) l = nxt H x l)
    (hyp : ∀ D : Nat → Nat → T → V → Bool,
      K4w * ST (fun H => sm (fun x => sumTo (K ^ K) (fun P => indB (permB K P) * sumTo (K ^ m) (fun W =>
        indB (D P W H (rv H x W)))))) ≤
      ST (fun H => SC (fun c => sm (fun x => sumTo (K ^ K) (fun P => indB (permB K P) * sumTo (K ^ m) (fun W =>
        indB (D P (pgJ P H W c x).2 (pgJ P H W c x).1 (sv P H W c x))))))) + ε)
    (E : Nat → T → V → Bool) :
    K4w * (K ^ m * ST (fun H => sm (fun x => sumTo (K ^ K) (fun P => indB (permB K P &&
        E P H (rv H x (WofR K (nxt H x) times m P))))))) ≤
      ST (fun H => SC (fun c => sm (fun x => sumTo (K ^ K) (fun P => indB (permB K P) * sumTo (K ^ m) (fun W =>
        indB (E (progSeqN K (nxtV (pgJ P H W c x).1 (sv P H W c x)) times m (pgJ P H W c x).2 P)
          (pgJ P H W c x).1 (sv P H W c x))))))) + ε +
      K4w * ST (fun H => sm (fun x => 2 * badSeq K (nxt H x) times m +
        sumTo m (fun j => K ^ (m - j) * badSeq K (nxt H x) times j))) :=
  zk_duplex hK ST hST sm hsm SC nxt hnx times htimes rv pgJ sv nxtV
    (fun H x W P => (List.range m).all (fun i => readB K (nxt H x) times i W (progSeqN K (nxt H x) times i W P)))
    (fun H x => sumTo m (fun j => K ^ (m - j) * badSeq K (nxt H x) times j))
    (fun H x => by
      refine Nat.le_trans (sumTo_mono _ (fun W _ => sumTo_mono _ (fun P _ => indB_not_all _ _ m))) ?_
      rw [sumTo_congr _ (fun W _ => sumTo_exch _ m (K ^ K)), sumTo_exch _ m (K ^ m)]
      exact sumTo_mono _ (fun j hj => stage_count hK (nxt H x) (hnx H x) times htimes m j (Nat.le_of_lt hj)))
    (fun H x W P _ hg => progSeqN_agree _ _ times htimes m W P (hcons H x W) m (Nat.le_refl _)
      (fun i hi => List.all_eq_true.1 hg i (List.mem_range.2 hi)))
    hyp E

end Circuit
