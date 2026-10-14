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
  bounded by `squeeze_bad_run` and `revisit_countP` at `times j`.

Not shown: that the run on the programmed table reads state `j` at
squeeze `j` (a readback lemma, which costs the states' collisions, about
`m² / K`, and their freshness on the programmed tables); the challenges'
tables indexed by transcript prefixes, as the composites read `H1`–`H3`;
the composites restated with the first three challenges read from the
permutation.  0.8 pops several challenges from one squeezed state, so a
challenge is a projection of some squeeze's state, not of its own.
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

end Circuit
