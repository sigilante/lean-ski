import Ski.ZK.FSQuery

/-!
# Several proofs under one oracle

The simulator of each proof programs the oracle at its own messages; two
proofs share the oracle, so the second proof's real message may hit an
answer the first's simulator set.  A hybrid swaps the first proof for its
simulation with the second real beside it (the distinguisher computes the
second proof from the table), then the second, the first's programming
in place: where the second's message misses the programmed answer the
reprogramming is exact (`rget_rset_ne`, `reprog_beside`), and the pairs
where it hits it, `δ` of them, enter the bound (`fs_zk_two`); a salted
commitment's spread over its salts bounds them (`col_spread`).  One round
per proof, one table.
-/

namespace Circuit

open ZKF

/-- A digit other than `m'` does not read the digit at `m'`. -/
theorem rget_digit_ne {K m m' : Nat} (hK : 0 < K) (hne : m ≠ m') {lo hi : Nat} (hlo : lo < K ^ m') (d d' : Nat) :
    rget K m (lo + K ^ m' * (d + K * hi)) = rget K m (lo + K ^ m' * (d' + K * hi)) ∨ K ≤ d ∨ K ≤ d' := by
  rcases Nat.lt_or_ge d K with hd | hd
  · rcases Nat.lt_or_ge d' K with hd' | hd'
    · left
      unfold rget
      rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
      · -- m < m': the digit sits below
        have hp : K ^ m' = K ^ m * K ^ (m' - m) := by rw [← Nat.pow_add]; congr 1; omega
        have hk : K ^ (m' - m) = K * K ^ (m' - m - 1) := by rw [← Nat.pow_succ']; congr 1; omega
        have hpos : 0 < K ^ m := Nat.pow_pos hK
        have e : ∀ x, (lo + K ^ m' * x) / K ^ m % K = lo / K ^ m % K := fun x => by
          rw [hp, Nat.mul_assoc, Nat.add_mul_div_left _ _ hpos, hk, Nat.mul_assoc, Nat.add_mul_mod_self_left]
        rw [e, e]
      · -- m > m': the digit sits above
        have hp : K ^ m = K ^ m' * (K * K ^ (m - m' - 1)) := by
          rw [← Nat.pow_succ', ← Nat.pow_add]; congr 1; omega
        have hpos : 0 < K ^ m' := Nat.pow_pos hK
        have e : ∀ x, x < K → (lo + K ^ m' * (x + K * hi)) / K ^ m = hi / K ^ (m - m' - 1) := fun x hx => by
          rw [hp, ← Nat.div_div_eq_div_mul, Nat.add_mul_div_left _ _ hpos, Nat.div_eq_of_lt hlo, Nat.zero_add,
            ← Nat.div_div_eq_div_mul, Nat.add_mul_div_left _ _ hK, Nat.div_eq_of_lt hx, Nat.zero_add]
        rw [e d hd, e d' hd']
    · exact .inr (.inr hd')
  · exact .inr (.inl hd)

/-- **Setting one answer leaves the others**: for `m ≠ m'`. -/
theorem rget_rset_ne {K m m' H c : Nat} (hK : 0 < K) (hne : m ≠ m') (hc : c < K) :
    rget K m (rset K m' H c) = rget K m H := by
  have hpos : 0 < K ^ m' := Nat.pow_pos hK
  have h1 := Nat.mod_add_div H (K ^ m')
  have h2 := Nat.mod_add_div (H / K ^ m') K
  have hH : H = H % K ^ m' + K ^ m' * (H / K ^ m' % K + K * (H / K ^ m' / K)) := by rw [h2]; exact h1.symm
  obtain ⟨_, hs⟩ := split_digit (m := m') hK (Nat.mod_lt H hpos) (Nat.mod_lt (H / K ^ m') hK)
    (hi := H / K ^ m' / K)
  rw [← hH] at hs
  rw [hs c]
  conv => rhs; rw [hH]
  rcases rget_digit_ne hK hne (Nat.mod_lt H hpos) (hi := H / K ^ m' / K) c (H / K ^ m' % K) with e | e | e
  · exact e
  · omega
  · exact absurd e (Nat.not_le.2 (Nat.mod_lt _ hK))

theorem smK {X : Type} (sm : (X → Nat) → Nat)
    (hsm : ∀ (N : Nat) (f : Nat → X → Nat), sm (fun x => sumTo N (fun i => f i x)) = sumTo N (fun i => sm (f i)))
    (c : Nat) (f : X → Nat) : sm (fun x => c * f x) = c * sm f := by
  rw [show (fun x => c * f x) = fun x => sumTo c (fun _ => f x) from funext fun x => (sumTo_const _ c).symm,
    hsm c (fun _ x => f x), sumTo_const]

theorem smC {X : Type} (sm : (X → Nat) → Nat)
    (hsm : ∀ (N : Nat) (f : Nat → X → Nat), sm (fun x => sumTo N (fun i => f i x)) = sumTo N (fun i => sm (f i)))
    (c : Nat) : sm (fun _ => c) = c * sm (fun _ => 1) := by
  rw [← smK sm hsm c (fun _ => 1)]; simp only [Nat.mul_one]

/-- **Reprogramming one answer, read back**. -/
theorem oracle_reprog_get {K n m : Nat} (hK : 0 < K) (hm : m < n) (f : Nat → Nat → Nat) :
    sumTo (K ^ n) (fun H => sumTo K (fun c => f (rset K m H c) c)) = K * sumTo (K ^ n) (fun H => f H (rget K m H)) := by
  rw [← oracle_reprog hK hm (fun H => f H (rget K m H))]
  exact sumTo_congr _ (fun H _ => sumTo_congr _ (fun c hc => by rw [rget_rset hK hc]))

/-- **The second proof's real count beside the first's programming**: where
    its message misses the programmed answer, reprogramming is exact;
    where it hits it, the whole count `K Kⁿ` bounds it. -/
theorem reprog_beside {K n m p ca : Nat} (hK : 0 < K) (hm : m < n) (hca : ca < K) (f : Nat → Nat → Nat)
    (hf : ∀ H c, f H c ≤ 1) :
    K * sumTo (K ^ n) (fun H => f (rset K p H ca) (rget K m (rset K p H ca))) ≤
      sumTo (K ^ n) (fun H => sumTo K (fun cb => f (rset K p (rset K m H cb) ca) cb)) +
        K * (K ^ n * indB (decide (m = p))) := by
  by_cases e : m = p
  · simp only [e, decide_true, indB, if_true, Nat.mul_one]
    refine Nat.le_trans ?_ (Nat.le_add_left _ _)
    refine Nat.mul_le_mul_left _ (Nat.le_trans (sumTo_mono _ (fun H _ => hf _ _)) (Nat.le_of_eq ?_))
    rw [sumTo_const, Nat.mul_one]
  · simp only [e, decide_false, indB]
    rw [oracle_reprog_get hK hm (fun H c => f (rset K p H ca) c)]
    exact Nat.le_of_eq (congrArg _ (sumTo_congr _ (fun H _ => by rw [rget_rset_ne hK e hca])))

/-- **Two proofs under one oracle**, one round each: the real count, both
    proofs reading one table, against the simulators', the first proof's
    answers programmed over the second's.  The error is each proof's own,
    over the other's randomness, and the pairs whose second real message
    hits the first simulated one (`δ` of them). -/
theorem fs_zk_two {XA XB VA VB : Type} {K n εA εB δ : Nat} (hK : 0 < K)
    (smA : (XA → Nat) → Nat)
    (hsmA : ∀ (N : Nat) (f : Nat → XA → Nat), smA (fun x => sumTo N (fun i => f i x)) = sumTo N (fun i => smA (f i)))
    (smB : (XB → Nat) → Nat)
    (hsmB : ∀ (N : Nat) (f : Nat → XB → Nat), smB (fun x => sumTo N (fun i => f i x)) = sumTo N (fun i => smB (f i)))
    (hcomm : ∀ f : XA → XB → Nat, smB (fun xb => smA (fun xa => f xa xb)) = smA (fun xa => smB (fun xb => f xa xb)))
    (mA sA : XA → Nat) (mB sB : XB → Nat) (hmA : ∀ x, mA x < n) (hmB : ∀ x, mB x < n)
    (rvA svA : Nat → XA → VA) (rvB svB : Nat → XB → VB)
    (hA : ∀ F : Nat → Nat → VA → Bool, sumTo K (fun c => smA (fun x => indB (F c (mA x) (rvA c x)))) ≤
      sumTo K (fun c => smA (fun x => indB (F c (sA x) (svA c x)))) + εA)
    (hB : ∀ F : Nat → Nat → VB → Bool, sumTo K (fun c => smB (fun x => indB (F c (mB x) (rvB c x)))) ≤
      sumTo K (fun c => smB (fun x => indB (F c (sB x) (svB c x)))) + εB)
    (hcol : smA (fun xa => smB (fun xb => indB (decide (mB xb = sA xa)))) ≤ δ)
    (E : Nat → Nat → Nat → VA → VB → Bool) :
    K * (K * sumTo (K ^ n) (fun H => smB (fun xb => smA (fun xa =>
      indB (E H (mA xa) (mB xb) (rvA (rget K (mA xa) H) xa) (rvB (rget K (mB xb) H) xb)))))) ≤
    sumTo K (fun ca => sumTo (K ^ n) (fun H => sumTo K (fun cb => smA (fun xa => smB (fun xb =>
      indB (E (rset K (sA xa) (rset K (sB xb) H cb) ca) (sA xa) (sB xb) (svA ca xa) (svB cb xb))))))) +
    K * (K ^ n * εB) * smA (fun _ => 1) + K * (K * (K ^ n * δ)) + K * (K ^ n * εA * smB (fun _ => 1)) := by
  -- the first proof simulated, the second real beside it
  let hyb := fun (ca : Nat) (H : Nat) (xa : XA) (xb : XB) =>
    indB (E (rset K (sA xa) H ca) (sA xa) (mB xb) (svA ca xa) (rvB (rget K (mB xb) (rset K (sA xa) H ca)) xb))
  have h1 : ∀ xb, K * sumTo (K ^ n) (fun H => smA (fun xa =>
      indB (E H (mA xa) (mB xb) (rvA (rget K (mA xa) H) xa) (rvB (rget K (mB xb) H) xb)))) ≤
      sumTo (K ^ n) (fun H => sumTo K (fun ca => smA (fun xa => hyb ca H xa xb))) + K ^ n * εA := fun xb => by
    rw [fs_real hK smA hsmA mA hmA rvA (fun H m _ v => E H m (mB xb) v (rvB (rget K (mB xb) H) xb))]
    calc sumTo (K ^ n) (fun H => sumTo K (fun c => smA (fun x => indB (E (rset K (mA x) H c) (mA x) (mB xb) (rvA c x)
          (rvB (rget K (mB xb) (rset K (mA x) H c)) xb)))))
        ≤ sumTo (K ^ n) (fun H => sumTo K (fun ca => smA (fun xa => hyb ca H xa xb)) + εA) :=
          sumTo_mono _ (fun H _ => hA (fun c m v => E (rset K m H c) m (mB xb) v (rvB (rget K (mB xb) (rset K m H c)) xb)))
      _ = _ := by rw [sumTo_add, sumTo_const]
  -- the first step, over the second proof's randomness
  have s1 : K * sumTo (K ^ n) (fun H => smB (fun xb => smA (fun xa =>
      indB (E H (mA xa) (mB xb) (rvA (rget K (mA xa) H) xa) (rvB (rget K (mB xb) H) xb))))) ≤
      smB (fun xb => sumTo (K ^ n) (fun H => sumTo K (fun ca => smA (fun xa => hyb ca H xa xb)))) +
        K ^ n * εA * smB (fun _ => 1) := by
    rw [← hsmB (K ^ n) (fun H xb => smA (fun xa =>
      indB (E H (mA xa) (mB xb) (rvA (rget K (mA xa) H) xa) (rvB (rget K (mB xb) H) xb)))), ← smK smB hsmB]
    refine Nat.le_trans (sm_mono smB hsmB h1) (Nat.le_of_eq ?_)
    rw [sm_add smB hsmB, smC smB hsmB]
  -- the second step, at each first challenge and first randomness
  have h2 : ∀ ca, ca < K → ∀ xa xb, K * sumTo (K ^ n) (fun H => hyb ca H xa xb) ≤
      sumTo (K ^ n) (fun H => sumTo K (fun cb =>
        indB (E (rset K (sA xa) (rset K (mB xb) H cb) ca) (sA xa) (mB xb) (svA ca xa) (rvB cb xb)))) +
        K * (K ^ n * indB (decide (mB xb = sA xa))) := fun ca hca xa xb =>
    reprog_beside hK (hmB xb) hca (fun H c => indB (E H (sA xa) (mB xb) (svA ca xa) (rvB c xb)))
      (fun _ _ => indB_le _)
  let G' := fun (ca H cb : Nat) (xa : XA) (xb : XB) =>
    indB (E (rset K (sA xa) (rset K (mB xb) H cb) ca) (sA xa) (mB xb) (svA ca xa) (rvB cb xb))
  let Sm := fun (ca H cb : Nat) (xa : XA) (xb : XB) =>
    indB (E (rset K (sA xa) (rset K (sB xb) H cb) ca) (sA xa) (sB xb) (svA ca xa) (svB cb xb))
  let col := fun (xa : XA) (xb : XB) => indB (decide (mB xb = sA xa))
  -- the second proof's bound at each first challenge and randomness
  have hb : ∀ ca xa, smB (fun xb => sumTo (K ^ n) (fun H => sumTo K (fun cb => G' ca H cb xa xb))) ≤
      sumTo (K ^ n) (fun H => sumTo K (fun cb => smB (fun xb => Sm ca H cb xa xb))) + K ^ n * εB := fun ca xa => by
    rw [hsmB]
    calc sumTo (K ^ n) (fun H => smB (fun xb => sumTo K (fun cb => G' ca H cb xa xb)))
        ≤ sumTo (K ^ n) (fun H => sumTo K (fun cb => smB (fun xb => Sm ca H cb xa xb)) + εB) :=
          sumTo_mono _ (fun H _ => by
            rw [hsmB]
            exact hB (fun cb m v => E (rset K (sA xa) (rset K m H cb) ca) (sA xa) m (svA ca xa) v))
      _ = _ := by rw [sumTo_add, sumTo_const]
  -- the hybrid's sums reordered
  have e2 : smB (fun xb => sumTo (K ^ n) (fun H => sumTo K (fun ca => smA (fun xa => hyb ca H xa xb)))) =
      sumTo K (fun ca => smA (fun xa => smB (fun xb => sumTo (K ^ n) (fun H => hyb ca H xa xb)))) := by
    rw [hsmB]
    simp only [hsmB, hcomm]
    rw [sumTo_exch _ K (K ^ n)]
    refine sumTo_congr _ (fun ca _ => ?_)
    rw [← hsmA]
  have s2 : K * smB (fun xb => sumTo (K ^ n) (fun H => sumTo K (fun ca => smA (fun xa => hyb ca H xa xb)))) ≤
      sumTo K (fun ca => sumTo (K ^ n) (fun H => sumTo K (fun cb => smA (fun xa => smB (fun xb => Sm ca H cb xa xb))))) +
        K * (K ^ n * εB) * smA (fun _ => 1) + K * (K * (K ^ n * smA (fun xa => smB (fun xb => col xa xb)))) := by
    rw [e2, sumTo_mul]
    calc sumTo K (fun ca => K * smA (fun xa => smB (fun xb => sumTo (K ^ n) (fun H => hyb ca H xa xb))))
        ≤ sumTo K (fun ca => sumTo (K ^ n) (fun H => sumTo K (fun cb => smA (fun xa => smB (fun xb => Sm ca H cb xa xb)))) +
            K ^ n * εB * smA (fun _ => 1) + K * (K ^ n * smA (fun xa => smB (fun xb => col xa xb)))) :=
          sumTo_mono _ (fun ca hca => by
            rw [← smK smA hsmA]
            calc smA (fun xa => K * smB (fun xb => sumTo (K ^ n) (fun H => hyb ca H xa xb)))
                ≤ smA (fun xa => smB (fun xb => sumTo (K ^ n) (fun H => sumTo K (fun cb => G' ca H cb xa xb)) +
                    K * (K ^ n * col xa xb))) := sm_mono smA hsmA (fun xa => by
                  rw [← smK smB hsmB]
                  exact sm_mono smB hsmB (fun xb => h2 ca hca xa xb))
              _ ≤ smA (fun xa => sumTo (K ^ n) (fun H => sumTo K (fun cb => smB (fun xb => Sm ca H cb xa xb))) +
                    K ^ n * εB + K * (K ^ n * smB (fun xb => col xa xb))) := sm_mono smA hsmA (fun xa => by
                  rw [sm_add smB hsmB, smK smB hsmB, smK smB hsmB]
                  exact Nat.add_le_add_right (hb ca xa) _)
              _ = _ := by
                rw [sm_add smA hsmA, sm_add smA hsmA, smC smA hsmA, smK smA hsmA, smK smA hsmA, hsmA]
                simp only [hsmA])
      _ = _ := by
        simp only [sumTo_add, sumTo_const]
        rw [Nat.mul_assoc K (K ^ n * εB)]
  have hfin := Nat.mul_le_mul_left K s1
  rw [Nat.mul_add] at hfin
  refine Nat.le_trans hfin ?_
  have hd : K * (K * (K ^ n * smA (fun xa => smB (fun xb => col xa xb)))) ≤ K * (K * (K ^ n * δ)) :=
    Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hcol))
  have := Nat.add_le_add_right (Nat.le_trans s2 (Nat.add_le_add_left hd _)) (K * (K ^ n * εA * smB (fun _ => 1)))
  exact this

/-- **The collision count from the second message's spread**: where no
    message value takes more than `δ₀` of the second proof's randomness (a
    salted commitment's spread over its salts), the pairs hitting the first
    simulated message are at most `δ₀` per first randomness. -/
theorem col_spread {XA XB : Type} {δ₀ : Nat} (smA : (XA → Nat) → Nat)
    (hsmA : ∀ (N : Nat) (f : Nat → XA → Nat), smA (fun x => sumTo N (fun i => f i x)) = sumTo N (fun i => smA (f i)))
    (smB : (XB → Nat) → Nat) (mB : XB → Nat) (sA : XA → Nat)
    (hsp : ∀ v, smB (fun xb => indB (decide (mB xb = v))) ≤ δ₀) :
    smA (fun xa => smB (fun xb => indB (decide (mB xb = sA xa)))) ≤ δ₀ * smA (fun _ => 1) := by
  rw [← smC smA hsmA]
  exact sm_mono smA hsmA (fun xa => hsp (sA xa))

end Circuit
