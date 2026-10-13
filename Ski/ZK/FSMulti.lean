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
per proof, one table; the statements and witnesses fixed in advance (not
chosen after seeing the oracle or the other proof).  Normalized, the
error is `εA/(K|A|) + εB/(K|B|) + δ/(|A||B|)`.

The same hybrid over any number of rounds and tables (`fs_two`): each
proof's own bound against every event of the tables and its view, and the
second proof's real view on the first's programmed tables equal to its view
on the tables themselves unless its messages hit the first's programmed
answers.  Over `fs_open4`, two four-round proofs on the same four tables
(`fs_open4_abs`, `fs_open4_two`): every round's message carries the first
commitment as its low digits, so a collision in any round puts the second
proof's first commitment at the first's simulated one, which the
commitment's spread over its salts bounds.
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

/-- A count over a finite set: it commutes with finite sums. -/
def Lin {X : Type} (sm : (X → Nat) → Nat) : Prop :=
  ∀ (N : Nat) (f : Nat → X → Nat), sm (fun x => sumTo N (fun i => f i x)) = sumTo N (fun i => sm (f i))

/-- Two counts commute (Fubini). -/
def Comm {X Y : Type} (sx : (X → Nat) → Nat) (sy : (Y → Nat) → Nat) : Prop :=
  ∀ f : X → Y → Nat, sy (fun y => sx (fun x => f x y)) = sx (fun x => sy (fun y => f x y))

/-- **Two proofs under shared oracle tables**, each of any number of rounds:
    the tables `T` counted by `ST`; proof A with randomness counted by
    `smA`, real view `rvA H xa` read from the tables, simulator challenges
    counted by `SCA`, its programming `pgA H ca xa` and view `svA ca xa`;
    the same for B.  Each proof's own bound against every event of the
    tables and its view (`hA`, `hB`).  The second proof's real view on the
    first's programmed tables is its view on the tables themselves unless
    its messages hit the first's programmed answers (`col`, `hread`).  The
    real count with both proofs reading the tables is within both errors
    and the collisions of the simulators', B programmed and then A. -/
theorem fs_two {T XA XB CA CB VA VB : Type} {KA KB εA εB : Nat}
    (ST : (T → Nat) → Nat) (hST : Lin ST)
    (smA : (XA → Nat) → Nat) (hsA : Lin smA) (smB : (XB → Nat) → Nat) (hsB : Lin smB)
    (SCA : (CA → Nat) → Nat) (hcA : Lin SCA) (SCB : (CB → Nat) → Nat)
    (c1 : Comm smA smB) (c2 : Comm ST smB) (c3 : Comm SCA smB) (c4 : Comm ST SCA) (c5 : Comm ST smA)
    (rvA : T → XA → VA) (pgA : T → CA → XA → T) (svA : CA → XA → VA)
    (rvB : T → XB → VB) (pgB : T → CB → XB → T) (svB : CB → XB → VB)
    (hA : ∀ E : T → VA → Bool, KA * ST (fun H => smA (fun x => indB (E H (rvA H x)))) ≤
      ST (fun H => SCA (fun c => smA (fun x => indB (E (pgA H c x) (svA c x))))) + εA)
    (hB : ∀ E : T → VB → Bool, KB * ST (fun H => smB (fun x => indB (E H (rvB H x)))) ≤
      ST (fun H => SCB (fun c => smB (fun x => indB (E (pgB H c x) (svB c x))))) + εB)
    (col : T → CA → XA → XB → Bool) (okA : CA → Bool)
    (hokA : ∀ f g : CA → Nat, (∀ c, okA c = true → f c ≤ g c) → SCA f ≤ SCA g)
    (hread : ∀ H ca xa xb, okA ca = true → col H ca xa xb = false → rvB (pgA H ca xa) xb = rvB H xb)
    (E : T → VA → VB → Bool) :
    KB * (KA * ST (fun H => smB (fun xb => smA (fun xa => indB (E H (rvA H xa) (rvB H xb)))))) ≤
      SCA (fun ca => smA (fun xa => ST (fun H => SCB (fun cb => smB (fun xb =>
        indB (E (pgA (pgB H cb xb) ca xa) (svA ca xa) (svB cb xb))))))) +
      KB * (εA * smB (fun _ => 1)) + εB * SCA (fun _ => smA (fun _ => 1)) +
      KB * SCA (fun ca => smA (fun xa => ST (fun H => smB (fun xb => indB (col H ca xa xb))))) := by
  -- the first proof simulated, the second real on the programmed tables
  have s1 : KA * ST (fun H => smB (fun xb => smA (fun xa => indB (E H (rvA H xa) (rvB H xb))))) ≤
      smB (fun xb => ST (fun H => SCA (fun ca => smA (fun xa =>
        indB (E (pgA H ca xa) (svA ca xa) (rvB (pgA H ca xa) xb)))))) + εA * smB (fun _ => 1) := by
    rw [← c2 (fun H xb => smA (fun xa => indB (E H (rvA H xa) (rvB H xb)))), ← smK smB hsB]
    refine Nat.le_trans (sm_mono smB hsB (fun xb => hA (fun H v => E H v (rvB H xb)))) (Nat.le_of_eq ?_)
    rw [sm_add smB hsB, smC smB hsB]
  -- the second proof's reads off the first's programming, but for collisions
  have hpt : ∀ H ca xa xb, okA ca = true → indB (E (pgA H ca xa) (svA ca xa) (rvB (pgA H ca xa) xb)) ≤
      indB (E (pgA H ca xa) (svA ca xa) (rvB H xb)) + indB (col H ca xa xb) := fun H ca xa xb hok => by
    cases hc : col H ca xa xb
    · rw [hread H ca xa xb hok hc]; exact Nat.le_add_right _ _
    · exact Nat.le_trans (indB_le _) (Nat.le_add_left _ _)
  let g2 := fun (H : T) (ca : CA) (xa : XA) (xb : XB) => indB (E (pgA H ca xa) (svA ca xa) (rvB H xb))
  let cl := fun (H : T) (ca : CA) (xa : XA) (xb : XB) => indB (col H ca xa xb)
  let sim := fun (H : T) (ca : CA) (xa : XA) (cb : CB) (xb : XB) =>
    indB (E (pgA (pgB H cb xb) ca xa) (svA ca xa) (svB cb xb))
  have s2 : smB (fun xb => ST (fun H => SCA (fun ca => smA (fun xa =>
        indB (E (pgA H ca xa) (svA ca xa) (rvB (pgA H ca xa) xb)))))) ≤
      SCA (fun ca => smA (fun xa => ST (fun H => smB (fun xb => g2 H ca xa xb + cl H ca xa xb)))) := by
    refine Nat.le_trans (sm_mono smB hsB (fun xb => sm_mono ST hST (fun H => hokA _ _ (fun ca hok =>
      sm_mono smA hsA (fun xa => hpt H ca xa xb hok))))) (Nat.le_of_eq ?_)
    calc smB (fun xb => ST (fun H => SCA (fun ca => smA (fun xa => g2 H ca xa xb + cl H ca xa xb))))
        = ST (fun H => smB (fun xb => SCA (fun ca => smA (fun xa => g2 H ca xa xb + cl H ca xa xb)))) :=
          c2 (fun H xb => SCA (fun ca => smA (fun xa => g2 H ca xa xb + cl H ca xa xb)))
      _ = ST (fun H => SCA (fun ca => smB (fun xb => smA (fun xa => g2 H ca xa xb + cl H ca xa xb)))) :=
          congrArg ST (funext fun H => c3 (fun ca xb => smA (fun xa => g2 H ca xa xb + cl H ca xa xb)))
      _ = ST (fun H => SCA (fun ca => smA (fun xa => smB (fun xb => g2 H ca xa xb + cl H ca xa xb)))) :=
          congrArg ST (funext fun H => congrArg SCA (funext fun ca => c1 (fun xa xb => g2 H ca xa xb + cl H ca xa xb)))
      _ = SCA (fun ca => ST (fun H => smA (fun xa => smB (fun xb => g2 H ca xa xb + cl H ca xa xb)))) :=
          (c4 (fun H ca => smA (fun xa => smB (fun xb => g2 H ca xa xb + cl H ca xa xb)))).symm
      _ = _ := congrArg SCA (funext fun ca => (c5 (fun H xa => smB (fun xb => g2 H ca xa xb + cl H ca xa xb))).symm)
  have s3 : KB * SCA (fun ca => smA (fun xa => ST (fun H => smB (fun xb => g2 H ca xa xb + cl H ca xa xb)))) ≤
      SCA (fun ca => smA (fun xa => ST (fun H => SCB (fun cb => smB (fun xb => sim H ca xa cb xb))))) +
      εB * SCA (fun _ => smA (fun _ => 1)) +
      KB * SCA (fun ca => smA (fun xa => ST (fun H => smB (fun xb => cl H ca xa xb)))) := by
    have hpc : ∀ ca xa, KB * ST (fun H => smB (fun xb => g2 H ca xa xb + cl H ca xa xb)) ≤
        ST (fun H => SCB (fun cb => smB (fun xb => sim H ca xa cb xb))) + εB +
          KB * ST (fun H => smB (fun xb => cl H ca xa xb)) := fun ca xa => by
      have e : ST (fun H => smB (fun xb => g2 H ca xa xb + cl H ca xa xb)) =
          ST (fun H => smB (fun xb => g2 H ca xa xb)) + ST (fun H => smB (fun xb => cl H ca xa xb)) := by
        rw [← sm_add ST hST]; exact congrArg ST (funext fun H => sm_add smB hsB _ _)
      rw [e, Nat.mul_add]
      exact Nat.add_le_add_right (hB (fun H v => E (pgA H ca xa) (svA ca xa) v)) _
    calc KB * SCA (fun ca => smA (fun xa => ST (fun H => smB (fun xb => g2 H ca xa xb + cl H ca xa xb))))
        = SCA (fun ca => smA (fun xa => KB * ST (fun H => smB (fun xb => g2 H ca xa xb + cl H ca xa xb)))) := by
          rw [← smK SCA hcA]; exact congrArg SCA (funext fun ca => (smK smA hsA _ _).symm)
      _ ≤ SCA (fun ca => smA (fun xa => ST (fun H => SCB (fun cb => smB (fun xb => sim H ca xa cb xb))) + εB +
            KB * ST (fun H => smB (fun xb => cl H ca xa xb)))) :=
          sm_mono SCA hcA (fun ca => sm_mono smA hsA (fun xa => hpc ca xa))
      _ = _ := by
        have e1 : ∀ ca, smA (fun xa => ST (fun H => SCB (fun cb => smB (fun xb => sim H ca xa cb xb))) + εB +
            KB * ST (fun H => smB (fun xb => cl H ca xa xb))) =
            smA (fun xa => ST (fun H => SCB (fun cb => smB (fun xb => sim H ca xa cb xb)))) + εB * smA (fun _ => 1) +
              KB * smA (fun xa => ST (fun H => smB (fun xb => cl H ca xa xb))) := fun ca => by
          rw [sm_add smA hsA, sm_add smA hsA, smC smA hsA, smK smA hsA]
        rw [congrArg SCA (funext e1), sm_add SCA hcA, sm_add SCA hcA, smK SCA hcA, smK SCA hcA]
  calc KB * (KA * ST (fun H => smB (fun xb => smA (fun xa => indB (E H (rvA H xa) (rvB H xb))))))
      ≤ KB * (SCA (fun ca => smA (fun xa => ST (fun H => smB (fun xb => g2 H ca xa xb + cl H ca xa xb)))) +
          εA * smB (fun _ => 1)) := Nat.mul_le_mul_left _ (Nat.le_trans s1 (Nat.add_le_add_right s2 _))
    _ ≤ _ := by
      rw [Nat.mul_add]
      have := Nat.add_le_add_right s3 (KB * (εA * smB (fun _ => 1)))
      refine Nat.le_trans this (Nat.le_of_eq ?_)
      ac_rfl
theorem lin_sumN {Y : Type} {sy : (Y → Nat) → Nat} (h : Lin sy) :
    ∀ (m : Nat) (g : (Nat → Tup) → Y → Nat), sy (fun y => sumN m (fun t => g t y)) = sumN m (fun t => sy (g t))
  | 0, _ => rfl
  | m + 1, g => by
    show sy (fun y => sumTo Q4 (fun i => sumN m (fun t => g (updT t m (Tup.dec i)) y))) =
      sumTo Q4 (fun i => sumN m (fun t => sy (g (updT t m (Tup.dec i)))))
    rw [h]
    exact sumTo_congr _ (fun i _ => lin_sumN h m _)

theorem lin_sumTo (N : Nat) : Lin (fun f : Nat → Nat => sumTo N f) := fun M f => sumTo_exch _ M N

theorem lin_sm (NS1 NS2 NR m : Nat) :
    Lin (fun (g : Nat × Nat × Nat × (Nat → Tup) → Nat) =>
      sumTo NS1 (fun σ1 => sumTo NS2 (fun σ => sumTo NR (fun r => sumN m (fun t => g (σ1, σ, r, t)))))) :=
  fun N f => by
    show sumTo NS1 (fun σ1 => sumTo NS2 (fun σ => sumTo NR (fun r => sumN m (fun t =>
      sumTo N (fun i => f i (σ1, σ, r, t)))))) = _
    rw [sumTo_congr _ (fun σ1 _ => sm_exch (NS := NS2) (NR := NR) (m := m) (N := N) (fun i σ r t => f i (σ1, σ, r, t)))]
    exact sumTo_exch _ N NS1

/-- A count commutes with every count built from `sumTo` and `sumN`. -/
theorem comm_sm {Y : Type} {sy : (Y → Nat) → Nat} (h : Lin sy) (NS1 NS2 NR m : Nat) :
    Comm (fun (g : Nat × Nat × Nat × (Nat → Tup) → Nat) =>
      sumTo NS1 (fun σ1 => sumTo NS2 (fun σ => sumTo NR (fun r => sumN m (fun t => g (σ1, σ, r, t)))))) sy :=
  fun f => by
    show sy (fun y => sumTo NS1 (fun σ1 => sumTo NS2 (fun σ => sumTo NR (fun r => sumN m (fun t =>
      f (σ1, σ, r, t) y))))) = _
    rw [h]; refine sumTo_congr _ (fun σ1 _ => ?_)
    rw [h]; refine sumTo_congr _ (fun σ _ => ?_)
    rw [h]; refine sumTo_congr _ (fun r _ => ?_)
    exact lin_sumN h m _

theorem comm_sum4 {Y : Type} {sy : (Y → Nat) → Nat} (h : Lin sy) (A B C D : Nat) :
    Comm (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo D (fun d => sumTo A (fun a =>
      sumTo B (fun b => sumTo C (fun c => f (a, b, c, d)))))) sy := fun f => by
  show sy (fun y => sumTo D (fun d => sumTo A (fun a => sumTo B (fun b => sumTo C (fun c => f (a, b, c, d) y))))) = _
  rw [h]; refine sumTo_congr _ (fun d _ => ?_)
  rw [h]; refine sumTo_congr _ (fun a _ => ?_)
  rw [h]; refine sumTo_congr _ (fun b _ => ?_)
  rw [h]

theorem lin_sum4 (A B C D : Nat) : Lin (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo D (fun d => sumTo A (fun a =>
      sumTo B (fun b => sumTo C (fun c => f (a, b, c, d)))))) := fun N f =>
  (comm_sum4 (lin_sumTo N) A B C D (fun x i => f i x)).symm
/-- **`fs_open4` in `fs_two`'s shape**: the four tables one, counted by `ST`,
    the four challenges one, counted by `SC`; the real view reads the
    tables, the simulator programs them. -/
theorem fs_open4_abs {PV PB D1 O1 P1 D2 O2 P2 D3 O3 P3 W : Type} {NR m e1 e2 NS1 NS2 NS3 K2 K3 K4 n1 n2 n3 : Nat}
    (hK2 : 0 < K2) (hK3 : 0 < K3) (hK4 : 0 < K4)
    (φ : Nat → W → Nat) {N4 : Nat} (hφ : ∀ m w, φ m w < N4)
    (rv sv : Nat → Nat → Nat → EF → EF → Nat → (Nat → Tup) → TViewN PV PB) (gz : Nat → Nat → Bool)
    {Bz : Nat} (hgz : sumTo K2 (fun c2 => sumTo K3 (fun c3 => indB (!gz c2 c3))) ≤ Bz)
    (g4 : Nat → Bool) {B4 : Nat} (hB4 : sumTo K4 (fun c4 => indB (!g4 c4)) ≤ B4)
    (hrv : ∀ c4 c2 c3 α β r t, rv c4 c2 c3 α β r t = none ∨ ∃ p x y, rv c4 c2 c3 α β r t = some (p, α, β, x, y))
    (hsv : ∀ c4 c2 c3 α β r t, ∃ p x y, sv c4 c2 c3 α β r t = some (p, α, β, x, y))
    (oz : TViewN PV PB → W) (hoz : ∀ c4 c2 c3 α β r t, oz (rv c4 c2 c3 α β r t) = oz (rv 0 c2 c3 α β r t))
    (h1 : ∀ c4 c2 c3, g4 c4 = true → gz c2 c3 = true → ∀ E : TViewN PV PB → Bool,
      tsumN NR m (fun α β r t => indB (genB β && E (rv c4 c2 c3 α β r t))) ≤
        tsumN NR m (fun α β r t => indB (genB β && E (sv c4 c2 c3 α β r t))) + e1 + e2)
    (h2 : ∀ c4 c2 c3, g4 c4 = true → gz c2 c3 = true → ∀ E : TViewN PV PB → Bool,
      tsumN NR m (fun α β r t => indB (genB β && E (sv c4 c2 c3 α β r t))) ≤
        tsumN NR m (fun α β r t => indB (genB β && E (rv c4 c2 c3 α β r t))) + e1 + e2)
    (Com1 : D1 → Nat → Nat) (Pf1 : Nat → D1 → Nat → P1) (op1 : Nat → D1 → O1) (sd1 : Nat → O1 → D1) (d1 : D1)
    (hc1 : ComHides NS1 Com1) (hp1 : ∀ c4, ComPfHides NS1 Com1 (Pf1 c4) (op1 c4)) (hr1 : ∀ d σ, Com1 d σ < n1)
    (ov1 : Nat → TViewN PV PB → Option O1) (hov1 : ∀ c4, ov1 c4 none = none) (main1 : (Nat → Tup) → Nat → D1)
    (hsd1 : ∀ c4 t r, op1 c4 (sd1 c4 (op1 c4 (main1 t r))) = op1 c4 (main1 t r))
    (Com2 : D2 → Nat → Nat) (Pf2 : Nat → D2 → Nat → P2) (op2 : Nat → D2 → O2) (sd2 : Nat → O2 → D2) (d2 : D2)
    (hc2 : ComHides NS2 Com2) (hp2 : ∀ c4, ComPfHides NS2 Com2 (Pf2 c4) (op2 c4)) (hr2 : ∀ d σ, Com2 d σ < n2)
    (ov2 : Nat → TViewN PV PB → Option O2) (hov2 : ∀ c4, ov2 c4 none = none) (main2 : Nat → (Nat → Tup) → Nat → D2)
    (hsd2 : ∀ c4 c t r, op2 c4 (sd2 c4 (op2 c4 (main2 c t r))) = op2 c4 (main2 c t r))
    (Com3 : D3 → Nat → Nat) (Pf3 : Nat → D3 → Nat → P3) (op3 : Nat → D3 → O3) (sd3 : Nat → O3 → D3) (d3 : D3)
    (hc3 : ComHides NS3 Com3) (hp3 : ∀ c4, ComPfHides NS3 Com3 (Pf3 c4) (op3 c4)) (hr3 : ∀ d σ, Com3 d σ < n3)
    (ov3 : Nat → TViewN PV PB → Option O3) (hov3 : ∀ c4, ov3 c4 none = none) (main3 : Nat → Nat → (Nat → Tup) → Nat → D3)
    (hsd3 : ∀ c4 c c' t r, op3 c4 (sd3 c4 (op3 c4 (main3 c c' t r))) = op3 c4 (main3 c c' t r))
    (hvo1 : ∀ c4 c2 c3 c r t, rv c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t = none ∨
      ov1 c4 (rv c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (op1 c4 (main1 t r)))
    (hvo2 : ∀ c4 c2 c3 c r t, rv c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t = none ∨
      ov2 c4 (rv c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (op2 c4 (main2 c t r)))
    (hvo3 : ∀ c4 c2 c3 c r t, rv c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t = none ∨
      ov3 c4 (rv c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (op3 c4 (main3 c c2 t r)))
    (sop1 : Nat → Nat → Nat → Nat → (Nat → Tup) → O1) (sop2 : Nat → Nat → Nat → Nat → Nat → (Nat → Tup) → O2)
    (sop3 : Nat → Nat → Nat → Nat → Nat → (Nat → Tup) → O3)
    (hsvo1 : ∀ c4 c2 c3 c r t, ov1 c4 (sv c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (sop1 c4 c2 c3 r t))
    (hsvo2 : ∀ c4 c2 c3 c r t, ov2 c4 (sv c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (sop2 c4 c2 c3 c r t))
    (hsvo3 : ∀ c4 c2 c3 c r t, ov3 c4 (sv c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (sop3 c4 c2 c3 c r t)) :
    let sm := fun (g : Nat × Nat × Nat × (Nat → Tup) → Nat) =>
      sumTo NS1 (fun σ1 => sumTo (NS2 * NS3) (fun σ => sumTo NR (fun r => sumN m (fun t => g (σ1, σ, r, t)))))
    let m1 := fun (x : Nat × Nat × Nat × (Nat → Tup)) => Com1 (main1 x.2.2.2 x.2.2.1) x.1
    let m2 := fun (c1 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      m1 x + n1 * Com2 (main2 c1 x.2.2.2 x.2.2.1) (x.2.1 % NS2)
    let m3 := fun (c1 c2 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      m1 x + n1 * comPair NS2 n2 Com2 Com3 (main2 c1 x.2.2.2 x.2.2.1, main3 c1 c2 x.2.2.2 x.2.2.1) x.2.1
    let rvo := fun (c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      ((ov1 c4 (rv c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)).map (fun _ => Pf1 c4 (main1 x.2.2.2 x.2.2.1) x.1),
       (ovPair (ov2 c4) (ov3 c4) (rv c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)).map
         (fun _ => pfPair NS2 (Pf2 c4) (Pf3 c4) (main2 c1 x.2.2.2 x.2.2.1, main3 c1 c2 x.2.2.2 x.2.2.1) x.2.1),
       rv c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)
    let s1 := fun (c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) => Com1 (sd1 c4 (sop1 c4 c2 c3 x.2.2.1 x.2.2.2)) x.1
    let s2 := fun (c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      s1 c4 c1 c2 c3 x + n1 * Com2 (sd2 c4 (sop2 c4 c2 c3 c1 x.2.2.1 x.2.2.2)) (x.2.1 % NS2)
    let s3 := fun (c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      s1 c4 c1 c2 c3 x + n1 * comPair NS2 n2 Com2 Com3
        (sd2 c4 (sop2 c4 c2 c3 c1 x.2.2.1 x.2.2.2), sd3 c4 (sop3 c4 c2 c3 c1 x.2.2.1 x.2.2.2)) x.2.1
    let svo := fun (c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      (some (Pf1 c4 (sd1 c4 (sop1 c4 c2 c3 x.2.2.1 x.2.2.2)) x.1),
       some (pfPair NS2 (Pf2 c4) (Pf3 c4) (sd2 c4 (sop2 c4 c2 c3 c1 x.2.2.1 x.2.2.2), sd3 c4 (sop3 c4 c2 c3 c1 x.2.2.1 x.2.2.2)) x.2.1),
       sv c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)
    let sm4 := fun (g : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup)) → Nat) =>
      sumTo ((Q4 * Q4) ^ n1) (fun H1 => sumTo (K2 ^ (n1 * n2)) (fun H2 =>
        sumTo (K3 ^ (n1 * (n2 * n3))) (fun H3 => sm (fun x => g (H1, H2, H3, x)))))
    let r1 := fun (y : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup))) => rget (Q4 * Q4) (m1 y.2.2.2) y.1
    let r2 := fun (y : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup))) => rget K2 (m2 (r1 y) y.2.2.2) y.2.1
    let r3 := fun (y : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup))) => rget K3 (m3 (r1 y) (r2 y) y.2.2.2) y.2.2.1
    let Mq := fun (y : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup))) => φ (m3 (r1 y) (r2 y) y.2.2.2)
      (oz (rv 0 (r2 y) (r3 y) (efOf (r1 y / Q4)) (efOf (r1 y % Q4)) y.2.2.2.2.2.1 y.2.2.2.2.2.2))
    let ST := fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo (K4 ^ N4) (fun H4 => sumTo ((Q4 * Q4) ^ n1) (fun H1 =>
      sumTo (K2 ^ (n1 * n2)) (fun H2 => sumTo (K3 ^ (n1 * (n2 * n3))) (fun H3 => f (H1, H2, H3, H4)))))
    let SC := fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo K4 (fun c4 => sumTo (Q4 * Q4) (fun c1 =>
      sumTo K2 (fun c2 => sumTo K3 (fun c3 => f (c1, c2, c3, c4)))))
    let rvT := fun (H : Nat × Nat × Nat × Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      (m1 x, m2 (r1 (H.1, H.2.1, H.2.2.1, x)) x, m3 (r1 (H.1, H.2.1, H.2.2.1, x)) (r2 (H.1, H.2.1, H.2.2.1, x)) x,
       rvo (rget K4 (Mq (H.1, H.2.1, H.2.2.1, x)) H.2.2.2) (r1 (H.1, H.2.1, H.2.2.1, x)) (r2 (H.1, H.2.1, H.2.2.1, x))
         (r3 (H.1, H.2.1, H.2.2.1, x)) x)
    let pgT := fun (H : Nat × Nat × Nat × Nat) (c : Nat × Nat × Nat × Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      (rset (Q4 * Q4) (s1 c.2.2.2 c.1 c.2.1 c.2.2.1 x) H.1 c.1, rset K2 (s2 c.2.2.2 c.1 c.2.1 c.2.2.1 x) H.2.1 c.2.1,
       rset K3 (s3 c.2.2.2 c.1 c.2.1 c.2.2.1 x) H.2.2.1 c.2.2.1,
       rset K4 (φ (s3 c.2.2.2 c.1 c.2.1 c.2.2.1 x) (oz (sv c.2.2.2 c.2.1 c.2.2.1 (efOf (c.1 / Q4)) (efOf (c.1 % Q4))
         x.2.2.1 x.2.2.2))) H.2.2.2 c.2.2.2)
    let svT := fun (c : Nat × Nat × Nat × Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      (s1 c.2.2.2 c.1 c.2.1 c.2.2.1 x, s2 c.2.2.2 c.1 c.2.1 c.2.2.1 x, s3 c.2.2.2 c.1 c.2.1 c.2.2.1 x,
       svo c.2.2.2 c.1 c.2.1 c.2.2.1 x)
    ∀ E : Nat × Nat × Nat × Nat → Nat × Nat × Nat × (Option P1 × Option (P2 × P3) × TViewN PV PB) → Bool,
    K4 * (Q4 * Q4 * (K2 * K3)) * ST (fun H => sm (fun x => indB (E H (rvT H x)))) ≤
    ST (fun H => SC (fun c => sm (fun x => indB (E (pgT H c x) (svT c x))))) +
      K4 ^ N4 * (K4 * ((Q4 * Q4) ^ n1 * (K2 ^ (n1 * n2) * (K3 ^ (n1 * (n2 * n3)) *
        (K2 * (K3 * (NS1 * (NS2 * NS3 * (e1 + e2)))) +
          (Q4 * (P * P) * (K2 * K3) + Q4 * Q4 * Bz) * (NS1 * (NS2 * NS3 * (NR * (Q4 ^ m * 1)))))))) +
          B4 * (Q4 * Q4 * (K2 * K3) * sm4 (fun _ => 1))) := by
  intro sm m1 m2 m3 rvo s1 s2 s3 svo sm4 r1 r2 r3 Mq ST SC rvT pgT svT E
  have h := fs_open4 hK2 hK3 hK4 φ hφ rv sv gz hgz g4 hB4 hrv hsv oz hoz h1 h2 Com1 Pf1 op1 sd1 d1 hc1 hp1 hr1 ov1 hov1 main1 hsd1 Com2 Pf2 op2 sd2 d2 hc2 hp2 hr2 ov2 hov2 main2 hsd2 Com3 Pf3 op3 sd3 d3 hc3 hp3 hr3 ov3 hov3 main3 hsd3 hvo1 hvo2 hvo3 sop1 sop2 sop3 hsvo1 hsvo2 hsvo3 (fun H1 H2 H3 H4 a b c v => E (H1, H2, H3, H4) (a, b, c, v))
  rw [Nat.mul_assoc]
  refine Nat.le_trans h (Nat.add_le_add_right (Nat.le_of_eq ?_) _)
  refine sumTo_congr _ (fun H4 _ => ?_)
  rw [sumTo_exch _ ((Q4 * Q4) ^ n1) K4]
  refine sumTo_congr _ (fun H1 _ => ?_)
  rw [sumTo_exch _ (K2 ^ (n1 * n2)) K4]
  refine sumTo_congr _ (fun H2 _ => ?_)
  rw [sumTo_exch _ (K3 ^ (n1 * (n2 * n3))) K4]

set_option maxRecDepth 100000 in
/-- **Two four-round proofs under shared oracle tables** (`fs_two` over
    `fs_open4_abs`): both proofs read the same four tables; the simulator
    programs the second's answers and then the first's.  The error is each
    proof's own over the other's draws and the draws where the second
    proof's real message in some round hits the first's programmed answer
    on that round's table (`colT`).  Every round's message carries the first
    commitment as its low digits, and `φ` keeps them (`hφ`), so a collision
    puts the second proof's first commitment at the first's simulated one;
    the commitment's spread over its salts, `δ₀` per draw (`hsp`), bounds
    it.  `hφ` restricts the query hash's input map: it must keep the
    transcript's residue mod `n1`, as `φ m w = m % n1 + n1 (g m w % M)` with
    `N4 = n1 M` does; a map that discards it falls outside. -/
theorem fs_open4_two {PVA PBA D1A O1A P1A D2A O2A P2A D3A O3A P3A WA : Type} {NRA mA e1A e2A NS1A NS2A NS3A K2 K3 K4 n1 n2 n3 : Nat}
    (hK2 : 0 < K2) (hK3 : 0 < K3) (hK4 : 0 < K4)
    (φA : Nat → WA → Nat) {N4 : Nat} (hφA : ∀ mA w, φA mA w < N4)
    (rvA svA : Nat → Nat → Nat → EF → EF → Nat → (Nat → Tup) → TViewN PVA PBA) (gzA : Nat → Nat → Bool)
    {BzA : Nat} (hgzA : sumTo K2 (fun c2 => sumTo K3 (fun c3 => indB (!gzA c2 c3))) ≤ BzA)
    (g4A : Nat → Bool) {B4A : Nat} (hB4A : sumTo K4 (fun c4 => indB (!g4A c4)) ≤ B4A)
    (hrvA : ∀ c4 c2 c3 α β r t, rvA c4 c2 c3 α β r t = none ∨ ∃ p x y, rvA c4 c2 c3 α β r t = some (p, α, β, x, y))
    (hsvA : ∀ c4 c2 c3 α β r t, ∃ p x y, svA c4 c2 c3 α β r t = some (p, α, β, x, y))
    (ozA : TViewN PVA PBA → WA) (hozA : ∀ c4 c2 c3 α β r t, ozA (rvA c4 c2 c3 α β r t) = ozA (rvA 0 c2 c3 α β r t))
    (h1A : ∀ c4 c2 c3, g4A c4 = true → gzA c2 c3 = true → ∀ E : TViewN PVA PBA → Bool,
      tsumN NRA mA (fun α β r t => indB (genB β && E (rvA c4 c2 c3 α β r t))) ≤
        tsumN NRA mA (fun α β r t => indB (genB β && E (svA c4 c2 c3 α β r t))) + e1A + e2A)
    (h2A : ∀ c4 c2 c3, g4A c4 = true → gzA c2 c3 = true → ∀ E : TViewN PVA PBA → Bool,
      tsumN NRA mA (fun α β r t => indB (genB β && E (svA c4 c2 c3 α β r t))) ≤
        tsumN NRA mA (fun α β r t => indB (genB β && E (rvA c4 c2 c3 α β r t))) + e1A + e2A)
    (Com1A : D1A → Nat → Nat) (Pf1A : Nat → D1A → Nat → P1A) (op1A : Nat → D1A → O1A) (sd1A : Nat → O1A → D1A) (d1A : D1A)
    (hc1A : ComHides NS1A Com1A) (hp1A : ∀ c4, ComPfHides NS1A Com1A (Pf1A c4) (op1A c4)) (hr1A : ∀ d σ, Com1A d σ < n1)
    (ov1A : Nat → TViewN PVA PBA → Option O1A) (hov1A : ∀ c4, ov1A c4 none = none) (main1A : (Nat → Tup) → Nat → D1A)
    (hsd1A : ∀ c4 t r, op1A c4 (sd1A c4 (op1A c4 (main1A t r))) = op1A c4 (main1A t r))
    (Com2A : D2A → Nat → Nat) (Pf2A : Nat → D2A → Nat → P2A) (op2A : Nat → D2A → O2A) (sd2A : Nat → O2A → D2A) (d2A : D2A)
    (hc2A : ComHides NS2A Com2A) (hp2A : ∀ c4, ComPfHides NS2A Com2A (Pf2A c4) (op2A c4)) (hr2A : ∀ d σ, Com2A d σ < n2)
    (ov2A : Nat → TViewN PVA PBA → Option O2A) (hov2A : ∀ c4, ov2A c4 none = none) (main2A : Nat → (Nat → Tup) → Nat → D2A)
    (hsd2A : ∀ c4 c t r, op2A c4 (sd2A c4 (op2A c4 (main2A c t r))) = op2A c4 (main2A c t r))
    (Com3A : D3A → Nat → Nat) (Pf3A : Nat → D3A → Nat → P3A) (op3A : Nat → D3A → O3A) (sd3A : Nat → O3A → D3A) (d3A : D3A)
    (hc3A : ComHides NS3A Com3A) (hp3A : ∀ c4, ComPfHides NS3A Com3A (Pf3A c4) (op3A c4)) (hr3A : ∀ d σ, Com3A d σ < n3)
    (ov3A : Nat → TViewN PVA PBA → Option O3A) (hov3A : ∀ c4, ov3A c4 none = none) (main3A : Nat → Nat → (Nat → Tup) → Nat → D3A)
    (hsd3A : ∀ c4 c c' t r, op3A c4 (sd3A c4 (op3A c4 (main3A c c' t r))) = op3A c4 (main3A c c' t r))
    (hvo1A : ∀ c4 c2 c3 c r t, rvA c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t = none ∨
      ov1A c4 (rvA c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (op1A c4 (main1A t r)))
    (hvo2A : ∀ c4 c2 c3 c r t, rvA c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t = none ∨
      ov2A c4 (rvA c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (op2A c4 (main2A c t r)))
    (hvo3A : ∀ c4 c2 c3 c r t, rvA c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t = none ∨
      ov3A c4 (rvA c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (op3A c4 (main3A c c2 t r)))
    (sop1A : Nat → Nat → Nat → Nat → (Nat → Tup) → O1A) (sop2A : Nat → Nat → Nat → Nat → Nat → (Nat → Tup) → O2A)
    (sop3A : Nat → Nat → Nat → Nat → Nat → (Nat → Tup) → O3A)
    (hsvo1A : ∀ c4 c2 c3 c r t, ov1A c4 (svA c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (sop1A c4 c2 c3 r t))
    (hsvo2A : ∀ c4 c2 c3 c r t, ov2A c4 (svA c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (sop2A c4 c2 c3 c r t))
    (hsvo3A : ∀ c4 c2 c3 c r t, ov3A c4 (svA c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (sop3A c4 c2 c3 c r t))
    {PVB PBB D1B O1B P1B D2B O2B P2B D3B O3B P3B WB : Type} {NRB mB e1B e2B NS1B NS2B NS3B : Nat}
    (φB : Nat → WB → Nat) (hφB : ∀ mB w, φB mB w < N4)
    (rvB svB : Nat → Nat → Nat → EF → EF → Nat → (Nat → Tup) → TViewN PVB PBB) (gzB : Nat → Nat → Bool)
    {BzB : Nat} (hgzB : sumTo K2 (fun c2 => sumTo K3 (fun c3 => indB (!gzB c2 c3))) ≤ BzB)
    (g4B : Nat → Bool) {B4B : Nat} (hB4B : sumTo K4 (fun c4 => indB (!g4B c4)) ≤ B4B)
    (hrvB : ∀ c4 c2 c3 α β r t, rvB c4 c2 c3 α β r t = none ∨ ∃ p x y, rvB c4 c2 c3 α β r t = some (p, α, β, x, y))
    (hsvB : ∀ c4 c2 c3 α β r t, ∃ p x y, svB c4 c2 c3 α β r t = some (p, α, β, x, y))
    (ozB : TViewN PVB PBB → WB) (hozB : ∀ c4 c2 c3 α β r t, ozB (rvB c4 c2 c3 α β r t) = ozB (rvB 0 c2 c3 α β r t))
    (h1B : ∀ c4 c2 c3, g4B c4 = true → gzB c2 c3 = true → ∀ E : TViewN PVB PBB → Bool,
      tsumN NRB mB (fun α β r t => indB (genB β && E (rvB c4 c2 c3 α β r t))) ≤
        tsumN NRB mB (fun α β r t => indB (genB β && E (svB c4 c2 c3 α β r t))) + e1B + e2B)
    (h2B : ∀ c4 c2 c3, g4B c4 = true → gzB c2 c3 = true → ∀ E : TViewN PVB PBB → Bool,
      tsumN NRB mB (fun α β r t => indB (genB β && E (svB c4 c2 c3 α β r t))) ≤
        tsumN NRB mB (fun α β r t => indB (genB β && E (rvB c4 c2 c3 α β r t))) + e1B + e2B)
    (Com1B : D1B → Nat → Nat) (Pf1B : Nat → D1B → Nat → P1B) (op1B : Nat → D1B → O1B) (sd1B : Nat → O1B → D1B) (d1B : D1B)
    (hc1B : ComHides NS1B Com1B) (hp1B : ∀ c4, ComPfHides NS1B Com1B (Pf1B c4) (op1B c4)) (hr1B : ∀ d σ, Com1B d σ < n1)
    (ov1B : Nat → TViewN PVB PBB → Option O1B) (hov1B : ∀ c4, ov1B c4 none = none) (main1B : (Nat → Tup) → Nat → D1B)
    (hsd1B : ∀ c4 t r, op1B c4 (sd1B c4 (op1B c4 (main1B t r))) = op1B c4 (main1B t r))
    (Com2B : D2B → Nat → Nat) (Pf2B : Nat → D2B → Nat → P2B) (op2B : Nat → D2B → O2B) (sd2B : Nat → O2B → D2B) (d2B : D2B)
    (hc2B : ComHides NS2B Com2B) (hp2B : ∀ c4, ComPfHides NS2B Com2B (Pf2B c4) (op2B c4)) (hr2B : ∀ d σ, Com2B d σ < n2)
    (ov2B : Nat → TViewN PVB PBB → Option O2B) (hov2B : ∀ c4, ov2B c4 none = none) (main2B : Nat → (Nat → Tup) → Nat → D2B)
    (hsd2B : ∀ c4 c t r, op2B c4 (sd2B c4 (op2B c4 (main2B c t r))) = op2B c4 (main2B c t r))
    (Com3B : D3B → Nat → Nat) (Pf3B : Nat → D3B → Nat → P3B) (op3B : Nat → D3B → O3B) (sd3B : Nat → O3B → D3B) (d3B : D3B)
    (hc3B : ComHides NS3B Com3B) (hp3B : ∀ c4, ComPfHides NS3B Com3B (Pf3B c4) (op3B c4)) (hr3B : ∀ d σ, Com3B d σ < n3)
    (ov3B : Nat → TViewN PVB PBB → Option O3B) (hov3B : ∀ c4, ov3B c4 none = none) (main3B : Nat → Nat → (Nat → Tup) → Nat → D3B)
    (hsd3B : ∀ c4 c c' t r, op3B c4 (sd3B c4 (op3B c4 (main3B c c' t r))) = op3B c4 (main3B c c' t r))
    (hvo1B : ∀ c4 c2 c3 c r t, rvB c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t = none ∨
      ov1B c4 (rvB c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (op1B c4 (main1B t r)))
    (hvo2B : ∀ c4 c2 c3 c r t, rvB c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t = none ∨
      ov2B c4 (rvB c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (op2B c4 (main2B c t r)))
    (hvo3B : ∀ c4 c2 c3 c r t, rvB c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t = none ∨
      ov3B c4 (rvB c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (op3B c4 (main3B c c2 t r)))
    (sop1B : Nat → Nat → Nat → Nat → (Nat → Tup) → O1B) (sop2B : Nat → Nat → Nat → Nat → Nat → (Nat → Tup) → O2B)
    (sop3B : Nat → Nat → Nat → Nat → Nat → (Nat → Tup) → O3B)
    (hsvo1B : ∀ c4 c2 c3 c r t, ov1B c4 (svB c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (sop1B c4 c2 c3 r t))
    (hsvo2B : ∀ c4 c2 c3 c r t, ov2B c4 (svB c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (sop2B c4 c2 c3 c r t))
    (hsvo3B : ∀ c4 c2 c3 c r t, ov3B c4 (svB c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (sop3B c4 c2 c3 c r t))
    (hφ : ∀ m w m' w', φB m w = φA m' w' → m % n1 = m' % n1) {δ₀ : Nat}
    (hsp : ∀ v, sumTo NS1B (fun σ1 => sumTo (NS2B * NS3B) (fun σ => sumTo NRB (fun r => sumN mB (fun t =>
      indB (decide (Com1B (main1B t r) σ1 = v)))))) ≤ δ₀) :
    let smA := fun (g : Nat × Nat × Nat × (Nat → Tup) → Nat) =>
      sumTo NS1A (fun σ1 => sumTo (NS2A * NS3A) (fun σ => sumTo NRA (fun r => sumN mA (fun t => g (σ1, σ, r, t)))))
    let m1A := fun (x : Nat × Nat × Nat × (Nat → Tup)) => Com1A (main1A x.2.2.2 x.2.2.1) x.1
    let m2A := fun (c1 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      m1A x + n1 * Com2A (main2A c1 x.2.2.2 x.2.2.1) (x.2.1 % NS2A)
    let m3A := fun (c1 c2 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      m1A x + n1 * comPair NS2A n2 Com2A Com3A (main2A c1 x.2.2.2 x.2.2.1, main3A c1 c2 x.2.2.2 x.2.2.1) x.2.1
    let rvoA := fun (c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      ((ov1A c4 (rvA c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)).map (fun _ => Pf1A c4 (main1A x.2.2.2 x.2.2.1) x.1),
       (ovPair (ov2A c4) (ov3A c4) (rvA c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)).map
         (fun _ => pfPair NS2A (Pf2A c4) (Pf3A c4) (main2A c1 x.2.2.2 x.2.2.1, main3A c1 c2 x.2.2.2 x.2.2.1) x.2.1),
       rvA c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)
    let s1A := fun (c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) => Com1A (sd1A c4 (sop1A c4 c2 c3 x.2.2.1 x.2.2.2)) x.1
    let s2A := fun (c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      s1A c4 c1 c2 c3 x + n1 * Com2A (sd2A c4 (sop2A c4 c2 c3 c1 x.2.2.1 x.2.2.2)) (x.2.1 % NS2A)
    let s3A := fun (c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      s1A c4 c1 c2 c3 x + n1 * comPair NS2A n2 Com2A Com3A
        (sd2A c4 (sop2A c4 c2 c3 c1 x.2.2.1 x.2.2.2), sd3A c4 (sop3A c4 c2 c3 c1 x.2.2.1 x.2.2.2)) x.2.1
    let svoA := fun (c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      (some (Pf1A c4 (sd1A c4 (sop1A c4 c2 c3 x.2.2.1 x.2.2.2)) x.1),
       some (pfPair NS2A (Pf2A c4) (Pf3A c4) (sd2A c4 (sop2A c4 c2 c3 c1 x.2.2.1 x.2.2.2), sd3A c4 (sop3A c4 c2 c3 c1 x.2.2.1 x.2.2.2)) x.2.1),
       svA c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)
    let sm4A := fun (g : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup)) → Nat) =>
      sumTo ((Q4 * Q4) ^ n1) (fun H1 => sumTo (K2 ^ (n1 * n2)) (fun H2 =>
        sumTo (K3 ^ (n1 * (n2 * n3))) (fun H3 => smA (fun x => g (H1, H2, H3, x)))))
    let r1A := fun (y : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup))) => rget (Q4 * Q4) (m1A y.2.2.2) y.1
    let r2A := fun (y : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup))) => rget K2 (m2A (r1A y) y.2.2.2) y.2.1
    let r3A := fun (y : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup))) => rget K3 (m3A (r1A y) (r2A y) y.2.2.2) y.2.2.1
    let MqA := fun (y : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup))) => φA (m3A (r1A y) (r2A y) y.2.2.2)
      (ozA (rvA 0 (r2A y) (r3A y) (efOf (r1A y / Q4)) (efOf (r1A y % Q4)) y.2.2.2.2.2.1 y.2.2.2.2.2.2))
    let smB := fun (g : Nat × Nat × Nat × (Nat → Tup) → Nat) =>
      sumTo NS1B (fun σ1 => sumTo (NS2B * NS3B) (fun σ => sumTo NRB (fun r => sumN mB (fun t => g (σ1, σ, r, t)))))
    let m1B := fun (x : Nat × Nat × Nat × (Nat → Tup)) => Com1B (main1B x.2.2.2 x.2.2.1) x.1
    let m2B := fun (c1 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      m1B x + n1 * Com2B (main2B c1 x.2.2.2 x.2.2.1) (x.2.1 % NS2B)
    let m3B := fun (c1 c2 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      m1B x + n1 * comPair NS2B n2 Com2B Com3B (main2B c1 x.2.2.2 x.2.2.1, main3B c1 c2 x.2.2.2 x.2.2.1) x.2.1
    let rvoB := fun (c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      ((ov1B c4 (rvB c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)).map (fun _ => Pf1B c4 (main1B x.2.2.2 x.2.2.1) x.1),
       (ovPair (ov2B c4) (ov3B c4) (rvB c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)).map
         (fun _ => pfPair NS2B (Pf2B c4) (Pf3B c4) (main2B c1 x.2.2.2 x.2.2.1, main3B c1 c2 x.2.2.2 x.2.2.1) x.2.1),
       rvB c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)
    let s1B := fun (c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) => Com1B (sd1B c4 (sop1B c4 c2 c3 x.2.2.1 x.2.2.2)) x.1
    let s2B := fun (c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      s1B c4 c1 c2 c3 x + n1 * Com2B (sd2B c4 (sop2B c4 c2 c3 c1 x.2.2.1 x.2.2.2)) (x.2.1 % NS2B)
    let s3B := fun (c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      s1B c4 c1 c2 c3 x + n1 * comPair NS2B n2 Com2B Com3B
        (sd2B c4 (sop2B c4 c2 c3 c1 x.2.2.1 x.2.2.2), sd3B c4 (sop3B c4 c2 c3 c1 x.2.2.1 x.2.2.2)) x.2.1
    let svoB := fun (c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      (some (Pf1B c4 (sd1B c4 (sop1B c4 c2 c3 x.2.2.1 x.2.2.2)) x.1),
       some (pfPair NS2B (Pf2B c4) (Pf3B c4) (sd2B c4 (sop2B c4 c2 c3 c1 x.2.2.1 x.2.2.2), sd3B c4 (sop3B c4 c2 c3 c1 x.2.2.1 x.2.2.2)) x.2.1),
       svB c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)
    let sm4B := fun (g : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup)) → Nat) =>
      sumTo ((Q4 * Q4) ^ n1) (fun H1 => sumTo (K2 ^ (n1 * n2)) (fun H2 =>
        sumTo (K3 ^ (n1 * (n2 * n3))) (fun H3 => smB (fun x => g (H1, H2, H3, x)))))
    let r1B := fun (y : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup))) => rget (Q4 * Q4) (m1B y.2.2.2) y.1
    let r2B := fun (y : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup))) => rget K2 (m2B (r1B y) y.2.2.2) y.2.1
    let r3B := fun (y : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup))) => rget K3 (m3B (r1B y) (r2B y) y.2.2.2) y.2.2.1
    let MqB := fun (y : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup))) => φB (m3B (r1B y) (r2B y) y.2.2.2)
      (ozB (rvB 0 (r2B y) (r3B y) (efOf (r1B y / Q4)) (efOf (r1B y % Q4)) y.2.2.2.2.2.1 y.2.2.2.2.2.2))
    let ST := fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo (K4 ^ N4) (fun H4 => sumTo ((Q4 * Q4) ^ n1) (fun H1 =>
      sumTo (K2 ^ (n1 * n2)) (fun H2 => sumTo (K3 ^ (n1 * (n2 * n3))) (fun H3 => f (H1, H2, H3, H4)))))
    let SC := fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo K4 (fun c4 => sumTo (Q4 * Q4) (fun c1 =>
      sumTo K2 (fun c2 => sumTo K3 (fun c3 => f (c1, c2, c3, c4)))))
    let rvTA := fun (H : Nat × Nat × Nat × Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      (m1A x, m2A (r1A (H.1, H.2.1, H.2.2.1, x)) x, m3A (r1A (H.1, H.2.1, H.2.2.1, x)) (r2A (H.1, H.2.1, H.2.2.1, x)) x,
       rvoA (rget K4 (MqA (H.1, H.2.1, H.2.2.1, x)) H.2.2.2) (r1A (H.1, H.2.1, H.2.2.1, x)) (r2A (H.1, H.2.1, H.2.2.1, x))
         (r3A (H.1, H.2.1, H.2.2.1, x)) x)
    let pgTA := fun (H : Nat × Nat × Nat × Nat) (c : Nat × Nat × Nat × Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      (rset (Q4 * Q4) (s1A c.2.2.2 c.1 c.2.1 c.2.2.1 x) H.1 c.1, rset K2 (s2A c.2.2.2 c.1 c.2.1 c.2.2.1 x) H.2.1 c.2.1,
       rset K3 (s3A c.2.2.2 c.1 c.2.1 c.2.2.1 x) H.2.2.1 c.2.2.1,
       rset K4 (φA (s3A c.2.2.2 c.1 c.2.1 c.2.2.1 x) (ozA (svA c.2.2.2 c.2.1 c.2.2.1 (efOf (c.1 / Q4)) (efOf (c.1 % Q4))
         x.2.2.1 x.2.2.2))) H.2.2.2 c.2.2.2)
    let svTA := fun (c : Nat × Nat × Nat × Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      (s1A c.2.2.2 c.1 c.2.1 c.2.2.1 x, s2A c.2.2.2 c.1 c.2.1 c.2.2.1 x, s3A c.2.2.2 c.1 c.2.1 c.2.2.1 x,
       svoA c.2.2.2 c.1 c.2.1 c.2.2.1 x)
    let rvTB := fun (H : Nat × Nat × Nat × Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      (m1B x, m2B (r1B (H.1, H.2.1, H.2.2.1, x)) x, m3B (r1B (H.1, H.2.1, H.2.2.1, x)) (r2B (H.1, H.2.1, H.2.2.1, x)) x,
       rvoB (rget K4 (MqB (H.1, H.2.1, H.2.2.1, x)) H.2.2.2) (r1B (H.1, H.2.1, H.2.2.1, x)) (r2B (H.1, H.2.1, H.2.2.1, x))
         (r3B (H.1, H.2.1, H.2.2.1, x)) x)
    let pgTB := fun (H : Nat × Nat × Nat × Nat) (c : Nat × Nat × Nat × Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      (rset (Q4 * Q4) (s1B c.2.2.2 c.1 c.2.1 c.2.2.1 x) H.1 c.1, rset K2 (s2B c.2.2.2 c.1 c.2.1 c.2.2.1 x) H.2.1 c.2.1,
       rset K3 (s3B c.2.2.2 c.1 c.2.1 c.2.2.1 x) H.2.2.1 c.2.2.1,
       rset K4 (φB (s3B c.2.2.2 c.1 c.2.1 c.2.2.1 x) (ozB (svB c.2.2.2 c.2.1 c.2.2.1 (efOf (c.1 / Q4)) (efOf (c.1 % Q4))
         x.2.2.1 x.2.2.2))) H.2.2.2 c.2.2.2)
    let svTB := fun (c : Nat × Nat × Nat × Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      (s1B c.2.2.2 c.1 c.2.1 c.2.2.1 x, s2B c.2.2.2 c.1 c.2.1 c.2.2.1 x, s3B c.2.2.2 c.1 c.2.1 c.2.2.1 x,
       svoB c.2.2.2 c.1 c.2.1 c.2.2.1 x)
    let colT := fun (H : Nat × Nat × Nat × Nat) (c : Nat × Nat × Nat × Nat) (xa xb : Nat × Nat × Nat × (Nat → Tup)) =>
      decide (m1B xb = s1A c.2.2.2 c.1 c.2.1 c.2.2.1 xa) ||
      decide (m2B (r1B (H.1, H.2.1, H.2.2.1, xb)) xb = s2A c.2.2.2 c.1 c.2.1 c.2.2.1 xa) ||
      decide (m3B (r1B (H.1, H.2.1, H.2.2.1, xb)) (r2B (H.1, H.2.1, H.2.2.1, xb)) xb = s3A c.2.2.2 c.1 c.2.1 c.2.2.1 xa) ||
      decide (MqB (H.1, H.2.1, H.2.2.1, xb) = φA (s3A c.2.2.2 c.1 c.2.1 c.2.2.1 xa)
        (ozA (svA c.2.2.2 c.2.1 c.2.2.1 (efOf (c.1 / Q4)) (efOf (c.1 % Q4)) xa.2.2.1 xa.2.2.2)))
    let okT := fun (c : Nat × Nat × Nat × Nat) =>
      decide (c.1 < Q4 * Q4) && decide (c.2.1 < K2) && decide (c.2.2.1 < K3) && decide (c.2.2.2 < K4)
    ∀ E : Nat × Nat × Nat × Nat → Nat × Nat × Nat × (Option P1A × Option (P2A × P3A) × TViewN PVA PBA) → Nat × Nat × Nat × (Option P1B × Option (P2B × P3B) × TViewN PVB PBB) → Bool,
    (K4 * (Q4 * Q4 * (K2 * K3))) * ((K4 * (Q4 * Q4 * (K2 * K3))) * ST (fun H => smB (fun xb => smA (fun xa => indB (E H (rvTA H xa) (rvTB H xb)))))) ≤
      SC (fun ca => smA (fun xa => ST (fun H => SC (fun cb => smB (fun xb =>
        indB (E (pgTA (pgTB H cb xb) ca xa) (svTA ca xa) (svTB cb xb))))))) +
      (K4 * (Q4 * Q4 * (K2 * K3))) * ((K4 ^ N4 * (K4 * ((Q4 * Q4) ^ n1 * (K2 ^ (n1 * n2) * (K3 ^ (n1 * (n2 * n3)) *
        (K2 * (K3 * (NS1A * (NS2A * NS3A * (e1A + e2A)))) +
          (Q4 * (P * P) * (K2 * K3) + Q4 * Q4 * BzA) * (NS1A * (NS2A * NS3A * (NRA * (Q4 ^ mA * 1)))))))) +
          B4A * (Q4 * Q4 * (K2 * K3) * sm4A (fun _ => 1)))) * smB (fun _ => 1)) + (K4 ^ N4 * (K4 * ((Q4 * Q4) ^ n1 * (K2 ^ (n1 * n2) * (K3 ^ (n1 * (n2 * n3)) *
        (K2 * (K3 * (NS1B * (NS2B * NS3B * (e1B + e2B)))) +
          (Q4 * (P * P) * (K2 * K3) + Q4 * Q4 * BzB) * (NS1B * (NS2B * NS3B * (NRB * (Q4 ^ mB * 1)))))))) +
          B4B * (Q4 * Q4 * (K2 * K3) * sm4B (fun _ => 1)))) * SC (fun _ => smA (fun _ => 1)) +
      (K4 * (Q4 * Q4 * (K2 * K3))) * SC (fun _ => smA (fun _ => ST (fun _ => δ₀))) := by
  intro smA m1A m2A m3A rvoA s1A s2A s3A svoA sm4A r1A r2A r3A MqA smB m1B m2B m3B rvoB s1B s2B s3B svoB sm4B r1B r2B r3B MqB ST SC rvTA pgTA svTA rvTB pgTB svTB colT okT E
  have hQ : 0 < Q4 * Q4 := Nat.mul_pos Q4_pos Q4_pos
  refine Nat.le_trans (fs_two ST (lin_sum4 _ _ _ _) smA (lin_sm _ _ _ _) smB (lin_sm _ _ _ _) SC (lin_sum4 _ _ _ _) SC
    (comm_sm (lin_sm _ _ _ _) _ _ _ _) (comm_sum4 (lin_sm _ _ _ _) _ _ _ _) (comm_sum4 (lin_sm _ _ _ _) _ _ _ _)
    (comm_sum4 (lin_sum4 _ _ _ _) _ _ _ _) (comm_sum4 (lin_sm _ _ _ _) _ _ _ _)
    rvTA pgTA svTA rvTB pgTB svTB (fun E' => fs_open4_abs hK2 hK3 hK4 φA hφA rvA svA gzA hgzA g4A hB4A hrvA hsvA ozA hozA h1A h2A Com1A Pf1A op1A sd1A d1A hc1A hp1A hr1A ov1A hov1A main1A hsd1A Com2A Pf2A op2A sd2A d2A hc2A hp2A hr2A ov2A hov2A main2A hsd2A Com3A Pf3A op3A sd3A d3A hc3A hp3A hr3A ov3A hov3A main3A hsd3A hvo1A hvo2A hvo3A sop1A sop2A sop3A hsvo1A hsvo2A hsvo3A E') (fun E' => fs_open4_abs hK2 hK3 hK4 φB hφB rvB svB gzB hgzB g4B hB4B hrvB hsvB ozB hozB h1B h2B Com1B Pf1B op1B sd1B d1B hc1B hp1B hr1B ov1B hov1B main1B hsd1B Com2B Pf2B op2B sd2B d2B hc2B hp2B hr2B ov2B hov2B main2B hsd2B Com3B Pf3B op3B sd3B d3B hc3B hp3B hr3B ov3B hov3B main3B hsd3B hvo1B hvo2B hvo3B sop1B sop2B sop3B hsvo1B hsvo2B hsvo3B E')
    colT okT ?_ ?_ E) (Nat.add_le_add_left (Nat.mul_le_mul_left _ ?_) _)
  · intro f g h
    refine sumTo_mono _ (fun c4 h4 => sumTo_mono _ (fun c1 h1 => sumTo_mono _ (fun c2 h2 => sumTo_mono _ (fun c3 h3 =>
      h _ ?_))))
    simp only [okT, h1, h2, h3, h4, decide_true, Bool.and_self]
  · intro H ca xa xb hok hc
    simp only [okT, Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨⟨⟨b1, b2⟩, b3⟩, b4⟩ := hok
    simp only [colT, Bool.or_eq_false_iff, decide_eq_false_iff_not] at hc
    obtain ⟨⟨⟨n1', n2'⟩, n3'⟩, n4'⟩ := hc
    let y := (H.1, H.2.1, H.2.2.1, xb)
    let y' := ((pgTA H ca xa).1, (pgTA H ca xa).2.1, (pgTA H ca xa).2.2.1, xb)
    have h1 : r1B y' = r1B y := rget_rset_ne (H := H.1) hQ n1' b1
    have h2 : r2B y' = r2B y := by
      show rget K2 (m2B (r1B y') xb) (pgTA H ca xa).2.1 = rget K2 (m2B (r1B y) xb) H.2.1
      rw [h1]; exact rget_rset_ne (H := H.2.1) hK2 n2' b2
    have h3 : r3B y' = r3B y := by
      show rget K3 (m3B (r1B y') (r2B y') xb) (pgTA H ca xa).2.2.1 = rget K3 (m3B (r1B y) (r2B y) xb) H.2.2.1
      rw [h1, h2]; exact rget_rset_ne (H := H.2.2.1) hK3 n3' b3
    have hq : MqB y' = MqB y := by
      show φB (m3B (r1B y') (r2B y') xb) (ozB (rvB 0 (r2B y') (r3B y') (efOf (r1B y' / Q4)) (efOf (r1B y' % Q4))
          xb.2.2.1 xb.2.2.2)) = φB (m3B (r1B y) (r2B y) xb) (ozB (rvB 0 (r2B y) (r3B y) (efOf (r1B y / Q4))
          (efOf (r1B y % Q4)) xb.2.2.1 xb.2.2.2))
      rw [h1, h2, h3]
    have h4 : rget K4 (MqB y') (pgTA H ca xa).2.2.2 = rget K4 (MqB y) H.2.2.2 := by
      rw [hq]; exact rget_rset_ne (H := H.2.2.2) hK4 n4' b4
    show (m1B xb, m2B (r1B y') xb, m3B (r1B y') (r2B y') xb, rvoB (rget K4 (MqB y') (pgTA H ca xa).2.2.2) (r1B y')
      (r2B y') (r3B y') xb) = (m1B xb, m2B (r1B y) xb, m3B (r1B y) (r2B y) xb, rvoB (rget K4 (MqB y) H.2.2.2) (r1B y)
      (r2B y) (r3B y) xb)
    rw [h1, h2, h3, h4]
  · have hm1 : ∀ x, m1B x < n1 := fun x => hr1B _ _
    have hs1 : ∀ c4 c1 c2 c3 x, s1A c4 c1 c2 c3 x < n1 := fun _ _ _ _ _ => hr1A _ _
    have hpt : ∀ H ca xa xb, indB (colT H ca xa xb) ≤
        indB (decide (m1B xb = s1A ca.2.2.2 ca.1 ca.2.1 ca.2.2.1 xa)) := fun H ca xa xb => by
      cases hc : colT H ca xa xb
      · exact Nat.zero_le _
      · have e : m1B xb = s1A ca.2.2.2 ca.1 ca.2.1 ca.2.2.1 xa := by
          simp only [colT, Bool.or_eq_true, decide_eq_true_eq] at hc
          rcases hc with ((e | e) | e) | e
          · exact e
          · have := congrArg (fun z : Nat => z % n1) e
            simp only [m2B, s2A, Nat.add_mul_mod_self_left] at this
            rwa [Nat.mod_eq_of_lt (hm1 xb), Nat.mod_eq_of_lt (hs1 ca.2.2.2 ca.1 ca.2.1 ca.2.2.1 xa)] at this
          · have := congrArg (fun z : Nat => z % n1) e
            simp only [m3B, s3A, Nat.add_mul_mod_self_left] at this
            rwa [Nat.mod_eq_of_lt (hm1 xb), Nat.mod_eq_of_lt (hs1 ca.2.2.2 ca.1 ca.2.1 ca.2.2.1 xa)] at this
          · have := hφ _ _ _ _ e
            simp only [m3B, s3A, Nat.add_mul_mod_self_left] at this
            rwa [Nat.mod_eq_of_lt (hm1 xb), Nat.mod_eq_of_lt (hs1 ca.2.2.2 ca.1 ca.2.1 ca.2.2.1 xa)] at this
        have ed : decide (m1B xb = s1A ca.2.2.2 ca.1 ca.2.1 ca.2.2.1 xa) = true := decide_eq_true e
        rw [ed]; exact Nat.le_refl _
    have hin : ∀ ca xa H, smB (fun xb => indB (colT H ca xa xb)) ≤ δ₀ := fun ca xa H =>
      Nat.le_trans (sm_mono smB (lin_sm NS1B (NS2B * NS3B) NRB mB) (fun xb => hpt H ca xa xb))
        (hsp (s1A ca.2.2.2 ca.1 ca.2.1 ca.2.2.1 xa))
    have hST : ∀ ca xa, ST (fun H => smB (fun xb => indB (colT H ca xa xb))) ≤ ST (fun _ => δ₀) := fun ca xa =>
      sumTo_mono _ (fun H4 _ => sumTo_mono _ (fun H1 _ => sumTo_mono _ (fun H2 _ => sumTo_mono _ (fun H3 _ =>
        hin ca xa (H1, H2, H3, H4)))))
    have hsA : ∀ ca, smA (fun xa => ST (fun H => smB (fun xb => indB (colT H ca xa xb)))) ≤
        smA (fun _ => ST (fun _ => δ₀)) := fun ca => sm_mono smA (lin_sm NS1A (NS2A * NS3A) NRA mA) (hST ca)
    exact sumTo_mono _ (fun c4 _ => sumTo_mono _ (fun c1 _ => sumTo_mono _ (fun c2 _ => sumTo_mono _ (fun c3 _ =>
      hsA (c1, c2, c3, c4)))))

end Circuit
