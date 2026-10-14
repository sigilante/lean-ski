import Ski.ZK.SpongeMany

/-!
# The load of one capacity value under a uniform permutation

`SpongeIndex` and `SpongeMany` bound the sponge index's preimage through
all meeting pairs, which needs `n1²` below the capacity.  Here the count is
local to one target, which reaches Plonky3's widths when the index is the
state one absorption after the first commitment.

- **Hits on a fixed set.** `k` adaptive forward queries under a uniform
  permutation land `B` fresh answers in a fixed set of `F` values;
  `E[B choose m] ≤ C(k, m) F^m / (K - k)^m` (`hitN_moment`), so at least
  `m` such hits occur on at most `(k F)^m / (m! (K - k)^m)` of the
  permutation tables (`hitN_tail`).
- **One absorption after the first commitment.** The index
  `P(x ‖ keep(P(c ‖ iv)))` of first commitment `c` and later block `x`,
  `keep` the part of the state the block does not overwrite
  (`idx1`) agrees for two commitments only if their first answers share a
  capacity (`idx1_eq`).  So an index's preimage among the `n1` first
  commitments is one capacity value's load (`hitN_nxt0`): at most `m - 1`,
  or `n1` on tables where some capacity value collects `m` first answers
  (`loadM`, `idx1_preimage`).  The bound holds for every later block `x`,
  so no union over later transcripts enters.
- **The spread at every table.** `δs' = δs loadM` meets `SudChallenger`'s
  `hsp1` and `hφsp` for every `d`, `rest`, `w` and `v` (`load_hsp`).
  Averaged, `m! (K - n1)^m E[loadM] ≤ m! (K - n1)^m (m - 1) +
  n1 Kc (n1 F)^m`, `Kc` the number of capacity values (`loadM_countP`,
  `load_δs_countP`).  With `F / K` one over the capacity's size and
  `n1 ≤ R1` the overwritten rate, `r = n1 F / (K - n1)` stays near
  `R1 / Kc`, and `E[loadM] ≤ m - 1 + n1 Kc r^m / m!`.  At Plonky3's
  challengers the rate equals the capacity, so `r = C / (C - 1)`, about
  `1`; with `n1 = Kc = p^8` the bound falls from about `2^247` to about
  `95` (BabyBear, `m = 96`).
- **The composite.** `sud_interleaveS` with this index holds at every
  permutation table and averaged over them (`zkbT_avgW`,
  `sud_interleaveL`), with a number for its error (`sud_interleaveLN`).
  `load_satPT` meets `hκ` at `two_meet_satPT`'s instance.

Limits.  The index is the state after one absorption past the first
commitment; Plonky3 absorbs the whole later transcript, and each later
absorption can merge capacity classes again (not shown).  As in
`SpongeIndex`, the state before the first commitment is fixed, the first
commitment fills one aligned block (`n1 ≤ R1`), and the fourth table `H4`
stays independent of the permutation.  The index reads only the first
later block, and, as `SudChallenger`'s `hφsp` takes it, that block does not
depend on the salt; in Plonky3 the next commitment follows challenges drawn
after the first.
-/

set_option autoImplicit false

namespace Circuit
open ZKF

/-! ### Hits on a fixed set: the load of one capacity value -/

/-- The fresh queries of a newest-first run whose answers lie in `T`. -/
def hitN (T : List Nat) : List (Nat × Nat) → Nat
  | [] => 0
  | x :: rest => hitN T rest + indB (!decide (x.1 ∈ rest.map Prod.fst) && decide (x.2 ∈ T))

theorem hitN_le (T : List Nat) : ∀ l : List (Nat × Nat), hitN T l ≤ l.length
  | [] => Nat.le_refl _
  | x :: rest => by
    show hitN T rest + _ ≤ rest.length + 1
    exact Nat.add_le_add (hitN_le T rest) (indB_le _)

/-- `chs k m F^m`, by Pascal's rule. -/
def eC (F : Nat) : Nat → Nat → Nat
  | _, 0 => 1
  | 0, _ + 1 => 0
  | k + 1, m + 1 => eC F k (m + 1) + F * eC F k m

/-- **The `m`-th factorial moment of the hits on a fixed set**: `F` values,
    `k` adaptive forward queries; `E[hits choose m] ≤ C(k, m) F^m / (K - k)^m`. -/
theorem hitN_moment {K F : Nat} (hK : 0 < K) (T : List Nat) (hT : T.length ≤ F) (nxt : List Nat → Nat) (hnx : ∀ l, nxt l < K) :
    ∀ k m, (K - k) ^ m * sumTo (K ^ K) (fun H => indB (permB K H) * chs (hitN T (runAdp K nxt H k)) m) ≤
      eC F k m * sumTo (K ^ K) (fun H => indB (permB K H))
  | k, 0 => by
    have e : ∀ n, chs n 0 = 1 := fun n => by cases n <;> rfl
    have e2 : ∀ k, eC F k 0 = 1 := fun k => by cases k <;> rfl
    rw [Nat.pow_zero, Nat.one_mul, e2, Nat.one_mul, sumTo_congr _ (fun H _ => by rw [e, Nat.mul_one])]
    exact Nat.le_refl _
  | 0, m + 1 => by
    have e : ∀ H, indB (permB K H) * chs (hitN T (runAdp K nxt H 0)) (m + 1) = 0 := fun H => by
      show indB (permB K H) * chs 0 (m + 1) = 0
      rw [show chs 0 (m + 1) = 0 from rfl, Nat.mul_zero]
    rw [sumTo_congr _ (fun H _ => e H), sumTo_const, Nat.mul_zero, Nat.mul_zero]; exact Nat.zero_le _
  | k + 1, m + 1 => by
    have ih1 := hitN_moment hK T hT nxt hnx k (m + 1)
    have ih0 := hitN_moment hK T hT nxt hnx k m
    let p := fun H => nxt ((runAdp K nxt H k).map Prod.snd)
    let g := fun H => !decide (p H ∈ (runAdp K nxt H k).map Prod.fst)
    let A := fun H => (runAdp K nxt H k).map Prod.snd
    let S := fun (_ : Nat) => T
    let w := fun H => chs (hitN T (runAdp K nxt H k)) m
    have hnot : ∀ H, g H = true → p H ∉ (runAdp K nxt H k).map Prod.fst := fun H hg h => by
      simp only [g, h, decide_true, Bool.not_true] at hg; exact Bool.false_ne_true hg
    have hw : ∀ H, w H ≤ 2 ^ k := fun H =>
      Nat.le_trans (chs_le_pow _ m) (Nat.pow_le_pow_right (by decide) (by
        have := hitN_le T (runAdp K nxt H k); rw [runAdp_length] at this; exact this))
    -- the fresh near answer, weighted by the history's binomial
    have fcw : (K - k) * sumTo (K ^ K) (fun H => indB (permB K H && g H && decide (rget K (p H) H ∈ S H)) * w H) ≤
        F * sumTo (K ^ K) (fun H => indB (permB K H) * w H) := by
      have each : ∀ u, (K - k) * sumTo (K ^ K) (fun H => indB (permB K H && (g H && decide (u < w H)) &&
          decide (rget K (p H) H ∈ S H))) ≤ F * sumTo (K ^ K) (fun H => indB (permB K H && (g H && decide (u < w H)))) := by
        intro u
        refine fresh_countPG (j := k) (k := F) hK p (fun H => hnx _) (fun H => g H && decide (u < w H)) A S
          (fun H => by simp only [A, List.length_map, runAdp_length]; exact Nat.le_refl _)
          (fun _ => hT) ?_ ?_
        · intro H _ hP hgu h
          have hg : g H = true := (Bool.and_eq_true_iff.1 hgu).1
          obtain ⟨z, hz, hza⟩ := List.mem_map.1 h
          have e : rget K (p H) H = rget K z.1 H := by rw [← hza, runAdp_ans K nxt H k z hz]
          have := permB_inj hP (hnx _) (runAdp_pos nxt hnx H k z hz) e
          exact hnot H hg (List.mem_map.2 ⟨z, hz, this.symm⟩)
        · intro H a b _ ha hb haA hbA _ hgu
          have e := runAdp_vswap hK ha hb nxt hnx k H haA hbA
          refine ⟨by simp only [p, e], by simp only [A, e], rfl, ?_⟩
          simp only [g, w, p, e]; exact hgu
      have l : sumTo (K ^ K) (fun H => indB (permB K H && g H && decide (rget K (p H) H ∈ S H)) * w H) =
          sumTo (2 ^ k) (fun u => sumTo (K ^ K) (fun H => indB (permB K H && (g H && decide (u < w H)) &&
            decide (rget K (p H) H ∈ S H)))) := by
        rw [← sumTo_exch _ (2 ^ k) (K ^ K)]
        refine sumTo_congr _ (fun H _ => ?_)
        rw [Nat.mul_comm, Nat.mul_comm (w H), weight_split _ (w H) (2 ^ k) (hw H)]
        refine sumTo_congr _ (fun u _ => ?_)
        cases permB K H <;> cases g H <;> cases decide (u < w H) <;> cases decide (rget K (p H) H ∈ S H) <;> rfl
      have r : sumTo (2 ^ k) (fun u => sumTo (K ^ K) (fun H => indB (permB K H && (g H && decide (u < w H))))) ≤
          sumTo (K ^ K) (fun H => indB (permB K H) * w H) := by
        rw [sumTo_exch _ (K ^ K) (2 ^ k)]
        refine sumTo_mono _ (fun H _ => ?_)
        rw [weight_split _ (w H) (2 ^ k) (hw H)]
        refine sumTo_mono _ (fun u _ => ?_)
        cases permB K H <;> cases g H <;> cases decide (u < w H) <;> simp [indB]
      rw [l, sumTo_mul]
      refine Nat.le_trans (sumTo_mono _ (fun u _ => each u)) ?_
      rw [← sumTo_mul]
      exact Nat.mul_le_mul_left _ r
    -- Pascal over the newest query
    have pt : ∀ H, indB (permB K H) * chs (hitN T (runAdp K nxt H (k + 1))) (m + 1) =
        indB (permB K H) * chs (hitN T (runAdp K nxt H k)) (m + 1) +
          indB (permB K H && g H && decide (rget K (p H) H ∈ S H)) * w H := by
      intro H
      show indB (permB K H) * chs (hitN T (runAdp K nxt H k) +
        indB (!decide (p H ∈ (runAdp K nxt H k).map Prod.fst) &&
          decide (rget K (p H) H ∈ T))) (m + 1) = _
      rw [chs_step, Nat.mul_add]
      congr 1
      show indB (permB K H) * (indB (g H && decide (rget K (p H) H ∈ S H)) * w H) = _
      rw [← Nat.mul_assoc, indB_and', Bool.and_assoc]
    have hkk : K - (k + 1) ≤ K - k := Nat.sub_le_sub_left (Nat.le_succ k) K
    rw [sumTo_congr _ (fun H _ => pt H), sumTo_add, Nat.mul_add]
    show _ ≤ (eC F k (m + 1) + F * eC F k m) * _
    rw [Nat.add_mul]
    refine Nat.add_le_add (Nat.le_trans (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hkk _)) ih1) ?_
    rw [Nat.pow_succ, Nat.mul_assoc]
    calc (K - (k + 1)) ^ m * ((K - (k + 1)) * sumTo (K ^ K) (fun H =>
          indB (permB K H && g H && decide (rget K (p H) H ∈ S H)) * w H))
        ≤ (K - k) ^ m * ((K - k) * sumTo (K ^ K) (fun H =>
          indB (permB K H && g H && decide (rget K (p H) H ∈ S H)) * w H)) :=
          Nat.mul_le_mul (Nat.pow_le_pow_left hkk _) (Nat.mul_le_mul_right _ hkk)
      _ ≤ (K - k) ^ m * (F * sumTo (K ^ K) (fun H => indB (permB K H) * w H)) := Nat.mul_le_mul_left _ fcw
      _ = F * ((K - k) ^ m * sumTo (K ^ K) (fun H => indB (permB K H) * w H)) := Nat.mul_left_comm _ _ _
      _ ≤ F * (eC F k m * sumTo (K ^ K) (fun H => indB (permB K H))) := Nat.mul_le_mul_left _ ih0
      _ = F * eC F k m * sumTo (K ^ K) (fun H => indB (permB K H)) := (Nat.mul_assoc _ _ _).symm

theorem eC_le (F : Nat) : ∀ k m, fact m * eC F k m ≤ (k * F) ^ m
  | k, 0 => by cases k <;> exact Nat.le_refl _
  | 0, m + 1 => by show fact (m + 1) * 0 ≤ _; rw [Nat.mul_zero]; exact Nat.zero_le _
  | k + 1, m + 1 => by
    have ih1 := eC_le F k (m + 1)
    have ih0 := eC_le F k m
    show fact (m + 1) * (eC F k (m + 1) + F * eC F k m) ≤ ((k + 1) * F) ^ (m + 1)
    rw [Nat.mul_add, Nat.succ_mul]
    refine Nat.le_trans (Nat.add_le_add ih1 ?_) (pow_succ_ge _ _ m)
    show (m + 1) * fact m * (F * eC F k m) ≤ (m + 1) * F * (k * F) ^ m
    calc (m + 1) * fact m * (F * eC F k m) = (m + 1) * F * (fact m * eC F k m) := by ac_rfl
      _ ≤ (m + 1) * F * (k * F) ^ m := Nat.mul_le_mul_left _ ih0

/-- **At least `m` hits on a fixed set of `F` values are rare**: on at most
    `(k F)^m / (m! (K - k)^m)` of the permutation tables. -/
theorem hitN_tail {K F : Nat} (hK : 0 < K) (T : List Nat) (hT : T.length ≤ F) (nxt : List Nat → Nat)
    (hnx : ∀ l, nxt l < K) (k m : Nat) :
    fact m * ((K - k) ^ m * sumTo (K ^ K) (fun H => indB (permB K H && decide (m ≤ hitN T (runAdp K nxt H k))))) ≤
      (k * F) ^ m * sumTo (K ^ K) (fun H => indB (permB K H)) := by
  have pt : ∀ H, indB (permB K H && decide (m ≤ hitN T (runAdp K nxt H k))) ≤
      indB (permB K H) * chs (hitN T (runAdp K nxt H k)) m := fun H => by
    cases hP : permB K H
    · simp [indB]
    · by_cases h : m ≤ hitN T (runAdp K nxt H k)
      · rw [decide_eq_true h, show indB (true && true) = 1 from rfl, show indB true = 1 from rfl, Nat.one_mul]
        exact chs_pos _ _ h
      · rw [decide_eq_false h]; simp [indB]
  calc fact m * ((K - k) ^ m * sumTo (K ^ K) (fun H => indB (permB K H && decide (m ≤ hitN T (runAdp K nxt H k)))))
      ≤ fact m * ((K - k) ^ m * sumTo (K ^ K) (fun H => indB (permB K H) * chs (hitN T (runAdp K nxt H k)) m)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (sumTo_mono _ (fun H _ => pt H)))
    _ ≤ fact m * (eC F k m * sumTo (K ^ K) (fun H => indB (permB K H))) :=
        Nat.mul_le_mul_left _ (hitN_moment hK T hT nxt hnx k m)
    _ = fact m * eC F k m * sumTo (K ^ K) (fun H => indB (permB K H)) := (Nat.mul_assoc _ _ _).symm
    _ ≤ _ := Nat.mul_le_mul_right _ (eC_le F k m)

/-! ### One absorption after the first commitment -/

/-- The first commitments' queries: `inner iv c` for `c` in order. -/
def nxt0 (inner : Nat → Nat → Nat) (iv : Nat) (l : List Nat) : Nat := inner iv l.length

theorem runAdp_nxt0 (K : Nat) (inner : Nat → Nat → Nat) (iv H : Nat) : ∀ k,
    runAdp K (nxt0 inner iv) H (k + 1) = (inner iv k, rget K (inner iv k) H) :: runAdp K (nxt0 inner iv) H k := by
  intro k
  show (nxt0 inner iv ((runAdp K (nxt0 inner iv) H k).map Prod.snd), _) :: _ = _
  rw [nxt0, List.length_map, runAdp_length]

theorem runAdp_nxt0_fst (K : Nat) (inner : Nat → Nat → Nat) (iv H : Nat) :
    ∀ k, ∀ y ∈ runAdp K (nxt0 inner iv) H k, ∃ j, j < k ∧ y.1 = inner iv j
  | 0, _, h => absurd h List.not_mem_nil
  | k + 1, y, h => by
    rw [runAdp_nxt0] at h
    rcases List.mem_cons.1 h with e | e
    · exact ⟨k, Nat.lt_succ_self k, by rw [e]⟩
    · obtain ⟨j, hj, hy⟩ := runAdp_nxt0_fst K inner iv H k y e
      exact ⟨j, Nat.lt_succ_of_lt hj, hy⟩

/-- **With distinct first positions every query is fresh**, so the hits
    count the first commitments whose answers lie in `T`. -/
theorem hitN_nxt0 (K : Nat) (inner : Nat → Nat → Nat) (iv H n1 : Nat)
    (hd : ∀ a b, a < n1 → b < n1 → a ≠ b → inner iv a ≠ inner iv b) (T : List Nat) :
    ∀ k, k ≤ n1 → hitN T (runAdp K (nxt0 inner iv) H k) = sumTo k (fun c => indB (decide (rget K (inner iv c) H ∈ T)))
  | 0, _ => rfl
  | k + 1, hk => by
    rw [runAdp_nxt0]
    show hitN T (runAdp K (nxt0 inner iv) H k) + indB (!decide (inner iv k ∈ (runAdp K (nxt0 inner iv) H k).map Prod.fst) &&
      decide (rget K (inner iv k) H ∈ T)) = sumTo k _ + _
    rw [hitN_nxt0 K inner iv H n1 hd T k (Nat.le_of_succ_le hk)]
    have hf : inner iv k ∉ (runAdp K (nxt0 inner iv) H k).map Prod.fst := fun h => by
      obtain ⟨y, hy, hy1⟩ := List.mem_map.1 h
      obtain ⟨j, hj, e⟩ := runAdp_nxt0_fst K inner iv H k y hy
      exact hd j k (Nat.lt_of_lt_of_le hj (Nat.le_of_succ_le hk)) hk (Nat.ne_of_lt hj) (e ▸ hy1)
    rw [decide_eq_false hf, Bool.not_false, Bool.true_and]

/-- The values below `K` whose projection is `v`. -/
def fib (K : Nat) (κ : Nat → Nat) (v : Nat) : List Nat := (List.range K).filter (fun u => κ u == v)

theorem fib_length {K F : Nat} (κ : Nat → Nat) (hF : ∀ v, sumTo K (fun u => indB (decide (κ u = v))) ≤ F) (v : Nat) :
    (fib K κ v).length ≤ F := by
  have hlen : ∀ (l : List Nat) (f : Nat → Bool), (l.filter f).length = (l.map (fun u => indB (f u))).sum := by
    intro l f
    induction l with
    | nil => rfl
    | cons u l ih => cases hf : f u <;> simp [hf, ih, indB] <;> omega
  unfold fib
  rw [hlen, range_map_sum]
  refine Nat.le_trans (Nat.le_of_eq (sumTo_congr _ (fun u _ => ?_))) (hF v)
  by_cases h : κ u = v
  · rw [beq_iff_eq.2 h, decide_eq_true h]
  · rw [decide_eq_false h, show (κ u == v) = false from beq_eq_false_iff_ne.2 h]

/-- The index after the first commitment `c` and one more block `x`. -/
def idx1 (K : Nat) (inner : Nat → Nat → Nat) (iv x c H : Nat) : Nat := rget K (inner (rget K (inner iv c) H) x) H

theorem idx1_eq {K : Nat} (inner : Nat → Nat → Nat) (hin : ∀ s x, inner s x < K) (κ : Nat → Nat)
    (hpk : ∀ x s s', inner s x = inner s' x → κ s = κ s') {iv x c c' H : Nat} (hP : permB K H = true)
    (h : idx1 K inner iv x c H = idx1 K inner iv x c' H) :
    κ (rget K (inner iv c) H) = κ (rget K (inner iv c') H) :=
  hpk x _ _ (permB_inj hP (hin _ _) (hin _ _) h)

/-- The load bound at the table: `m - 1`, or `n1` where some capacity value
    collects `m` of the `n1` first answers. -/
def loadM (K : Nat) (inner : Nat → Nat → Nat) (iv n1 : Nat) (κ : Nat → Nat) (Kc m H : Nat) : Nat :=
  (m - 1) + n1 * sumTo Kc (fun v0 => indB (decide (m ≤ hitN (fib K κ v0) (runAdp K (nxt0 inner iv) H n1))))

/-- **One absorption after the first commitment: an index's preimage is one
    capacity value's load**, at most `loadM`. -/
theorem idx1_preimage {K : Nat} (inner : Nat → Nat → Nat) (hin : ∀ s x, inner s x < K) (κ : Nat → Nat) {Kc : Nat}
    (hκ : ∀ u, κ u < Kc) (hpk : ∀ x s s', inner s x = inner s' x → κ s = κ s') {iv n1 : Nat}
    (hd : ∀ a b, a < n1 → b < n1 → a ≠ b → inner iv a ≠ inner iv b) (m : Nat) {H : Nat} (hP : permB K H = true)
    (x v : Nat) :
    sumTo n1 (fun c => indB (decide (idx1 K inner iv x c H = v))) ≤ loadM K inner iv n1 κ Kc m H := by
  by_cases hex : ∃ c0, c0 < n1 ∧ idx1 K inner iv x c0 H = v
  · obtain ⟨c0, hc0, hv⟩ := hex
    let v0 := κ (rget K (inner iv c0) H)
    have sub : sumTo n1 (fun c => indB (decide (idx1 K inner iv x c H = v))) ≤
        hitN (fib K κ v0) (runAdp K (nxt0 inner iv) H n1) := by
      rw [hitN_nxt0 K inner iv H n1 hd _ n1 (Nat.le_refl _)]
      refine sumTo_mono _ (fun c _ => ?_)
      by_cases e : idx1 K inner iv x c H = v
      · rw [decide_eq_true e]
        have hk := idx1_eq inner hin κ hpk hP (e.trans hv.symm)
        have : rget K (inner iv c) H ∈ fib K κ v0 :=
          List.mem_filter.2 ⟨List.mem_range.2 (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (rget_lt (Nat.lt_of_le_of_lt
            (Nat.zero_le _) (hin iv 0)) _ _) (Nat.le_refl _)) (Nat.le_refl _)), beq_iff_eq.2 hk⟩
        rw [decide_eq_true this]; exact Nat.le_refl _
      · rw [decide_eq_false e]; exact Nat.zero_le _
    unfold loadM
    by_cases hm : m ≤ hitN (fib K κ v0) (runAdp K (nxt0 inner iv) H n1)
    · have h1 : 1 ≤ sumTo Kc (fun v1 => indB (decide (m ≤ hitN (fib K κ v1) (runAdp K (nxt0 inner iv) H n1)))) :=
        Nat.le_trans (by rw [decide_eq_true hm]; exact Nat.le_refl _)
          (le_sumTo (fun v1 => indB (decide (m ≤ hitN (fib K κ v1) (runAdp K (nxt0 inner iv) H n1)))) Kc (hκ _))
      have h2 : sumTo n1 (fun c => indB (decide (idx1 K inner iv x c H = v))) ≤ n1 :=
        Nat.le_trans (sumTo_mono _ (fun c _ => indB_le _)) (Nat.le_of_eq (by rw [sumTo_const, Nat.mul_one]))
      exact Nat.le_trans h2 (Nat.le_trans (Nat.le_mul_of_pos_right _ h1) (Nat.le_add_left _ _))
    · exact Nat.le_trans sub (Nat.le_trans (Nat.le_pred_of_lt (Nat.lt_of_not_le hm)) (Nat.le_add_right _ _))
  · have : sumTo n1 (fun c => indB (decide (idx1 K inner iv x c H = v))) = 0 :=
      Eq.trans (sumTo_congr _ (fun c hc => by rw [decide_eq_false (fun e => hex ⟨c, hc, e⟩)]; rfl))
        (Eq.trans (sumTo_const 0 n1) (Nat.mul_zero n1))
    rw [this]; exact Nat.zero_le _

/-- **The load bound averaged over a uniform permutation**: `m! (K - n1)^m`
    times the summed `loadM` is at most `m! (K - n1)^m (m - 1)` plus
    `n1 Kc (n1 F)^m` per permutation table. -/
theorem loadM_countP {K F : Nat} (hK : 0 < K) (inner : Nat → Nat → Nat) (hin : ∀ s x, inner s x < K) (κ : Nat → Nat)
    (hF : ∀ v, sumTo K (fun u => indB (decide (κ u = v))) ≤ F) (iv n1 Kc m : Nat) :
    fact m * ((K - n1) ^ m * sumTo (K ^ K) (fun H => indB (permB K H) * loadM K inner iv n1 κ Kc m H)) ≤
      (fact m * ((K - n1) ^ m * (m - 1)) + n1 * (Kc * (n1 * F) ^ m)) * sumTo (K ^ K) (fun H => indB (permB K H)) := by
  have hnx : ∀ l, nxt0 inner iv l < K := fun l => hin _ _
  have e : ∀ H, indB (permB K H) * loadM K inner iv n1 κ Kc m H = indB (permB K H) * (m - 1) +
      n1 * sumTo Kc (fun v0 => indB (permB K H && decide (m ≤ hitN (fib K κ v0) (runAdp K (nxt0 inner iv) H n1)))) := by
    intro H
    unfold loadM
    rw [Nat.mul_add, Nat.mul_left_comm, sumTo_mul]
    congr 2
    refine sumTo_congr _ (fun v0 _ => ?_)
    rw [indB_and']
  have tail : ∀ v0, fact m * ((K - n1) ^ m * sumTo (K ^ K) (fun H =>
      indB (permB K H && decide (m ≤ hitN (fib K κ v0) (runAdp K (nxt0 inner iv) H n1))))) ≤
      (n1 * F) ^ m * sumTo (K ^ K) (fun H => indB (permB K H)) := fun v0 =>
    hitN_tail hK (fib K κ v0) (fib_length κ hF v0) (nxt0 inner iv) hnx n1 m
  have e2 : sumTo (K ^ K) (fun H => indB (permB K H) * (m - 1)) = (m - 1) * sumTo (K ^ K) (fun H => indB (permB K H)) := by
    rw [sumTo_mul]; exact sumTo_congr _ (fun H _ => Nat.mul_comm _ _)
  rw [sumTo_congr _ (fun H _ => e H), sumTo_add, e2, ← sumTo_mul, sumTo_exch _ Kc (K ^ K)]
  generalize hPi : sumTo (K ^ K) (fun H => indB (permB K H)) = Pi0 at *
  have hs : fact m * ((K - n1) ^ m * sumTo Kc (fun v0 => sumTo (K ^ K) (fun H =>
      indB (permB K H && decide (m ≤ hitN (fib K κ v0) (runAdp K (nxt0 inner iv) H n1)))))) ≤ Kc * ((n1 * F) ^ m * Pi0) := by
    rw [sumTo_mul, sumTo_mul]
    refine Nat.le_trans (sumTo_mono _ (fun v0 _ => ?_)) (Nat.le_of_eq (sumTo_const _ Kc))
    exact tail v0
  calc fact m * ((K - n1) ^ m * ((m - 1) * Pi0 + n1 * sumTo Kc (fun v0 => sumTo (K ^ K) (fun H =>
        indB (permB K H && decide (m ≤ hitN (fib K κ v0) (runAdp K (nxt0 inner iv) H n1)))))))
      = fact m * ((K - n1) ^ m * (m - 1)) * Pi0 + n1 * (fact m * ((K - n1) ^ m * sumTo Kc (fun v0 => sumTo (K ^ K) (fun H =>
        indB (permB K H && decide (m ≤ hitN (fib K κ v0) (runAdp K (nxt0 inner iv) H n1))))))) := by
        rw [Nat.mul_add, Nat.mul_add]
        congr 1
        · rw [← Nat.mul_assoc, ← Nat.mul_assoc, ← Nat.mul_assoc]
        · ac_rfl
    _ ≤ fact m * ((K - n1) ^ m * (m - 1)) * Pi0 + n1 * (Kc * ((n1 * F) ^ m * Pi0)) := Nat.add_le_add_left (Nat.mul_le_mul_left _ hs) _
    _ = (fact m * ((K - n1) ^ m * (m - 1)) + n1 * (Kc * (n1 * F) ^ m)) * Pi0 := by
        rw [Nat.add_mul, Nat.mul_assoc n1, Nat.mul_assoc Kc]

/-- **`SudChallenger`'s spread hypotheses at every table, one absorption
    after the first commitment**: the index `φ m w` the state after the
    first commitment `m % n1` and the first block of `enc (m / n1) w`; the
    table's `δs' = δs loadM` meets `hsp1` and `hφsp` for every `d`, `rest`,
    `w` and `v` (`m ≥ 2`). -/
theorem load_hsp {D W : Type} {K NS1 n1 δs Kc : Nat} (inner : Nat → Nat → Nat) (hin : ∀ s x, inner s x < K)
    (κ : Nat → Nat) (hκ : ∀ u, κ u < Kc) (hpk : ∀ x s s', inner s x = inner s' x → κ s = κ s') (iv : Nat)
    (hd : ∀ a b, a < n1 → b < n1 → a ≠ b → inner iv a ≠ inner iv b) (enc : Nat → W → List Nat)
    (Com1 : D → Nat → Nat) (hr1 : ∀ d σ, Com1 d σ < n1)
    (hsp1 : ∀ d v, sumTo NS1 (fun σ => indB (decide (Com1 d σ = v))) ≤ δs) {m : Nat} (hm : 2 ≤ m) {H : Nat}
    (hP : permB K H = true) :
    (∀ d v, sumTo NS1 (fun σ => indB (decide (Com1 d σ = v))) ≤ δs * loadM K inner iv n1 κ Kc m H) ∧
      (∀ d rest w v, sumTo NS1 (fun σ1 => indB (decide
        ((fun m' w => idx1 K inner iv ((enc (m' / n1) w).getD 0 0) (m' % n1) H) (Com1 d σ1 + n1 * rest) w = v))) ≤
        δs * loadM K inner iv n1 κ Kc m H) := by
  have h1 : 1 ≤ loadM K inner iv n1 κ Kc m H := Nat.le_trans (Nat.le_sub_of_add_le hm) (Nat.le_add_right _ _)
  refine ⟨fun d v => Nat.le_trans (hsp1 d v) (Nat.le_trans (Nat.le_of_eq (Nat.mul_one δs).symm)
    (Nat.mul_le_mul_left _ h1)), fun d rest w v => ?_⟩
  have hn1 : 0 < n1 := Nat.lt_of_le_of_lt (Nat.zero_le _) (hr1 d 0)
  have em : ∀ σ1, (Com1 d σ1 + n1 * rest) % n1 = Com1 d σ1 ∧ (Com1 d σ1 + n1 * rest) / n1 = rest := fun σ1 =>
    ⟨by rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (hr1 d σ1)],
     by rw [Nat.add_mul_div_left _ _ hn1, Nat.div_eq_of_lt (hr1 d σ1), Nat.zero_add]⟩
  let x := (enc rest w).getD 0 0
  let φ := fun c => idx1 K inner iv x c H
  have e : ∀ σ1, (fun m' w => idx1 K inner iv ((enc (m' / n1) w).getD 0 0) (m' % n1) H) (Com1 d σ1 + n1 * rest) w =
      φ (Com1 d σ1) := fun σ1 => by
    show idx1 K inner iv ((enc ((Com1 d σ1 + n1 * rest) / n1) w).getD 0 0) ((Com1 d σ1 + n1 * rest) % n1) H = _
    rw [(em σ1).1, (em σ1).2]
  rw [sumTo_congr _ (fun σ1 _ => by rw [e σ1])]
  rw [sumTo_split_pos (Com1 d) (hr1 d)]
  have each : ∀ c, sumTo NS1 (fun σ => indB (decide (Com1 d σ = c)) * indB (decide (φ (Com1 d σ) = v))) ≤
      δs * indB (decide (φ c = v)) := fun c => by
    have e : ∀ σ, indB (decide (Com1 d σ = c)) * indB (decide (φ (Com1 d σ) = v)) =
        indB (decide (φ c = v)) * indB (decide (Com1 d σ = c)) := fun σ => by
      by_cases h : Com1 d σ = c
      · rw [h, Nat.mul_comm]
      · rw [decide_eq_false h]; simp [indB]
    rw [sumTo_congr _ (fun σ _ => e σ), ← sumTo_mul, Nat.mul_comm δs]
    exact Nat.mul_le_mul_left _ (hsp1 d c)
  refine Nat.le_trans (sumTo_mono _ (fun c _ => each c)) ?_
  rw [← sumTo_mul]
  exact Nat.mul_le_mul_left _ (idx1_preimage inner hin κ hκ hpk hd m hP x v)

/-- **The table's `δs'` averaged**: `m! (K - n1)^m` times the weighted
    `δs loadM` is at most `δs (m! (K - n1)^m (m - 1) + n1 Kc (n1 F)^m)` per
    permutation table. -/
theorem load_δs_countP {K F : Nat} (hK : 0 < K) (inner : Nat → Nat → Nat) (hin : ∀ s x, inner s x < K) (κ : Nat → Nat)
    (hF : ∀ v, sumTo K (fun u => indB (decide (κ u = v))) ≤ F) (iv n1 Kc m δs : Nat) :
    fact m * (K - n1) ^ m * sumTo (K ^ K) (fun H => indB (permB K H) * (δs * loadM K inner iv n1 κ Kc m H)) ≤
      δs * ((fact m * ((K - n1) ^ m * (m - 1)) + n1 * (Kc * (n1 * F) ^ m)) * sumTo (K ^ K) (fun H => indB (permB K H))) := by
  have h := loadM_countP hK inner hin κ hF iv n1 Kc m
  rw [sumTo_congr _ (fun H _ => Nat.mul_left_comm _ _ _), ← sumTo_mul, Nat.mul_left_comm, Nat.mul_assoc]
  exact Nat.mul_le_mul_left _ h

/-- **The hypotheses at the full-width instance**: `κ` reads the capacity
    `c` of `r1 + R1 (r2 + R2 c)`, below `C`. -/
theorem load_satPT {R1 R2 C : Nat} (hR2 : 0 < R2) (hC : 0 < C) (u : Nat) : ((u / R1) % (R2 * C)) / R2 < C :=
  (Nat.div_lt_iff_lt_mul hR2).2 (by
    have := Nat.mod_lt (u / R1) (Nat.mul_pos hR2 hC)
    exact Nat.lt_of_lt_of_le this (Nat.le_of_eq (Nat.mul_comm R2 C)))

/-- **`zkbT_avg` asking each table's bound only where its weight is
    nonzero.** -/
theorem zkbT_avgW {T X C V : Type} {K M : Nat} (w : Nat → Nat) (ST : (T → Nat) → Nat) (sm : (X → Nat) → Nat)
    (SC : (C → Nat) → Nat) (rv : Nat → T → X → V) (pg : Nat → T → C → X → T) (sv : Nat → T → C → X → V)
    (ε : Nat → Nat) (h : ∀ P, P < M → w P ≠ 0 → ZKBT ST K sm SC (rv P) (pg P) (sv P) (ε P)) :
    ZKBT (fun f : Nat × T → Nat => sumTo M (fun P => w P * ST (fun H => f (P, H)))) K sm SC
      (fun PH x => rv PH.1 PH.2 x) (fun PH c x => (PH.1, pg PH.1 PH.2 c x)) (fun PH c x => sv PH.1 PH.2 c x)
      (sumTo M (fun P => w P * ε P)) := by
  intro E
  show K * sumTo M (fun P => w P * ST (fun H => sm (fun x => indB (E (P, H) (rv P H x))))) ≤
    sumTo M (fun P => w P * ST (fun H => SC (fun c => sm (fun x => indB (E (P, pg P H c x) (sv P H c x)))))) +
      sumTo M (fun P => w P * ε P)
  rw [sumTo_mul, ← sumTo_add]
  refine sumTo_mono _ (fun P hP => ?_)
  rw [Nat.mul_left_comm, ← Nat.mul_add]
  by_cases hw : w P = 0
  · rw [hw, Nat.zero_mul, Nat.zero_mul]; exact Nat.le_refl _
  · exact Nat.mul_le_mul_left _ (h P hP hw (fun H v => E (P, H) v))

theorem permB_of_indB {K P : Nat} (h : indB (permB K P) ≠ 0) : permB K P = true := by
  cases e : permB K P
  · rw [e] at h; exact absurd rfl h
  · rfl

/-- The fourth table's index one absorption after the first commitment,
    under the permutation `H`. -/
def loadφ {W : Type} (K : Nat) (inner : Nat → Nat → Nat) (iv n1 : Nat) (enc : Nat → W → List Nat) (H : Nat) :
    Nat → Nat → W → Nat :=
  fun _ m w => idx1 K inner iv ((enc (m / n1) w).getD 0 0) (m % n1) H

/-- The spread the permutation `H` gives proof `ix`: `δ0 ix loadM`. -/
def δsL (K : Nat) (inner : Nat → Nat → Nat) (iv n1 : Nat) (κ : Nat → Nat) (Kc m : Nat) (δ0 : Nat → Nat) (H ix : Nat) : Nat :=
  δ0 ix * loadM K inner iv n1 κ Kc m H

section
open B Air Stmt Mach Sudoku SudokuText Compose CompM Wit

set_option maxRecDepth 100000 in
/-- **`sud_interleaveS` averaged over a uniform permutation, the index one
    absorption after the first commitment** (`loadφ`): at each permutation
    table `P` with `δsL P = δ0 loadM` (`load_hsp`); the error the
    permutation-weighted sum of the tables' errors (`zkbT_avgW`). -/
theorem sud_interleaveL {V Wv P1 P2 P3 W1 W2 W3 : Type} {kr kq : Nat} (φ1 : Nat → Nat → W1 → Nat) (nx1 : Nat → Nat → Nat → List Nat → Nat × Nat × W1) (G1 : Nat → Nat → Nat → List (List (List F)) → Nat → List Nat → P1) (φ2 : Nat → Nat → W2 → Nat) (nx2 : Nat → Nat → Nat → List Nat → Nat × Nat × W2) (G2 : Nat → Nat → Nat → List (List (List F)) → Nat → List Nat → P2) (φ3 : Nat → Nat → W3 → Nat) (nx3 : Nat → Nat → Nat → List Nat → Nat × Nat × W3) (G3 : Nat → Nat → Nat → List (List (List (List F))) × List (List (List F)) → Nat → List Nat → P3)
     (off : EF → String → EF) {puzzle : ∀ ix : Nat, List Nat} (hc : ∀ ix : Nat, CluesOK (cluesOf (puzzle ix))) {ρ : ∀ ix : Nat, Nat → Bool} {A : ∀ ix : Nat, List Cell} {k : ∀ ix : Nat, Nat} {row : ∀ ix : Nat, Nat → Air.Row} (hA : ∀ ix : Nat, AcceptsFrom (A ix) (stmtMachine (ρ ix) 729 (sudokuExpr (cluesOf (puzzle ix))) ACC REJ) (k ix) (row ix)) (hacc : ∀ ix : Nat, rd (A ix) ((row ix) ((k ix) - 1)).ctr ((row ix) ((k ix) - 1)).hd = some (.atom ACC)) (hlen : ∀ ix : Nat, (A ix).length = 2 ^ 16) (hk : ∀ ix : Nat, (k ix) ≤ 2 ^ 16) {tP : ∀ ix : Nat, Nat} (htp : ∀ ix : Nat, (tP ix) = progTp (stmtMachine (fun _ => false) 729 (sudokuExpr (cluesOf (puzzle ix))) ACC REJ).heap) (S16 S10 SP : ∀ ix : Nat, Nat → List F) (qv : ∀ ix : Nat, EF → EF → List EF → F → List F → List F → List EF) (wm wc ww wp : ∀ ix : Nat, Nat → List (EF → EF → List F)) {Lwm Lwc Lww Lwp : ∀ ix : Nat, Nat} (hlwm : ∀ ix : Nat, ∀ c, ((wm ix) c).length = (Lwm ix)) (hlwc : ∀ ix : Nat, ∀ c, ((wc ix) c).length = (Lwc ix)) (hlww : ∀ ix : Nat, ∀ c, ((ww ix) c).length = (Lww ix)) (hlwp : ∀ ix : Nat, ∀ c, ((wp ix) c).length = (Lwp ix)) {K2 K4 : Nat} (hK2 : 0 < K2) (hK4 : 0 < K4) (hS16 : ∀ ix : Nat, ∀ c4, ∀ x ∈ (S16 ix) c4, x ∉ cosetL 1 (bbGen 16) (2 ^ 16)) (hS10 : ∀ ix : Nat, ∀ c4, ∀ x ∈ (S10 ix) c4, x ∉ cosetL 1 (bbGen 10) (2 ^ 10)) (hSP : ∀ ix : Nat, ∀ c4, ∀ x ∈ (SP ix) c4, x ∉ cosetL 1 (bbGen ((tP ix) + 1)) (2 ^ ((tP ix) + 1))) (hsz16 : ∀ ix : Nat, ∀ c4, 2 * ((S16 ix) c4).length + 8 ≤ 2 ^ 16) (hsz : ∀ ix : Nat, ∀ c4, 2 * ((S10 ix) c4).length + 8 ≤ 2 ^ 10) (hszP : ∀ ix : Nat, ∀ c4, 2 * ((SP ix) c4).length + 8 ≤ 2 ^ ((tP ix) + 1)) {ncw : ∀ ix : Nat, Nat} (αd : ∀ ix : Nat, Nat → EF) {B4 : ∀ ix : Nat, Nat} (hB4 : ∀ ix : Nat, sumTo K4 (fun c4 => indB (!genB ((αd ix) c4))) ≤ (B4 ix)) (fri : ∀ ix : Nat, Nat → EF → EF → List (EF → EF) → V) (hncw : ∀ ix : Nat, 4 ≤ (ncw ix)) (NR2 : ∀ ix : Nat, Nat) (Rb : ∀ ix : Nat, Nat → EF → EF → Nat → List (EF → EF)) (Ro : ∀ ix : Nat, Nat → EF → EF → Nat → Wv) {n1 n2 n3 : Nat} {NS1 NS2 NS3 : ∀ ix : Nat, Nat} (Com1 : ∀ ix : Nat, List (List (List F)) → Nat → Nat) (hc1 : ∀ ix : Nat, ComHides (NS1 ix) (Com1 ix)) (hp1 : ∀ ix : Nat, ∀ c4 T1 T2 T3 T4 M, ComPfHides (NS1 ix) (Com1 ix) ((pfRdM (Q4 * Q4) K2 Q4 K4 n1 kr (φ1 ix) (nx1 ix) (G1 ix)) c4 T1 T2 T3 T4 M) (opF ((sudGroups (tP ix) ((S16 ix) c4) ((S10 ix) c4) ((SP ix) c4) EF.zero (qv ix)).map (·.base.S)) [0, 2, 4, 6])) (hr1 : ∀ ix : Nat, ∀ d σ, (Com1 ix) d σ < n1) (d1 : ∀ ix : Nat, List (List (List F))) (Com2 : ∀ ix : Nat, List (List (List F)) → Nat → Nat) (hc2 : ∀ ix : Nat, ComHides (NS2 ix) (Com2 ix)) (hp2 : ∀ ix : Nat, ∀ c4 T1 T2 T3 T4 M, ComPfHides (NS2 ix) (Com2 ix) ((pfRdM (Q4 * Q4) K2 Q4 K4 n1 kr (φ2 ix) (nx2 ix) (G2 ix)) c4 T1 T2 T3 T4 M) (opF ((sudGroups (tP ix) ((S16 ix) c4) ((S10 ix) c4) ((SP ix) c4) EF.zero (qv ix)).map (·.base.S)) [1, 3, 5, 7])) (hr2 : ∀ ix : Nat, ∀ d σ, (Com2 ix) d σ < n2) (d2 : ∀ ix : Nat, List (List (List F))) (Com3 : ∀ ix : Nat, List (List (List (List F))) × List (List (List F)) → Nat → Nat) (hc3 : ∀ ix : Nat, ComHides (NS3 ix) (Com3 ix)) (hp3 : ∀ ix : Nat, ∀ c4 T1 T2 T3 T4 M, ComPfHides (NS3 ix) (Com3 ix) ((pfRdM (Q4 * Q4) K2 Q4 K4 n1 kr (φ3 ix) (nx3 ix) (G3 ix)) c4 T1 T2 T3 T4 M) (fun d => (opQ (sudSsT ((S16 ix) c4) ((S10 ix) c4) ((SP ix) c4)) d.1, opCw (sudSsC (tP ix) ((S16 ix) c4) ((S10 ix) c4) ((SP ix) c4)) d.2))) (hr3 : ∀ ix : Nat, ∀ d σ, (Com3 ix) d σ < n3) (d3 : ∀ ix : Nat, List (List (List (List F))) × List (List (List F)))
    {Kp : Nat} (hKp : 0 < Kp) (inner : Nat → Nat → Nat) (hin : ∀ s x, inner s x < Kp) (κ : Nat → Nat) {Kc : Nat}
    (hκ : ∀ u, κ u < Kc) (hpk : ∀ x s s', inner s x = inner s' x → κ s = κ s') (iv : Nat)
    (hd : ∀ a b, a < n1 → b < n1 → a ≠ b → inner iv a ≠ inner iv b)
    (enc : Nat → Option (List (List (List EF)) × List (List (List (List EF))) × List (List (List EF))) → List Nat) (δ0 : Nat → Nat)
    (hsp1 : ∀ ix d v, sumTo (NS1 ix) (fun σ => indB (decide (Com1 ix d σ = v))) ≤ δ0 ix) {m : Nat} (hm : 2 ≤ m)
    (isQ : Nat → Bool) (nxtQ : Nat → List Nat → Nat × Nat × Unit) :
    ∀ n, ZKBT (fun (f : Nat × (Nat × Nat × Nat × Nat) → Nat) => sumTo (Kp ^ Kp) (fun P => indB (permB Kp P) *
        (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo (K4 ^ Kp) (fun H4 => sumTo ((Q4 * Q4) ^ n1) (fun H1 => sumTo (K2 ^ (n1 * n2)) (fun H2 => sumTo (Q4 ^ (n1 * (n2 * n3))) (fun H3 => f (H1, H2, H3, H4)))))) (fun H => f (P, H))))
      (KPowD (fun _ => (K4 * (Q4 * Q4 * (K2 * Q4)))) n)
      (smPowD (X := fun _ => Nat × Nat × Nat × (Nat → Tup)) (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφ Kp inner iv n1 enc 0) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).sm 2) n)
      (scPowD (C := fun _ => Nat × Nat × Nat × Nat) (fun _ => (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo K4 (fun c4 => sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo Q4 (fun c3 => f (c1, c2, c3, c4))))))) n)
      (fun PH x => (rvPowD (mixRv (Q4 * Q4) K2 Q4 K4 kq isQ nxtQ
        (fun i => read4T (Q4 * Q4) K2 Q4 K4 ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφ Kp inner iv n1 enc PH.1) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).m1 ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφ Kp inner iv n1 enc PH.1) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).m2 ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφ Kp inner iv n1 enc PH.1) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).m3 ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφ Kp inner iv n1 enc PH.1) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).q ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφ Kp inner iv n1 enc PH.1) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).out)) n) PH.2 x)
      (fun PH c x => (PH.1, (pgPowD (pgRd (Q4 * Q4) K2 Q4 K4 (fun i => !isQ i) (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφ Kp inner iv n1 enc PH.1) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).pts) (fun _ c => c)) n) PH.2 c x))
      (fun PH c x => (svPowDT (pgRd (Q4 * Q4) K2 Q4 K4 (fun i => !isQ i) (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφ Kp inner iv n1 enc PH.1) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).pts) (fun _ c => c))
        (mixSv (Q4 * Q4) K2 Q4 K4 kq isQ nxtQ (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφ Kp inner iv n1 enc PH.1) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).sv)) n) PH.2 c x)
      (sumTo (Kp ^ Kp) (fun P => indB (permB Kp P) * (errPowD (fun _ => (K4 * (Q4 * Q4 * (K2 * Q4)))) (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφ Kp inner iv n1 enc P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).sm 2) (fun _ => (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo K4 (fun c4 => sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo Q4 (fun c3 => f (c1, c2, c3, c4))))))) (fun i => cond (isQ i) 0 ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφ Kp inner iv n1 enc P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).ε)
        (fun n => (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo K4 (fun c4 => sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo Q4 (fun c3 => f (c1, c2, c3, c4)))))) (fun _ => (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo (K4 ^ Kp) (fun H4 => sumTo ((Q4 * Q4) ^ n1) (fun H1 => sumTo (K2 ^ (n1 * n2)) (fun H2 => sumTo (Q4 ^ (n1 * (n2 * n3))) (fun H3 => f (H1, H2, H3, H4)))))) (fun _ => smPowD (X := fun _ => Nat × Nat × Nat × (Nat → Tup)) (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφ Kp inner iv n1 enc P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).sm 2) n
          (fun _ => rSum (fun i => cond (isQ i) kq (4 + 3 * kr)) n *
            cond (isQ n) 0 (((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφ Kp inner iv n1 enc P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) n).NS * (((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφ Kp inner iv n1 enc P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) n).NR * (Q4 ^ 2 * δsL Kp inner iv n1 κ Kc m δ0 P n))))))) n))) := by
  intro n
  exact zkbT_avgW (fun P => indB (permB Kp P)) (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo (K4 ^ Kp) (fun H4 => sumTo ((Q4 * Q4) ^ n1) (fun H1 => sumTo (K2 ^ (n1 * n2)) (fun H2 => sumTo (Q4 ^ (n1 * (n2 * n3))) (fun H3 => f (H1, H2, H3, H4)))))) (smPowD (X := fun _ => Nat × Nat × Nat × (Nat → Tup)) (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφ Kp inner iv n1 enc 0) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).sm 2) n) (scPowD (C := fun _ => Nat × Nat × Nat × Nat) (fun _ => (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo K4 (fun c4 => sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo Q4 (fun c3 => f (c1, c2, c3, c4))))))) n)
    (fun P => (rvPowD (mixRv (Q4 * Q4) K2 Q4 K4 kq isQ nxtQ
        (fun i => read4T (Q4 * Q4) K2 Q4 K4 ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφ Kp inner iv n1 enc P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).m1 ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφ Kp inner iv n1 enc P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).m2 ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφ Kp inner iv n1 enc P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).m3 ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφ Kp inner iv n1 enc P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).q ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφ Kp inner iv n1 enc P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).out)) n)) (fun P => (pgPowD (pgRd (Q4 * Q4) K2 Q4 K4 (fun i => !isQ i) (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφ Kp inner iv n1 enc P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).pts) (fun _ c => c)) n)) (fun P => (svPowDT (pgRd (Q4 * Q4) K2 Q4 K4 (fun i => !isQ i) (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφ Kp inner iv n1 enc P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).pts) (fun _ c => c))
        (mixSv (Q4 * Q4) K2 Q4 K4 kq isQ nxtQ (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφ Kp inner iv n1 enc P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).sv)) n))
    (fun P => (errPowD (fun _ => (K4 * (Q4 * Q4 * (K2 * Q4)))) (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφ Kp inner iv n1 enc P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).sm 2) (fun _ => (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo K4 (fun c4 => sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo Q4 (fun c3 => f (c1, c2, c3, c4))))))) (fun i => cond (isQ i) 0 ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφ Kp inner iv n1 enc P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).ε)
        (fun n => (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo K4 (fun c4 => sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo Q4 (fun c3 => f (c1, c2, c3, c4)))))) (fun _ => (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo (K4 ^ Kp) (fun H4 => sumTo ((Q4 * Q4) ^ n1) (fun H1 => sumTo (K2 ^ (n1 * n2)) (fun H2 => sumTo (Q4 ^ (n1 * (n2 * n3))) (fun H3 => f (H1, H2, H3, H4)))))) (fun _ => smPowD (X := fun _ => Nat × Nat × Nat × (Nat → Tup)) (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφ Kp inner iv n1 enc P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).sm 2) n
          (fun _ => rSum (fun i => cond (isQ i) kq (4 + 3 * kr)) n *
            cond (isQ n) 0 (((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφ Kp inner iv n1 enc P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) n).NS * (((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφ Kp inner iv n1 enc P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) n).NR * (Q4 ^ 2 * δsL Kp inner iv n1 κ Kc m δ0 P n))))))) n)) (fun P _ hw =>
    sud_interleaveS φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3 off hc hA hacc hlen hk htp S16 S10 SP qv wm wc ww wp hlwm hlwc hlww hlwp
      hK2 hK4 (loadφ Kp inner iv n1 enc P) (fun _ _ _ => rget_lt hKp _ _) hS16 hS10 hSP hsz16 hsz hszP αd hB4 fri hncw NR2 Rb Ro
      Com1 hc1 hp1 hr1 d1 Com2 hc2 hp2 hr2 d2 Com3 hc3 hp3 hr3 d3 (δsL Kp inner iv n1 κ Kc m δ0 P)
      (fun ix => (load_hsp inner hin κ hκ hpk iv hd enc (Com1 ix) (hr1 ix) (hsp1 ix) hm (permB_of_indB hw)).1)
      (fun ix => (load_hsp inner hin κ hκ hpk iv hd enc (Com1 ix) (hr1 ix) (hsp1 ix) hm (permB_of_indB hw)).2) isQ nxtQ n)


-- The statement unfolds `sudDD`'s fields at every `ix`; elaborating it exceeds the default heartbeats.
set_option maxHeartbeats 1600000 in
set_option maxRecDepth 100000 in
/-- **`sud_interleaveL` with a number for its error**: `Kq = m! (Kp - n1)^m`
    times the averaged real count is at most `Kq` times the averaged
    simulation plus `errPowD` at the errors `Kq W ε` and each spread
    `δ0 i (m! (Kp - n1)^m (m - 1) + n1 Kc (n1 F)^m) W`, `W` the number of
    permutation tables (`avg_err_bound`, `load_δs_countP`). -/
theorem sud_interleaveLN {V Wv P1 P2 P3 W1 W2 W3 : Type} {kr kq : Nat} (φ1 : Nat → Nat → W1 → Nat) (nx1 : Nat → Nat → Nat → List Nat → Nat × Nat × W1) (G1 : Nat → Nat → Nat → List (List (List F)) → Nat → List Nat → P1) (φ2 : Nat → Nat → W2 → Nat) (nx2 : Nat → Nat → Nat → List Nat → Nat × Nat × W2) (G2 : Nat → Nat → Nat → List (List (List F)) → Nat → List Nat → P2) (φ3 : Nat → Nat → W3 → Nat) (nx3 : Nat → Nat → Nat → List Nat → Nat × Nat × W3) (G3 : Nat → Nat → Nat → List (List (List (List F))) × List (List (List F)) → Nat → List Nat → P3)
     (off : EF → String → EF) {puzzle : ∀ ix : Nat, List Nat} (hc : ∀ ix : Nat, CluesOK (cluesOf (puzzle ix))) {ρ : ∀ ix : Nat, Nat → Bool} {A : ∀ ix : Nat, List Cell} {k : ∀ ix : Nat, Nat} {row : ∀ ix : Nat, Nat → Air.Row} (hA : ∀ ix : Nat, AcceptsFrom (A ix) (stmtMachine (ρ ix) 729 (sudokuExpr (cluesOf (puzzle ix))) ACC REJ) (k ix) (row ix)) (hacc : ∀ ix : Nat, rd (A ix) ((row ix) ((k ix) - 1)).ctr ((row ix) ((k ix) - 1)).hd = some (.atom ACC)) (hlen : ∀ ix : Nat, (A ix).length = 2 ^ 16) (hk : ∀ ix : Nat, (k ix) ≤ 2 ^ 16) {tP : ∀ ix : Nat, Nat} (htp : ∀ ix : Nat, (tP ix) = progTp (stmtMachine (fun _ => false) 729 (sudokuExpr (cluesOf (puzzle ix))) ACC REJ).heap) (S16 S10 SP : ∀ ix : Nat, Nat → List F) (qv : ∀ ix : Nat, EF → EF → List EF → F → List F → List F → List EF) (wm wc ww wp : ∀ ix : Nat, Nat → List (EF → EF → List F)) {Lwm Lwc Lww Lwp : ∀ ix : Nat, Nat} (hlwm : ∀ ix : Nat, ∀ c, ((wm ix) c).length = (Lwm ix)) (hlwc : ∀ ix : Nat, ∀ c, ((wc ix) c).length = (Lwc ix)) (hlww : ∀ ix : Nat, ∀ c, ((ww ix) c).length = (Lww ix)) (hlwp : ∀ ix : Nat, ∀ c, ((wp ix) c).length = (Lwp ix)) {K2 K4 : Nat} (hK2 : 0 < K2) (hK4 : 0 < K4) (hS16 : ∀ ix : Nat, ∀ c4, ∀ x ∈ (S16 ix) c4, x ∉ cosetL 1 (bbGen 16) (2 ^ 16)) (hS10 : ∀ ix : Nat, ∀ c4, ∀ x ∈ (S10 ix) c4, x ∉ cosetL 1 (bbGen 10) (2 ^ 10)) (hSP : ∀ ix : Nat, ∀ c4, ∀ x ∈ (SP ix) c4, x ∉ cosetL 1 (bbGen ((tP ix) + 1)) (2 ^ ((tP ix) + 1))) (hsz16 : ∀ ix : Nat, ∀ c4, 2 * ((S16 ix) c4).length + 8 ≤ 2 ^ 16) (hsz : ∀ ix : Nat, ∀ c4, 2 * ((S10 ix) c4).length + 8 ≤ 2 ^ 10) (hszP : ∀ ix : Nat, ∀ c4, 2 * ((SP ix) c4).length + 8 ≤ 2 ^ ((tP ix) + 1)) {ncw : ∀ ix : Nat, Nat} (αd : ∀ ix : Nat, Nat → EF) {B4 : ∀ ix : Nat, Nat} (hB4 : ∀ ix : Nat, sumTo K4 (fun c4 => indB (!genB ((αd ix) c4))) ≤ (B4 ix)) (fri : ∀ ix : Nat, Nat → EF → EF → List (EF → EF) → V) (hncw : ∀ ix : Nat, 4 ≤ (ncw ix)) (NR2 : ∀ ix : Nat, Nat) (Rb : ∀ ix : Nat, Nat → EF → EF → Nat → List (EF → EF)) (Ro : ∀ ix : Nat, Nat → EF → EF → Nat → Wv) {n1 n2 n3 : Nat} {NS1 NS2 NS3 : ∀ ix : Nat, Nat} (Com1 : ∀ ix : Nat, List (List (List F)) → Nat → Nat) (hc1 : ∀ ix : Nat, ComHides (NS1 ix) (Com1 ix)) (hp1 : ∀ ix : Nat, ∀ c4 T1 T2 T3 T4 M, ComPfHides (NS1 ix) (Com1 ix) ((pfRdM (Q4 * Q4) K2 Q4 K4 n1 kr (φ1 ix) (nx1 ix) (G1 ix)) c4 T1 T2 T3 T4 M) (opF ((sudGroups (tP ix) ((S16 ix) c4) ((S10 ix) c4) ((SP ix) c4) EF.zero (qv ix)).map (·.base.S)) [0, 2, 4, 6])) (hr1 : ∀ ix : Nat, ∀ d σ, (Com1 ix) d σ < n1) (d1 : ∀ ix : Nat, List (List (List F))) (Com2 : ∀ ix : Nat, List (List (List F)) → Nat → Nat) (hc2 : ∀ ix : Nat, ComHides (NS2 ix) (Com2 ix)) (hp2 : ∀ ix : Nat, ∀ c4 T1 T2 T3 T4 M, ComPfHides (NS2 ix) (Com2 ix) ((pfRdM (Q4 * Q4) K2 Q4 K4 n1 kr (φ2 ix) (nx2 ix) (G2 ix)) c4 T1 T2 T3 T4 M) (opF ((sudGroups (tP ix) ((S16 ix) c4) ((S10 ix) c4) ((SP ix) c4) EF.zero (qv ix)).map (·.base.S)) [1, 3, 5, 7])) (hr2 : ∀ ix : Nat, ∀ d σ, (Com2 ix) d σ < n2) (d2 : ∀ ix : Nat, List (List (List F))) (Com3 : ∀ ix : Nat, List (List (List (List F))) × List (List (List F)) → Nat → Nat) (hc3 : ∀ ix : Nat, ComHides (NS3 ix) (Com3 ix)) (hp3 : ∀ ix : Nat, ∀ c4 T1 T2 T3 T4 M, ComPfHides (NS3 ix) (Com3 ix) ((pfRdM (Q4 * Q4) K2 Q4 K4 n1 kr (φ3 ix) (nx3 ix) (G3 ix)) c4 T1 T2 T3 T4 M) (fun d => (opQ (sudSsT ((S16 ix) c4) ((S10 ix) c4) ((SP ix) c4)) d.1, opCw (sudSsC (tP ix) ((S16 ix) c4) ((S10 ix) c4) ((SP ix) c4)) d.2))) (hr3 : ∀ ix : Nat, ∀ d σ, (Com3 ix) d σ < n3) (d3 : ∀ ix : Nat, List (List (List (List F))) × List (List (List F)))
    {Kp : Nat} (hKp : 0 < Kp) (inner : Nat → Nat → Nat) (hin : ∀ s x, inner s x < Kp) (κ : Nat → Nat) {Kc : Nat}
    (hκ : ∀ u, κ u < Kc) (hpk : ∀ x s s', inner s x = inner s' x → κ s = κ s') (iv : Nat)
    (hd : ∀ a b, a < n1 → b < n1 → a ≠ b → inner iv a ≠ inner iv b)
    (enc : Nat → Option (List (List (List EF)) × List (List (List (List EF))) × List (List (List EF))) → List Nat) (δ0 : Nat → Nat) {F : Nat} (hF : ∀ v, sumTo Kp (fun u => indB (decide (κ u = v))) ≤ F)
    (hsp1 : ∀ ix d v, sumTo (NS1 ix) (fun σ => indB (decide (Com1 ix d σ = v))) ≤ δ0 ix) {m : Nat} (hm : 2 ≤ m)
    (isQ : Nat → Bool) (nxtQ : Nat → List Nat → Nat × Nat × Unit) :
    ∀ n (E : Nat × (Nat × Nat × Nat × Nat) → _ → Bool),
      (fact m * (Kp - n1) ^ m) * ((KPowD (fun _ => (K4 * (Q4 * Q4 * (K2 * Q4)))) n) * (fun (f : Nat × (Nat × Nat × Nat × Nat) → Nat) => sumTo (Kp ^ Kp) (fun P => indB (permB Kp P) * (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo (K4 ^ Kp) (fun H4 => sumTo ((Q4 * Q4) ^ n1) (fun H1 => sumTo (K2 ^ (n1 * n2)) (fun H2 => sumTo (Q4 ^ (n1 * (n2 * n3))) (fun H3 => f (H1, H2, H3, H4)))))) (fun H => f (P, H)))) (fun H => (smPowD (X := fun _ => Nat × Nat × Nat × (Nat → Tup)) (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφ Kp inner iv n1 enc 0) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).sm 2) n) (fun x => indB (E H ((fun PH x => (rvPowD (mixRv (Q4 * Q4) K2 Q4 K4 kq isQ nxtQ
        (fun i => read4T (Q4 * Q4) K2 Q4 K4 ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφ Kp inner iv n1 enc PH.1) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).m1 ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφ Kp inner iv n1 enc PH.1) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).m2 ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφ Kp inner iv n1 enc PH.1) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).m3 ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφ Kp inner iv n1 enc PH.1) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).q ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφ Kp inner iv n1 enc PH.1) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).out)) n) PH.2 x) H x))))) ≤
        (fact m * (Kp - n1) ^ m) * (fun (f : Nat × (Nat × Nat × Nat × Nat) → Nat) => sumTo (Kp ^ Kp) (fun P => indB (permB Kp P) * (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo (K4 ^ Kp) (fun H4 => sumTo ((Q4 * Q4) ^ n1) (fun H1 => sumTo (K2 ^ (n1 * n2)) (fun H2 => sumTo (Q4 ^ (n1 * (n2 * n3))) (fun H3 => f (H1, H2, H3, H4)))))) (fun H => f (P, H)))) (fun H => (scPowD (C := fun _ => Nat × Nat × Nat × Nat) (fun _ => (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo K4 (fun c4 => sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo Q4 (fun c3 => f (c1, c2, c3, c4))))))) n) (fun c => (smPowD (X := fun _ => Nat × Nat × Nat × (Nat → Tup)) (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφ Kp inner iv n1 enc 0) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).sm 2) n) (fun x => indB (E ((fun PH c x => (PH.1, (pgPowD (pgRd (Q4 * Q4) K2 Q4 K4 (fun i => !isQ i) (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφ Kp inner iv n1 enc PH.1) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).pts) (fun _ c => c)) n) PH.2 c x)) H c x) ((fun PH c x => (svPowDT (pgRd (Q4 * Q4) K2 Q4 K4 (fun i => !isQ i) (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφ Kp inner iv n1 enc PH.1) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).pts) (fun _ c => c))
        (mixSv (Q4 * Q4) K2 Q4 K4 kq isQ nxtQ (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφ Kp inner iv n1 enc PH.1) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).sv)) n) PH.2 c x) H c x))))) +
        errPowD (fun _ => (K4 * (Q4 * Q4 * (K2 * Q4)))) (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφ Kp inner iv n1 enc 0) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).sm 2) (fun _ => (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo K4 (fun c4 => sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo Q4 (fun c3 => f (c1, c2, c3, c4))))))) (fun i => (fact m * (Kp - n1) ^ m) * (sumTo (Kp ^ Kp) (fun P => indB (permB Kp P))) * (fun i => cond (isQ i) 0 ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφ Kp inner iv n1 enc 0) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).ε) i) (fun i => (fun n x => (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo K4 (fun c4 => sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo Q4 (fun c3 => f (c1, c2, c3, c4)))))) (fun _ => (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo (K4 ^ Kp) (fun H4 => sumTo ((Q4 * Q4) ^ n1) (fun H1 => sumTo (K2 ^ (n1 * n2)) (fun H2 => sumTo (Q4 ^ (n1 * (n2 * n3))) (fun H3 => f (H1, H2, H3, H4)))))) (fun _ => smPowD (X := fun _ => Nat × Nat × Nat × (Nat → Tup)) (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφ Kp inner iv n1 enc 0) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).sm 2) n
          (fun _ => rSum (fun i => cond (isQ i) kq (4 + 3 * kr)) n *
            cond (isQ n) 0 (((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφ Kp inner iv n1 enc 0) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) n).NS * (((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφ Kp inner iv n1 enc 0) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) n).NR * (Q4 ^ 2 * x))))))) i ((fun i => δ0 i * ((fact m * ((Kp - n1) ^ m * (m - 1)) + n1 * (Kc * (n1 * F) ^ m)) * (sumTo (Kp ^ Kp) (fun P => indB (permB Kp P))))) i)) n := by
  intro n E
  have h := sud_interleaveL (kq := kq) φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3 off hc hA hacc hlen hk htp S16 S10 SP qv wm wc ww wp hlwm hlwc hlww hlwp hK2 hK4 hS16 hS10 hSP hsz16 hsz hszP αd hB4 fri hncw NR2 Rb Ro Com1 hc1 hp1 hr1 d1 Com2 hc2 hp2 hr2 d2 Com3 hc3 hp3 hr3 d3 hKp inner hin κ hκ hpk iv hd enc δ0 hsp1 hm isQ nxtQ n
  have hb := (avg_err_bound (fun _ => (K4 * (Q4 * Q4 * (K2 * Q4)))) (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφ Kp inner iv n1 enc 0) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).sm 2) (fun _ => (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo K4 (fun c4 => sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo Q4 (fun c3 => f (c1, c2, c3, c4))))))) (fun i => cond (isQ i) 0 ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφ Kp inner iv n1 enc 0) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).ε) (Kp ^ Kp) (fun P => indB (permB Kp P))
      (fun P i => δsL Kp inner iv n1 κ Kc m δ0 P i) (fun n x => (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo K4 (fun c4 => sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo Q4 (fun c3 => f (c1, c2, c3, c4)))))) (fun _ => (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo (K4 ^ Kp) (fun H4 => sumTo ((Q4 * Q4) ^ n1) (fun H1 => sumTo (K2 ^ (n1 * n2)) (fun H2 => sumTo (Q4 ^ (n1 * (n2 * n3))) (fun H3 => f (H1, H2, H3, H4)))))) (fun _ => smPowD (X := fun _ => Nat × Nat × Nat × (Nat → Tup)) (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφ Kp inner iv n1 enc 0) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).sm 2) n
          (fun _ => rSum (fun i => cond (isQ i) kq (4 + 3 * kr)) n *
            cond (isQ n) 0 (((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφ Kp inner iv n1 enc 0) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) n).NS * (((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφ Kp inner iv n1 enc 0) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) n).NR * (Q4 ^ 2 * x)))))))
      (fun i x => wrap_scale (lin_sum4 _ _ _ _) (lin_sum4 _ _ _ _) (lin_smPowD (fun _ => lin_sm _ _ _ _) i) _ _ _ _ _ x)
      (fact m * (Kp - n1) ^ m) (fun i => δ0 i * ((fact m * ((Kp - n1) ^ m * (m - 1)) + n1 * (Kc * (n1 * F) ^ m)) * (sumTo (Kp ^ Kp) (fun P => indB (permB Kp P))))) (fun i => load_δs_countP hKp inner hin κ hF iv n1 Kc m (δ0 i)) n)
  exact zkbT_err_le h _ _ hb E

end

end Circuit
