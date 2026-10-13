import Ski.ZK.SpongeAvg

/-!
# Many near-collisions are rare under a uniform permutation

`SpongeIndex` bounds the index's preimage by one plus the meeting pairs,
which costs `n1²` and fails at Plonky3's widths.  A sharper count needs
many near-collisions to be rare together.  Here an adaptive run under a
uniform permutation makes `B` fresh answers near an earlier one (`nearN`),
each answer near at most `F` of the `K` values.

- **Lazy sampling kept on the guard.** `fresh_countPG` is `fresh_countP`
  with its right side restricted to the guard's tables, so a guard may
  carry a weight read off the history (`weight_split`).
- **Factorial moments.** `E[B choose m]` is at most `eS k m / (K - k)^m`,
  `eS k m` the `m`-th elementary symmetric sum of `0, F, …, (k-1)F`
  (`nearN_moment`): Pascal's rule over the newest query, its fresh answer
  near an earlier one on at most `k F / (K - k)` of the tables carrying the
  history's binomial.
- **Tail.** `m! eS k m ≤ ((0 + ⋯ + (k-1)) F)^m` (`eS_le`), so at least `m`
  near-collisions occur on at most
  `((0 + ⋯ + (k-1)) F)^m / (m! (K - k)^m)` of the permutation tables
  (`nearN_tail`): the `m`-th power of the birthday term over `m!`.

Not shown: the step from this tail to the index's preimage.  Running all
`n1` first commitments as one adaptive run, `s` chains reaching one state
should need `s - 1` near-collisions, which would bound the preimage by
`m` outside an event of mass `(birthday term)^m / m!`.
-/

set_option autoImplicit false

namespace Circuit
open ZKF

/-- **`fresh_countP` kept on the guard**: the permutation tables where the
    guard holds and the fresh answer lands in `S H`, `K - j` times, are at
    most `k` times the permutation tables where the guard holds. -/
theorem fresh_countPG {K j k : Nat} (hK : 0 < K) (p : Nat → Nat) (hp : ∀ H, p H < K) (g : Nat → Bool) (A S : Nat → List Nat)
    (hA : ∀ H, (A H).length ≤ j) (hS : ∀ H, (S H).length ≤ k)
    (hfr : ∀ H, H < K ^ K → permB K H = true → g H = true → rget K (p H) H ∉ A H)
    (hinv : ∀ H a b, H < K ^ K → a < K → b < K → a ∉ A H → b ∉ A H → permB K H = true → g H = true →
      p (vswap K a b H) = p H ∧ A (vswap K a b H) = A H ∧ S (vswap K a b H) = S H ∧ g (vswap K a b H) = true) :
    (K - j) * sumTo (K ^ K) (fun H => indB (permB K H && g H && decide (rget K (p H) H ∈ S H))) ≤
      k * sumTo (K ^ K) (fun H => indB (permB K H && g H)) := by
  -- the seen-answer test and the hit, as functions of the two values
  let src := fun (c b H : Nat) => indB (permB K H && g H && decide (rget K (p H) H = c) && !decide (b ∈ A H) &&
    decide (c ∈ S H))
  let tgt := fun (c b H : Nat) => indB (permB K H && g H && decide (rget K (p H) H = b) && !decide (c ∈ A H) &&
    decide (c ∈ S H))
  -- each hit table has `K - j` unseen values
  have step1 : ∀ H, (K - j) * indB (permB K H && g H && decide (rget K (p H) H ∈ S H)) ≤
      sumTo K (fun b => sumTo K (fun c => src c b H)) := fun H => by
    cases hE : (permB K H && g H && decide (rget K (p H) H ∈ S H))
    · rw [show indB false = 0 from rfl, Nat.mul_zero]; exact Nat.zero_le _
    · rw [show indB true = 1 from rfl, Nat.mul_one]
      have each : ∀ b, b < K → indB (!decide (b ∈ A H)) ≤ sumTo K (fun c => src c b H) := fun b _ => by
        refine Nat.le_trans (Nat.le_of_eq ?_) (le_sumTo (fun c => src c b H) K (rget_lt hK (p H) H))
        show indB (!decide (b ∈ A H)) = indB (permB K H && g H && decide (rget K (p H) H = rget K (p H) H) &&
          !decide (b ∈ A H) && decide (rget K (p H) H ∈ S H))
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hE
        rw [hE.1.1, hE.1.2, decide_eq_true hE.2, decide_eq_true rfl]
        simp
      refine Nat.le_trans (Nat.le_trans ?_ (count_notmem K (A H))) (sumTo_mono _ each)
      exact Nat.sub_le_sub_left (hA H) K
  -- exchanging the hit value `c` with an unseen `b` moves the hit to `b`
  have step2 : ∀ c b, c < K → b < K → sumTo (K ^ K) (fun H => src c b H) ≤ sumTo (K ^ K) (fun H => tgt c b H) := by
    intro c b hc hb
    rw [← sumTo_perm (fun H => tgt c b H) (K ^ K) (vswap K c b) (vswap K c b)
      (fun _ _ => vswap_lt hK hc hb _) (fun _ _ => vswap_lt hK hc hb _)
      (fun H hH => vswap_vswap hK hc hb hH) (fun H hH => vswap_vswap hK hc hb hH)]
    refine sumTo_mono _ (fun H hH => ?_)
    cases hs : (permB K H && g H && decide (rget K (p H) H = c) && !decide (b ∈ A H) && decide (c ∈ S H))
    · show indB _ ≤ _; rw [hs]; exact Nat.zero_le _
    · show indB _ ≤ _; rw [hs]
      simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not] at hs
      obtain ⟨⟨⟨⟨hP, hg⟩, hans⟩, hbA⟩, hcS⟩ := hs
      have hcA : c ∉ A H := hans ▸ hfr H hH hP hg
      obtain ⟨e1, e2, e3, e4⟩ := hinv H c b hH hc hb hcA hbA hP hg
      have hpK : p H < K := hp H
      show indB (permB K (vswap K c b H) && g (vswap K c b H) &&
        decide (rget K (p (vswap K c b H)) (vswap K c b H) = b) && !decide (c ∈ A (vswap K c b H)) &&
        decide (c ∈ S (vswap K c b H))) ≥ 1
      rw [permB_vswap hK hc hb hP, e4, e1, e2, e3, rget_vswap hK hc hb hpK, hans]
      simp [swapV, hcA, hcS, indB]
  -- each table holds its hit at one value: at most `k` pairs per permutation table
  have step3 : ∀ H, sumTo K (fun c => sumTo K (fun b => tgt c b H)) ≤ k * indB (permB K H && g H) := fun H => by
    cases hP : permB K H
    · refine Nat.le_of_eq (Eq.trans (sumTo_congr _ (fun c _ => Eq.trans (sumTo_congr _ (fun b _ => ?_))
        (Eq.trans (sumTo_const 0 K) (Nat.mul_zero K)))) (Eq.trans (sumTo_const 0 K) ?_))
      · show indB (permB K H && _ && _ && _ && _) = 0; rw [hP]; rfl
      · simp [indB]
    · cases hg : g H
      · refine Nat.le_of_eq (Eq.trans (sumTo_congr _ (fun c _ => Eq.trans (sumTo_congr _ (fun b _ => ?_))
          (Eq.trans (sumTo_const 0 K) (Nat.mul_zero K)))) (Eq.trans (sumTo_const 0 K) ?_))
        · show indB (permB K H && g H && _ && _ && _) = 0; rw [hg, Bool.and_false]; rfl
        · simp [indB]
      · have each : ∀ c, sumTo K (fun b => tgt c b H) ≤ indB (decide (c ∈ S H)) := fun c => by
          have pt : ∀ b, tgt c b H ≤ indB (decide (c ∈ S H)) * indB (decide (b = rget K (p H) H)) := fun b => by
            show indB (permB K H && g H && decide (rget K (p H) H = b) && !decide (c ∈ A H) && decide (c ∈ S H)) ≤ _
            by_cases e : b = rget K (p H) H
            · rw [decide_eq_true e, show indB true = 1 from rfl, Nat.mul_one]
              cases decide (c ∈ S H) <;> cases (permB K H && g H && decide (rget K (p H) H = b) && !decide (c ∈ A H)) <;>
                simp [indB]
            · rw [decide_eq_false (fun h => e h.symm), decide_eq_false e]; simp [indB]
          refine Nat.le_trans (sumTo_mono _ (fun b _ => pt b)) ?_
          rw [← sumTo_mul]
          calc indB (decide (c ∈ S H)) * sumTo K (fun b => indB (decide (b = rget K (p H) H))) ≤
                indB (decide (c ∈ S H)) * 1 := Nat.mul_le_mul_left _ (sumTo_indEq _ K).1
            _ = indB (decide (c ∈ S H)) := Nat.mul_one _
        refine Nat.le_trans (sumTo_mono _ (fun c _ => each c)) ?_
        rw [Bool.true_and, show indB true = 1 from rfl, Nat.mul_one]
        exact Nat.le_trans (count_mem K (S H)) (hS H)
  rw [sumTo_mul]
  refine Nat.le_trans (sumTo_mono _ (fun H _ => step1 H)) ?_
  rw [sumTo_exch (fun H b => sumTo K (fun c => src c b H)) K (K ^ K)]
  rw [sumTo_congr K (fun b _ => sumTo_exch (fun H c => src c b H) K (K ^ K))]
  refine Nat.le_trans (sumTo_mono _ (fun b hb => sumTo_mono _ (fun c hc => step2 c b hc hb))) ?_
  rw [sumTo_exch (fun b c => sumTo (K ^ K) (fun H => tgt c b H)) K K]
  rw [sumTo_congr K (fun c _ => sumTo_exch (fun b H => tgt c b H) (K ^ K) K)]
  rw [sumTo_exch (fun c H => sumTo K (fun b => tgt c b H)) (K ^ K) K]
  refine Nat.le_trans (sumTo_mono _ (fun H _ => step3 H)) (Nat.le_of_eq ?_)
  rw [sumTo_mul]

theorem indB_and' (a b : Bool) : indB a * indB b = indB (a && b) := by cases a <;> cases b <;> rfl

/-! ### Factorial moments of the near-collisions in an adaptive run -/

/-- Binomial coefficients, by Pascal's rule. -/
def chs : Nat → Nat → Nat
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, m + 1 => chs n m + chs n (m + 1)

theorem chs_le_pow : ∀ n m, chs n m ≤ 2 ^ n
  | n, 0 => by cases n <;> exact Nat.one_le_two_pow
  | 0, _ + 1 => Nat.zero_le _
  | n + 1, m + 1 => by
    show chs n m + chs n (m + 1) ≤ 2 ^ (n + 1)
    rw [Nat.pow_succ, Nat.mul_two]
    exact Nat.add_le_add (chs_le_pow n m) (chs_le_pow n (m + 1))

/-- One more near-collision adds the binomials one rank down. -/
theorem chs_step (n m : Nat) (b : Bool) : chs (n + indB b) (m + 1) = chs n (m + 1) + indB b * chs n m := by
  cases b
  · show chs (n + 0) (m + 1) = chs n (m + 1) + 0 * chs n m; simp
  · show chs (n + 1) (m + 1) = chs n (m + 1) + 1 * chs n m
    rw [Nat.one_mul, Nat.add_comm (chs n (m + 1))]; rfl

/-- The queries, oldest first, that are fresh and answer near an earlier
    answer: near under `cl`, below `K`. -/
def nearN (K : Nat) (cl : Nat → Nat → Bool) : List (Nat × Nat) → Nat
  | [] => 0
  | x :: rest => nearN K cl rest +
    indB (!decide (x.1 ∈ rest.map Prod.fst) && decide (x.2 ∈ nearR K cl (rest.map Prod.snd)))

theorem nearN_le (K : Nat) (cl : Nat → Nat → Bool) : ∀ l : List (Nat × Nat), nearN K cl l ≤ l.length
  | [] => Nat.le_refl _
  | x :: rest => by
    show nearN K cl rest + _ ≤ rest.length + 1
    exact Nat.add_le_add (nearN_le K cl rest) (indB_le _)

theorem count_lt (w : Nat) : ∀ n, w ≤ n → sumTo n (fun u => indB (decide (u < w))) = w
  | 0, h => by rw [Nat.le_zero.1 h]; rfl
  | n + 1, h => by
    show sumTo n _ + indB (decide (n < w)) = w
    rcases Nat.lt_or_ge n w with hl | hl
    · have hw : w = n + 1 := Nat.le_antisymm h hl
      subst hw
      have e : sumTo n (fun u => indB (decide (u < n + 1))) = n :=
        Eq.trans (sumTo_congr _ (fun u hu => by rw [decide_eq_true (Nat.lt_succ_of_lt hu)]; rfl))
          (Eq.trans (sumTo_const 1 n) (Nat.mul_one n))
      rw [e, decide_eq_true hl]; rfl
    · rw [count_lt w n hl, decide_eq_false (Nat.not_lt.2 hl)]; rfl

/-- A weight below `Wb` is its count of thresholds. -/
theorem weight_split (b : Bool) (w Wb : Nat) (hw : w ≤ Wb) :
    indB b * w = sumTo Wb (fun u => indB (b && decide (u < w))) := by
  cases b
  · rw [show indB false = 0 from rfl, Nat.zero_mul]
    exact (Eq.trans (sumTo_congr _ (fun u _ => rfl)) (Eq.trans (sumTo_const 0 Wb) (Nat.mul_zero Wb))).symm
  · rw [show indB true = 1 from rfl, Nat.one_mul]
    exact (count_lt w Wb hw).symm

/-- **Many near-collisions are rare**: over the permutation tables, `k`
    adaptive forward queries make `B` fresh answers near an earlier one
    (`nearN`, each answer near at most `F`); the `m`-th factorial moment
    `E[B choose m]` is at most `eS k m / (K - k)^m`, `eS k m` the `m`-th
    elementary symmetric sum of `0, F, 2F, …, (k-1)F`, at most
    `((0 + ⋯ + (k-1)) F)^m / m!`. -/
def eS (F : Nat) : Nat → Nat → Nat
  | _, 0 => 1
  | 0, _ + 1 => 0
  | k + 1, m + 1 => eS F k (m + 1) + k * F * eS F k m

theorem nearN_moment {K F : Nat} (hK : 0 < K) (cl : Nat → Nat → Bool) (hsym : ∀ a b, cl a b = cl b a)
    (hF : ∀ a, sumTo K (fun u => indB (cl a u)) ≤ F) (nxt : List Nat → Nat) (hnx : ∀ l, nxt l < K) :
    ∀ k m, (K - k) ^ m * sumTo (K ^ K) (fun H => indB (permB K H) * chs (nearN K cl (runAdp K nxt H k)) m) ≤
      eS F k m * sumTo (K ^ K) (fun H => indB (permB K H))
  | k, 0 => by
    have e : ∀ n, chs n 0 = 1 := fun n => by cases n <;> rfl
    have e2 : ∀ k, eS F k 0 = 1 := fun k => by cases k <;> rfl
    rw [Nat.pow_zero, Nat.one_mul, e2, Nat.one_mul, sumTo_congr _ (fun H _ => by rw [e, Nat.mul_one])]
    exact Nat.le_refl _
  | 0, m + 1 => by
    have e : ∀ H, indB (permB K H) * chs (nearN K cl (runAdp K nxt H 0)) (m + 1) = 0 := fun H => by
      show indB (permB K H) * chs 0 (m + 1) = 0
      rw [show chs 0 (m + 1) = 0 from rfl, Nat.mul_zero]
    rw [sumTo_congr _ (fun H _ => e H), sumTo_const, Nat.mul_zero, Nat.mul_zero]; exact Nat.zero_le _
  | k + 1, m + 1 => by
    have ih1 := nearN_moment hK cl hsym hF nxt hnx k (m + 1)
    have ih0 := nearN_moment hK cl hsym hF nxt hnx k m
    let p := fun H => nxt ((runAdp K nxt H k).map Prod.snd)
    let g := fun H => !decide (p H ∈ (runAdp K nxt H k).map Prod.fst)
    let A := fun H => (runAdp K nxt H k).map Prod.snd
    let S := fun H => nearR K cl ((runAdp K nxt H k).map Prod.snd)
    let w := fun H => chs (nearN K cl (runAdp K nxt H k)) m
    have hnot : ∀ H, g H = true → p H ∉ (runAdp K nxt H k).map Prod.fst := fun H hg h => by
      simp only [g, h, decide_true, Bool.not_true] at hg; exact Bool.false_ne_true hg
    have hw : ∀ H, w H ≤ 2 ^ k := fun H =>
      Nat.le_trans (chs_le_pow _ m) (Nat.pow_le_pow_right (by decide) (by
        have := nearN_le K cl (runAdp K nxt H k); rw [runAdp_length] at this; exact this))
    -- the fresh near answer, weighted by the history's binomial
    have fcw : (K - k) * sumTo (K ^ K) (fun H => indB (permB K H && g H && decide (rget K (p H) H ∈ S H)) * w H) ≤
        k * F * sumTo (K ^ K) (fun H => indB (permB K H) * w H) := by
      have each : ∀ u, (K - k) * sumTo (K ^ K) (fun H => indB (permB K H && (g H && decide (u < w H)) &&
          decide (rget K (p H) H ∈ S H))) ≤ k * F * sumTo (K ^ K) (fun H => indB (permB K H && (g H && decide (u < w H)))) := by
        intro u
        refine fresh_countPG (j := k) (k := k * F) hK p (fun H => hnx _) (fun H => g H && decide (u < w H)) A S
          (fun H => by simp only [A, List.length_map, runAdp_length]; exact Nat.le_refl _)
          (fun H => by
            refine Nat.le_trans (nearR_length cl hF _) ?_
            rw [List.length_map, runAdp_length]; exact Nat.le_refl _) ?_ ?_
        · intro H _ hP hgu h
          have hg : g H = true := (Bool.and_eq_true_iff.1 hgu).1
          obtain ⟨z, hz, hza⟩ := List.mem_map.1 h
          have e : rget K (p H) H = rget K z.1 H := by rw [← hza, runAdp_ans K nxt H k z hz]
          have := permB_inj hP (hnx _) (runAdp_pos nxt hnx H k z hz) e
          exact hnot H hg (List.mem_map.2 ⟨z, hz, this.symm⟩)
        · intro H a b _ ha hb haA hbA _ hgu
          have e := runAdp_vswap hK ha hb nxt hnx k H haA hbA
          refine ⟨by simp only [p, e], by simp only [A, e], by simp only [S, e], ?_⟩
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
    have pt : ∀ H, indB (permB K H) * chs (nearN K cl (runAdp K nxt H (k + 1))) (m + 1) =
        indB (permB K H) * chs (nearN K cl (runAdp K nxt H k)) (m + 1) +
          indB (permB K H && g H && decide (rget K (p H) H ∈ S H)) * w H := by
      intro H
      show indB (permB K H) * chs (nearN K cl (runAdp K nxt H k) +
        indB (!decide (p H ∈ (runAdp K nxt H k).map Prod.fst) &&
          decide (rget K (p H) H ∈ nearR K cl ((runAdp K nxt H k).map Prod.snd)))) (m + 1) = _
      rw [chs_step, Nat.mul_add]
      congr 1
      show indB (permB K H) * (indB (g H && decide (rget K (p H) H ∈ S H)) * w H) = _
      rw [← Nat.mul_assoc, indB_and', Bool.and_assoc]
    have hkk : K - (k + 1) ≤ K - k := Nat.sub_le_sub_left (Nat.le_succ k) K
    rw [sumTo_congr _ (fun H _ => pt H), sumTo_add, Nat.mul_add]
    show _ ≤ (eS F k (m + 1) + k * F * eS F k m) * _
    rw [Nat.add_mul]
    refine Nat.add_le_add (Nat.le_trans (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hkk _)) ih1) ?_
    rw [Nat.pow_succ, Nat.mul_assoc]
    calc (K - (k + 1)) ^ m * ((K - (k + 1)) * sumTo (K ^ K) (fun H =>
          indB (permB K H && g H && decide (rget K (p H) H ∈ S H)) * w H))
        ≤ (K - k) ^ m * ((K - k) * sumTo (K ^ K) (fun H =>
          indB (permB K H && g H && decide (rget K (p H) H ∈ S H)) * w H)) :=
          Nat.mul_le_mul (Nat.pow_le_pow_left hkk _) (Nat.mul_le_mul_right _ hkk)
      _ ≤ (K - k) ^ m * (k * F * sumTo (K ^ K) (fun H => indB (permB K H) * w H)) := Nat.mul_le_mul_left _ fcw
      _ = k * F * ((K - k) ^ m * sumTo (K ^ K) (fun H => indB (permB K H) * w H)) := Nat.mul_left_comm _ _ _
      _ ≤ k * F * (eS F k m * sumTo (K ^ K) (fun H => indB (permB K H))) := Nat.mul_le_mul_left _ ih0
      _ = k * F * eS F k m * sumTo (K ^ K) (fun H => indB (permB K H)) := (Nat.mul_assoc _ _ _).symm

def fact : Nat → Nat
  | 0 => 1
  | m + 1 => (m + 1) * fact m

theorem chs_pos : ∀ n m, m ≤ n → 1 ≤ chs n m
  | n, 0, _ => by cases n <;> exact Nat.le_refl _
  | 0, _ + 1, h => absurd h (Nat.not_succ_le_zero _)
  | n + 1, m + 1, h => by
    show 1 ≤ chs n m + chs n (m + 1)
    exact Nat.le_trans (chs_pos n m (Nat.le_of_succ_le_succ h)) (Nat.le_add_right _ _)

/-- `(S + x)^(m+1) ≥ S^(m+1) + (m+1) x S^m`. -/
theorem pow_succ_ge (S x : Nat) : ∀ m, S ^ (m + 1) + (m + 1) * x * S ^ m ≤ (S + x) ^ (m + 1)
  | 0 => by simp
  | m + 1 => by
    have ih := pow_succ_ge S x m
    have hP : S ^ (m + 1) ≤ (S + x) ^ (m + 1) := Nat.le_trans (Nat.le_add_right _ _) ih
    rw [Nat.pow_succ S (m + 1), Nat.pow_succ (S + x) (m + 1)]
    calc S ^ (m + 1) * S + (m + 1 + 1) * x * S ^ (m + 1)
        = (S ^ (m + 1) + (m + 1) * x * S ^ m) * S + S ^ (m + 1) * x := by
          rw [Nat.pow_succ S m]
          generalize S ^ m = T
          simp only [Nat.add_mul, Nat.one_mul]
          ac_rfl
      _ ≤ (S + x) ^ (m + 1) * S + (S + x) ^ (m + 1) * x :=
          Nat.add_le_add (Nat.mul_le_mul_right S ih) (Nat.mul_le_mul_right x hP)
      _ = (S + x) ^ (m + 1) * (S + x) := (Nat.mul_add _ _ _).symm

/-- **The elementary symmetric sums are at most the power sum's powers over
    `m!`**: `m! eS k m ≤ ((0 + ⋯ + (k-1)) F)^m`. -/
theorem eS_le (F : Nat) : ∀ k m, fact m * eS F k m ≤ (sumTo k (fun j => j) * F) ^ m
  | k, 0 => by cases k <;> exact Nat.le_refl _
  | 0, m + 1 => by show fact (m + 1) * 0 ≤ _; rw [Nat.mul_zero]; exact Nat.zero_le _
  | k + 1, m + 1 => by
    have ih1 := eS_le F k (m + 1)
    have ih0 := eS_le F k m
    show fact (m + 1) * (eS F k (m + 1) + k * F * eS F k m) ≤ ((sumTo k (fun j => j) + k) * F) ^ (m + 1)
    rw [Nat.mul_add, Nat.add_mul]
    refine Nat.le_trans (Nat.add_le_add ih1 ?_) (pow_succ_ge _ _ m)
    show (m + 1) * fact m * (k * F * eS F k m) ≤ (m + 1) * (k * F) * (sumTo k (fun j => j) * F) ^ m
    calc (m + 1) * fact m * (k * F * eS F k m) = (m + 1) * (k * F) * (fact m * eS F k m) := by ac_rfl
      _ ≤ (m + 1) * (k * F) * (sumTo k (fun j => j) * F) ^ m := Nat.mul_le_mul_left _ ih0

/-- **At least `m` near-collisions are rare**: over the permutation tables,
    `k` adaptive forward queries make at least `m` fresh answers near an
    earlier one on at most `((0 + ⋯ + (k-1)) F)^m / (m! (K - k)^m)` of
    them. -/
theorem nearN_tail {K F : Nat} (hK : 0 < K) (cl : Nat → Nat → Bool) (hsym : ∀ a b, cl a b = cl b a)
    (hF : ∀ a, sumTo K (fun u => indB (cl a u)) ≤ F) (nxt : List Nat → Nat) (hnx : ∀ l, nxt l < K) (k m : Nat) :
    fact m * ((K - k) ^ m * sumTo (K ^ K) (fun H => indB (permB K H && decide (m ≤ nearN K cl (runAdp K nxt H k))))) ≤
      (sumTo k (fun j => j) * F) ^ m * sumTo (K ^ K) (fun H => indB (permB K H)) := by
  have pt : ∀ H, indB (permB K H && decide (m ≤ nearN K cl (runAdp K nxt H k))) ≤
      indB (permB K H) * chs (nearN K cl (runAdp K nxt H k)) m := fun H => by
    cases hP : permB K H
    · simp [indB]
    · by_cases h : m ≤ nearN K cl (runAdp K nxt H k)
      · rw [decide_eq_true h, show indB (true && true) = 1 from rfl, show indB true = 1 from rfl, Nat.one_mul]
        exact chs_pos _ _ h
      · rw [decide_eq_false h]; simp [indB]
  calc fact m * ((K - k) ^ m * sumTo (K ^ K) (fun H => indB (permB K H && decide (m ≤ nearN K cl (runAdp K nxt H k)))))
      ≤ fact m * ((K - k) ^ m * sumTo (K ^ K) (fun H => indB (permB K H) * chs (nearN K cl (runAdp K nxt H k)) m)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (sumTo_mono _ (fun H _ => pt H)))
    _ ≤ fact m * (eS F k m * sumTo (K ^ K) (fun H => indB (permB K H))) :=
        Nat.mul_le_mul_left _ (nearN_moment hK cl hsym hF nxt hnx k m)
    _ = fact m * eS F k m * sumTo (K ^ K) (fun H => indB (permB K H)) := (Nat.mul_assoc _ _ _).symm
    _ ≤ _ := Nat.mul_le_mul_right _ (eS_le F k m)

end Circuit
