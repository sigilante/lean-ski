import Ski.ZK.SpongePerm
import Ski.ZK.Count

/-!
# Sponge chains under a uniform permutation

`SpongePerm` reads one uniform table, the permutation modelled as a random
function.  Here the tables are the permutations themselves: the tables
below `K^K` whose answers at the `K` positions below `K` are distinct
(`permB`), each permutation of `[0, K)` once, averaged uniformly.  The
width `K` is the whole state, so no PRP/PRF switching term enters.

- **Lazy sampling.** Exchanging two values the run has not seen
  (`vswap`, an involution on permutation tables) leaves an adaptive run
  as it was (`runAdp_vswap`) and moves a fresh answer from one unseen value
  to the other.  So after `j` answers a fresh position's answer lies in a
  set of `k` values on at most `k / (K - j)` of the permutation tables
  (`fresh_countP`).
- **Birthday bound.** `k` adaptive forward queries see two distinct
  positions whose answers are related, each answer related to at most `F`,
  on at most `(0 + ⋯ + (k-1)) F / (K - k)` of the permutation tables
  (`colR_countP`).
- **Sponge chains.** With the state the permutation's output, the next
  input the state with a block overwriting part of the rate, and `κ` the capacity (`F / K` one over its
  size): chains from distinct capacities over shared blocks meet after
  `L + 1` absorptions on at most `(0 + ⋯ + (2L+1)) F / (K - 2(L+1))` of the
  permutation tables (`two_meet_countKP`); so do two digits absorbed at
  distinct positions (`two_meet_digitKP`); squeezed outputs `σ` agree on at
  most `(0 + ⋯ + (2L+1)) (Fκ + Fσ) / (K - 2(L+1))` (`two_squeeze_countP`).
  `two_meet_satPT` meets the hypotheses with a genuine partial-rate
  absorption at full width, and shows permutation tables exist;
  `two_meet_satPT_k0` gives two states apart under `κ` once the capacity
  has two values.

Not shown: inverse queries to the permutation (an honest sponge makes
none).  `SpongeIndex` takes these bounds toward `SudChallenger`'s `hφsp`.
-/

set_option autoImplicit false

namespace Circuit
open ZKF

/-! ### Tables from digits, and permutation tables -/

/-- The table whose answer at `m < n` is `f m`. -/
def tab (K : Nat) : (Nat → Nat) → Nat → Nat
  | _, 0 => 0
  | f, n + 1 => f 0 + K * tab K (fun m => f (m + 1)) n

theorem rget_zero' (K X : Nat) : rget K 0 X = X % K := by
  unfold rget; rw [Nat.pow_zero, Nat.div_one]

theorem rget_succ' (K m X : Nat) : rget K (m + 1) X = rget K m (X / K) := by
  unfold rget; rw [Nat.pow_succ', Nat.div_div_eq_div_mul]

theorem tab_lt {K : Nat} : ∀ (n : Nat) (f : Nat → Nat), (∀ m, m < n → f m < K) → tab K f n < K ^ n
  | 0, _, _ => by show 0 < K ^ 0; rw [Nat.pow_zero]; exact Nat.one_pos
  | n + 1, f, h => by
    have ih := tab_lt n (fun m => f (m + 1)) (fun m hm => h (m + 1) (Nat.succ_lt_succ hm))
    show f 0 + K * tab K (fun m => f (m + 1)) n < K ^ (n + 1)
    calc f 0 + K * tab K (fun m => f (m + 1)) n < K + K * tab K (fun m => f (m + 1)) n :=
          Nat.add_lt_add_right (h 0 (Nat.succ_pos _)) _
      _ = K * (tab K (fun m => f (m + 1)) n + 1) := by rw [Nat.mul_succ, Nat.add_comm]
      _ ≤ K * K ^ n := Nat.mul_le_mul_left _ ih
      _ = K ^ (n + 1) := (Nat.pow_succ' ..).symm

theorem rget_tab {K : Nat} (hK : 0 < K) : ∀ (n : Nat) (f : Nat → Nat), (∀ m, m < n → f m < K) →
    ∀ m, m < n → rget K m (tab K f n) = f m
  | 0, _, _, _, hm => absurd hm (Nat.not_lt_zero _)
  | n + 1, f, h, 0, _ => by
    show rget K 0 (f 0 + K * tab K (fun m => f (m + 1)) n) = f 0
    rw [rget_zero', Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (h 0 (Nat.succ_pos _))]
  | n + 1, f, h, m + 1, hm => by
    show rget K (m + 1) (f 0 + K * tab K (fun m => f (m + 1)) n) = f (m + 1)
    rw [rget_succ', Nat.add_mul_div_left _ _ hK, Nat.div_eq_of_lt (h 0 (Nat.succ_pos _)), Nat.zero_add]
    exact rget_tab hK n (fun m => f (m + 1)) (fun m hm => h (m + 1) (Nat.succ_lt_succ hm)) m (Nat.lt_of_succ_lt_succ hm)

/-- Tables below `K^n` with equal answers at every `m < n` are equal. -/
theorem digit_ext {K : Nat} (hK : 0 < K) : ∀ (n X Y : Nat), X < K ^ n → Y < K ^ n →
    (∀ m, m < n → rget K m X = rget K m Y) → X = Y
  | 0, X, Y, hX, hY, _ => by
    rw [Nat.pow_zero] at hX hY; omega
  | n + 1, X, Y, hX, hY, h => by
    have hX' : X / K < K ^ n := (Nat.div_lt_iff_lt_mul hK).2 (by rw [← Nat.pow_succ]; exact hX)
    have hY' : Y / K < K ^ n := (Nat.div_lt_iff_lt_mul hK).2 (by rw [← Nat.pow_succ]; exact hY)
    have e0 : X % K = Y % K := by rw [← rget_zero', ← rget_zero']; exact h 0 (Nat.succ_pos _)
    have e1 : X / K = Y / K := digit_ext hK n _ _ hX' hY' (fun m hm => by
      rw [← rget_succ', ← rget_succ']; exact h (m + 1) (Nat.succ_lt_succ hm))
    rw [← Nat.mod_add_div X K, ← Nat.mod_add_div Y K, e0, e1]

/-- The values `a` and `b` exchanged. -/
def swapV (a b v : Nat) : Nat := if v = a then b else if v = b then a else v

theorem swapV_swapV (a b v : Nat) : swapV a b (swapV a b v) = v := by
  unfold swapV
  by_cases h1 : v = a
  · subst h1; by_cases h2 : b = v
    · subst h2; simp
    · simp [h2]
  · by_cases h2 : v = b
    · subst h2; simp [h1]
    · simp [h1, h2]

theorem swapV_lt {K a b v : Nat} (ha : a < K) (hb : b < K) (hv : v < K) : swapV a b v < K := by
  unfold swapV; split
  · exact hb
  · split
    · exact ha
    · exact hv

theorem swapV_ne {a b v : Nat} (ha : v ≠ a) (hb : v ≠ b) : swapV a b v = v := by
  unfold swapV; rw [if_neg ha, if_neg hb]

theorem swapV_inj {a b v w : Nat} (h : swapV a b v = swapV a b w) : v = w := by
  rw [← swapV_swapV a b v, h, swapV_swapV]

/-- The table with every answer `a` made `b` and every `b` made `a`. -/
def vswap (K a b H : Nat) : Nat := tab K (fun m => swapV a b (rget K m H)) K

theorem rget_vswap {K a b m : Nat} (hK : 0 < K) (ha : a < K) (hb : b < K) (hm : m < K) (H : Nat) :
    rget K m (vswap K a b H) = swapV a b (rget K m H) :=
  rget_tab hK K _ (fun _ _ => swapV_lt ha hb (rget_lt hK _ _)) m hm

theorem vswap_lt {K a b : Nat} (hK : 0 < K) (ha : a < K) (hb : b < K) (H : Nat) : vswap K a b H < K ^ K :=
  tab_lt K _ (fun _ _ => swapV_lt ha hb (rget_lt hK _ _))

theorem vswap_vswap {K a b H : Nat} (hK : 0 < K) (ha : a < K) (hb : b < K) (hH : H < K ^ K) :
    vswap K a b (vswap K a b H) = H :=
  digit_ext hK K _ _ (vswap_lt hK ha hb _) hH (fun m hm => by
    rw [rget_vswap hK ha hb hm, rget_vswap hK ha hb hm, swapV_swapV])

/-- The table answers distinct positions below `K` distinctly: below `K^K`,
    a permutation of `[0, K)`. -/
def permB (K H : Nat) : Bool :=
  (List.range K).all (fun i => (List.range K).all (fun j => i == j || rget K i H != rget K j H))

theorem permB_inj {K H : Nat} (h : permB K H = true) {i j : Nat} (hi : i < K) (hj : j < K)
    (e : rget K i H = rget K j H) : i = j := by
  have h1 := List.all_eq_true.1 h i (List.mem_range.2 hi)
  have h2 := List.all_eq_true.1 h1 j (List.mem_range.2 hj)
  rw [Bool.or_eq_true, beq_iff_eq, bne_iff_ne] at h2
  rcases h2 with h2 | h2
  · exact h2
  · exact absurd e h2

theorem permB_of_inj {K H : Nat} (h : ∀ i j, i < K → j < K → rget K i H = rget K j H → i = j) : permB K H = true := by
  refine List.all_eq_true.2 (fun i hi => List.all_eq_true.2 (fun j hj => ?_))
  rw [Bool.or_eq_true, beq_iff_eq, bne_iff_ne]
  by_cases e : rget K i H = rget K j H
  · exact Or.inl (h i j (List.mem_range.1 hi) (List.mem_range.1 hj) e)
  · exact Or.inr e

theorem permB_vswap {K a b H : Nat} (hK : 0 < K) (ha : a < K) (hb : b < K) (h : permB K H = true) :
    permB K (vswap K a b H) = true :=
  permB_of_inj (fun i j hi hj e => by
    rw [rget_vswap hK ha hb hi, rget_vswap hK ha hb hj] at e
    exact permB_inj h hi hj (swapV_inj e))

theorem le_sumTo (f : Nat → Nat) {x : Nat} : ∀ n, x < n → f x ≤ sumTo n f
  | 0, h => absurd h (Nat.not_lt_zero _)
  | n + 1, h => by
    show f x ≤ sumTo n f + f n
    rcases Nat.lt_or_ge x n with hx | hx
    · exact Nat.le_trans (le_sumTo f n hx) (Nat.le_add_right _ _)
    · have e : x = n := by omega
      rw [e]; exact Nat.le_add_left _ _

/-- At least `K - |S|` values below `K` lie outside `S`. -/
theorem count_notmem (K : Nat) (S : List Nat) : K - S.length ≤ sumTo K (fun b => indB (!decide (b ∈ S))) := by
  have e : sumTo K (fun b => indB (decide (b ∈ S))) + sumTo K (fun b => indB (!decide (b ∈ S))) = K := by
    rw [← sumTo_add]
    refine Eq.trans (sumTo_congr _ (fun b _ => ?_)) (Eq.trans (sumTo_const 1 K) (Nat.mul_one K))
    cases decide (b ∈ S) <;> rfl
  have := count_mem K S
  omega

/-- **A fresh position's answer under a uniform permutation lies in a small
    set rarely**: over the permutation tables, `K - j` times those where the
    guard holds and the answer at `p H` lies in `S H` is at most `k` times
    all of them.  The guard means `p H`'s answer avoids the `j` answers
    `A H` already seen, and exchanging two unseen values leaves the position,
    the seen answers, the set and the guard unchanged. -/
theorem fresh_countP {K j k : Nat} (hK : 0 < K) (p : Nat → Nat) (hp : ∀ H, p H < K) (g : Nat → Bool) (A S : Nat → List Nat)
    (hA : ∀ H, (A H).length ≤ j) (hS : ∀ H, (S H).length ≤ k)
    (hfr : ∀ H, H < K ^ K → permB K H = true → g H = true → rget K (p H) H ∉ A H)
    (hinv : ∀ H a b, H < K ^ K → a < K → b < K → a ∉ A H → b ∉ A H → permB K H = true → g H = true →
      p (vswap K a b H) = p H ∧ A (vswap K a b H) = A H ∧ S (vswap K a b H) = S H ∧ g (vswap K a b H) = true) :
    (K - j) * sumTo (K ^ K) (fun H => indB (permB K H && g H && decide (rget K (p H) H ∈ S H))) ≤
      k * sumTo (K ^ K) (fun H => indB (permB K H)) := by
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
  have step3 : ∀ H, sumTo K (fun c => sumTo K (fun b => tgt c b H)) ≤ k * indB (permB K H) := fun H => by
    cases hP : permB K H
    · refine Nat.le_of_eq (Eq.trans (sumTo_congr _ (fun c _ => Eq.trans (sumTo_congr _ (fun b _ => ?_))
        (Eq.trans (sumTo_const 0 K) (Nat.mul_zero K)))) (Eq.trans (sumTo_const 0 K) ?_))
      · show indB (permB K H && _ && _ && _ && _) = 0; rw [hP]; rfl
      · rw [Nat.mul_zero, show indB false = 0 from rfl, Nat.mul_zero]
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
      rw [show indB true = 1 from rfl, Nat.mul_one]
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

/-! ### The birthday bound under a uniform permutation -/

theorem runAdp_pos {K : Nat} (nxt : List Nat → Nat) (hnx : ∀ l, nxt l < K) (H : Nat) :
    ∀ k, ∀ y ∈ runAdp K nxt H k, y.1 < K
  | 0, _, h => absurd h List.not_mem_nil
  | k + 1, y, h => by
    rcases List.mem_cons.1 h with e | e
    · rw [e]; exact hnx _
    · exact runAdp_pos nxt hnx H k y e

/-- **Exchanging two unseen values leaves the run as it was.** -/
theorem runAdp_vswap {K a b : Nat} (hK : 0 < K) (ha : a < K) (hb : b < K) (nxt : List Nat → Nat)
    (hnx : ∀ l, nxt l < K) : ∀ k H, a ∉ (runAdp K nxt H k).map Prod.snd → b ∉ (runAdp K nxt H k).map Prod.snd →
      runAdp K nxt (vswap K a b H) k = runAdp K nxt H k
  | 0, _, _, _ => rfl
  | k + 1, H, hA, hB => by
    have sub : ∀ v, v ∉ (runAdp K nxt H (k + 1)).map Prod.snd → v ∉ (runAdp K nxt H k).map Prod.snd :=
      fun v h h' => h (List.mem_cons_of_mem _ h')
    have ih := runAdp_vswap hK ha hb nxt hnx k H (sub a hA) (sub b hB)
    have hne : ∀ v, v ∉ (runAdp K nxt H (k + 1)).map Prod.snd →
        rget K (nxt ((runAdp K nxt H k).map Prod.snd)) H ≠ v := fun v h e => h (by
      show v ∈ (rget K (nxt ((runAdp K nxt H k).map Prod.snd)) H :: (runAdp K nxt H k).map Prod.snd)
      rw [e]; exact List.mem_cons_self)
    show (nxt ((runAdp K nxt (vswap K a b H) k).map Prod.snd),
        rget K (nxt ((runAdp K nxt (vswap K a b H) k).map Prod.snd)) (vswap K a b H)) :: runAdp K nxt (vswap K a b H) k =
      (nxt ((runAdp K nxt H k).map Prod.snd), rget K (nxt ((runAdp K nxt H k).map Prod.snd)) H) :: runAdp K nxt H k
    rw [ih, rget_vswap hK ha hb (hnx _), swapV_ne (hne a hA) (hne b hB)]

/-- **The birthday bound under a uniform permutation**: over the
    permutation tables of `[0, K)`, `k` adaptive forward queries see two
    distinct positions whose answers are related by `cl`, each answer
    related to at most `F` below `K`, on at most
    `(0 + ⋯ + (k-1)) F / (K - k)` of them. -/
theorem colR_countP {K F : Nat} (hK : 0 < K) (cl : Nat → Nat → Bool) (hsym : ∀ a b, cl a b = cl b a)
    (hF : ∀ a, sumTo K (fun u => indB (cl a u)) ≤ F) (nxt : List Nat → Nat) (hnx : ∀ l, nxt l < K) :
    ∀ k, (K - k) * sumTo (K ^ K) (fun H => indB (permB K H && colR cl (runAdp K nxt H k))) ≤
      sumTo k (fun j => j) * F * sumTo (K ^ K) (fun H => indB (permB K H))
  | 0 => by simp [colR, runAdp, indB, sumTo_const]
  | k + 1 => by
    have ih := colR_countP hK cl hsym hF nxt hnx k
    let p := fun H => nxt ((runAdp K nxt H k).map Prod.snd)
    let g := fun H => !decide (p H ∈ (runAdp K nxt H k).map Prod.fst)
    let A := fun H => (runAdp K nxt H k).map Prod.snd
    let S := fun H => nearR K cl ((runAdp K nxt H k).map Prod.snd)
    have hnot : ∀ H, g H = true → p H ∉ (runAdp K nxt H k).map Prod.fst := fun H hg h => by
      simp only [g, h, decide_true, Bool.not_true] at hg; exact Bool.false_ne_true hg
    have hfr : ∀ H, H < K ^ K → permB K H = true → g H = true → rget K (p H) H ∉ A H := fun H _ hP hg h => by
      obtain ⟨z, hz, hza⟩ := List.mem_map.1 h
      have e : rget K (p H) H = rget K z.1 H := by rw [← hza, runAdp_ans K nxt H k z hz]
      have := permB_inj hP (hnx _) (runAdp_pos nxt hnx H k z hz) e
      exact hnot H hg (List.mem_map.2 ⟨z, hz, this.symm⟩)
    have hinv : ∀ H a b, H < K ^ K → a < K → b < K → a ∉ A H → b ∉ A H → permB K H = true → g H = true →
        p (vswap K a b H) = p H ∧ A (vswap K a b H) = A H ∧ S (vswap K a b H) = S H ∧ g (vswap K a b H) = true := by
      intro H a b _ ha hb haA hbA _ hg
      have e := runAdp_vswap hK ha hb nxt hnx k H haA hbA
      refine ⟨by simp only [p, e], by simp only [A, e], by simp only [S, e], ?_⟩
      simp only [g, p, e]; exact hg
    have fc := fresh_countP (j := k) (k := k * F) hK p (fun H => hnx _) g A S
      (fun H => by simp only [A, List.length_map, runAdp_length]; exact Nat.le_refl _)
      (fun H => by
        refine Nat.le_trans (nearR_length cl hF _) ?_
        rw [List.length_map, runAdp_length]; exact Nat.le_refl _) hfr hinv
    -- a new related pair is an old one, or a fresh answer near an old one
    have pt0 : ∀ H, indB (colR cl (runAdp K nxt H (k + 1))) ≤ indB (colR cl (runAdp K nxt H k)) +
        indB (g H && decide (rget K (p H) H ∈ S H)) := by
      intro H
      show indB (colR cl (runAdp K nxt H k) ||
        (runAdp K nxt H k).any (fun y => y.1 != p H && cl y.2 (rget K (p H) H))) ≤ _
      cases hc : colR cl (runAdp K nxt H k)
      · simp only [Bool.false_or]
        cases hn : (runAdp K nxt H k).any (fun y => y.1 != p H && cl y.2 (rget K (p H) H))
        · exact Nat.zero_le _
        · obtain ⟨y, hy, hyc⟩ := List.any_eq_true.1 hn
          rw [Bool.and_eq_true, bne_iff_ne] at hyc
          have hS' : rget K (p H) H ∈ S H := by
            show rget K (p H) H ∈ nearR K cl ((runAdp K nxt H k).map Prod.snd)
            unfold nearR
            rw [List.mem_filter]
            exact ⟨List.mem_range.2 (rget_lt hK _ _), List.any_eq_true.2 ⟨y.2, List.mem_map.2 ⟨y, hy, rfl⟩, hyc.2⟩⟩
          cases hg : g H
          · exfalso
            have hm : p H ∈ (runAdp K nxt H k).map Prod.fst := by
              simp only [g, Bool.not_eq_false', decide_eq_true_eq] at hg; exact hg
            obtain ⟨z, hz, hzp⟩ := List.mem_map.1 hm
            have hza : z.2 = rget K (p H) H := by rw [runAdp_ans K nxt H k z hz, hzp]
            have : colR cl (runAdp K nxt H k) = true :=
              colR_of_mem cl hsym _ y z hy hz (by rw [hzp]; exact hyc.1) (by rw [hza]; exact hyc.2)
            rw [hc] at this; exact Bool.false_ne_true this
          · simp [indB, hS']
      · simp only [Bool.true_or]; simp [indB]
    have pt : ∀ H, indB (permB K H && colR cl (runAdp K nxt H (k + 1))) ≤
        indB (permB K H && colR cl (runAdp K nxt H k)) + indB (permB K H && g H && decide (rget K (p H) H ∈ S H)) := by
      intro H
      cases hP : permB K H
      · simp [indB]
      · simp only [Bool.true_and]; exact pt0 H
    have hkk : K - (k + 1) ≤ K - k := Nat.sub_le_sub_left (Nat.le_succ k) K
    refine Nat.le_trans (Nat.mul_le_mul_left _ (sumTo_mono _ (fun H _ => pt H))) ?_
    rw [sumTo_add, Nat.mul_add]
    refine Nat.le_trans (Nat.add_le_add (Nat.le_trans (Nat.mul_le_mul_right _ hkk) ih)
      (Nat.le_trans (Nat.mul_le_mul_right _ hkk) fc)) (Nat.le_of_eq ?_)
    show sumTo k (fun j => j) * F * _ + k * F * _ = (sumTo k (fun j => j) + k) * F * _
    rw [Nat.add_mul, Nat.add_mul]

/-! ### Sponge chains under a uniform permutation -/

theorem fib_rel {K F : Nat} (κ : Nat → Nat) (hF : ∀ v, sumTo K (fun u => indB (decide (κ u = v))) ≤ F) :
    ∀ a, sumTo K (fun u => indB (decide (κ a = κ u))) ≤ F := fun a =>
  Nat.le_trans (Nat.le_of_eq (sumTo_congr _ (fun u _ => by
    by_cases h : κ a = κ u
    · rw [decide_eq_true h, decide_eq_true h.symm]
    · rw [decide_eq_false h, decide_eq_false (fun e => h e.symm)]))) (hF (κ a))

theorem rel_symm (κ : Nat → Nat) (a b : Nat) : decide (κ a = κ b) = decide (κ b = κ a) := by
  by_cases h : κ a = κ b
  · rw [decide_eq_true h, decide_eq_true h.symm]
  · rw [decide_eq_false h, decide_eq_false (fun e => h e.symm)]

/-- **Partial-rate sponge chains under a uniform permutation meet rarely**:
    the state the permutation's whole output, positions injective in the
    projection `κ` only, `κ`'s fibres below `K` at most `F`, from states
    apart under `κ` over shared blocks; after `L + 1` absorptions the
    chains meet on at most `(0 + ⋯ + (2L+1)) F / (K - 2(L+1))` of the
    permutation tables: `κ` the capacity, `F / K = 1 / |capacity|`. -/
theorem two_meet_countKP {K F : Nat} (hK : 0 < K) (inner : Nat → Nat → Nat) (hin : ∀ s x, inner s x < K)
    (κ : Nat → Nat) (hF : ∀ v, sumTo K (fun u => indB (decide (κ u = v))) ≤ F)
    (hpk : ∀ x s s', inner s x = inner s' x → κ s = κ s') {sa sb : Nat} (hk0 : κ sa ≠ κ sb) (xs : List Nat) (L : Nat) :
    (K - 2 * (L + 1)) * sumTo (K ^ K) (fun H =>
        indB (permB K H && decide (stA K inner sa sb xs xs H (L + 1) = stB K inner sa sb xs xs H (L + 1)))) ≤
      sumTo (2 * (L + 1)) (fun j => j) * F * sumTo (K ^ K) (fun H => indB (permB K H)) := by
  refine Nat.le_trans (Nat.mul_le_mul_left _ (sumTo_mono _ (fun H _ => ?_)))
    (colR_countP hK (fun a b => decide (κ a = κ b)) (rel_symm κ) (fib_rel κ hF) (nxt2 inner sa sb xs xs)
      (fun l => by rw [nxt2_def]; split <;> exact hin _ _) (2 * (L + 1)))
  cases e : decide (stA K inner sa sb xs xs H (L + 1) = stB K inner sa sb xs xs H (L + 1))
  · rw [Bool.and_false]; exact Nat.zero_le _
  · rw [colR_of_colK κ _ (fun a b h => decide_eq_true h) _
      (two_meet_colK inner κ xs xs H hpk (fun _ _ => rfl) (fun hp => hk0 (hpk _ _ _ hp).symm) L (of_decide_eq_true e))]
    exact Nat.le_refl _

/-- **Two digits absorbed from one state, under a uniform permutation**: at
    distinct positions, then shared blocks, the chains meet after `L + 1`
    absorptions on at most `(0 + ⋯ + (2L+1)) F / (K - 2(L+1))` of the
    permutation tables. -/
theorem two_meet_digitKP {K F : Nat} (hK : 0 < K) (inner : Nat → Nat → Nat) (hin : ∀ s x, inner s x < K)
    (κ : Nat → Nat) (hF : ∀ v, sumTo K (fun u => indB (decide (κ u = v))) ≤ F)
    (hpk : ∀ x s s', inner s x = inner s' x → κ s = κ s') {iv a b : Nat} (hd : inner iv a ≠ inner iv b)
    (xs : List Nat) (L : Nat) :
    (K - 2 * (L + 1)) * sumTo (K ^ K) (fun H => indB (permB K H &&
        decide (stA K inner iv iv (a :: xs) (b :: xs) H (L + 1) = stB K inner iv iv (a :: xs) (b :: xs) H (L + 1)))) ≤
      sumTo (2 * (L + 1)) (fun j => j) * F * sumTo (K ^ K) (fun H => indB (permB K H)) := by
  refine Nat.le_trans (Nat.mul_le_mul_left _ (sumTo_mono _ (fun H _ => ?_)))
    (colR_countP hK (fun a b => decide (κ a = κ b)) (rel_symm κ) (fib_rel κ hF) (nxt2 inner iv iv (a :: xs) (b :: xs))
      (fun l => by rw [nxt2_def]; split <;> exact hin _ _) (2 * (L + 1)))
  cases e : decide (stA K inner iv iv (a :: xs) (b :: xs) H (L + 1) = stB K inner iv iv (a :: xs) (b :: xs) H (L + 1))
  · rw [Bool.and_false]; exact Nat.zero_le _
  · have hblk : ∀ i, 0 < i → (a :: xs).getD i 0 = (b :: xs).getD i 0 := fun i hi => by
      obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
      rfl
    rw [colR_of_colK κ _ (fun a b h => decide_eq_true h) _
      (two_meet_colK inner κ (a :: xs) (b :: xs) H hpk hblk (fun e => hd e.symm) L (of_decide_eq_true e))]
    exact Nat.le_refl _

/-- **Squeezed outputs under a uniform permutation agree rarely**: outputs
    `σ` of the final states, chains from distinct capacities over shared
    blocks; after `L + 1` absorptions on at most
    `(0 + ⋯ + (2L+1)) (Fκ + Fσ) / (K - 2(L+1))` of the permutation tables. -/
theorem two_squeeze_countP {K Fk Fs : Nat} (hK : 0 < K) (inner : Nat → Nat → Nat) (hin : ∀ s x, inner s x < K)
    (κ σ : Nat → Nat) (hFk : ∀ v, sumTo K (fun u => indB (decide (κ u = v))) ≤ Fk)
    (hFs : ∀ v, sumTo K (fun u => indB (decide (σ u = v))) ≤ Fs)
    (hpk : ∀ x s s', inner s x = inner s' x → κ s = κ s') {sa sb : Nat} (hk0 : κ sa ≠ κ sb) (xs : List Nat) (L : Nat) :
    (K - 2 * (L + 1)) * sumTo (K ^ K) (fun H => indB (permB K H &&
        decide (σ (stA K inner sa sb xs xs H (L + 1)) = σ (stB K inner sa sb xs xs H (L + 1))))) ≤
      sumTo (2 * (L + 1)) (fun j => j) * (Fk + Fs) * sumTo (K ^ K) (fun H => indB (permB K H)) := by
  let cl := fun a b => decide (κ a = κ b) || decide (σ a = σ b)
  have hsym : ∀ a b, cl a b = cl b a := fun a b => by
    simp only [cl]; rw [rel_symm κ a b, rel_symm σ a b]
  have hF : ∀ a, sumTo K (fun u => indB (cl a u)) ≤ Fk + Fs := fun a => by
    have pt : ∀ u, indB (cl a u) ≤ indB (decide (κ a = κ u)) + indB (decide (σ a = σ u)) := fun u => by
      simp only [cl]
      cases decide (κ a = κ u) <;> cases decide (σ a = σ u) <;> simp [indB]
    refine Nat.le_trans (sumTo_mono _ (fun u _ => pt u)) ?_
    rw [sumTo_add]; exact Nat.add_le_add (fib_rel κ hFk a) (fib_rel σ hFs a)
  refine Nat.le_trans (Nat.mul_le_mul_left _ (sumTo_mono _ (fun H _ => ?_)))
    (colR_countP hK cl hsym hF (nxt2 inner sa sb xs xs) (fun l => by rw [nxt2_def]; split <;> exact hin _ _)
      (2 * (L + 1)))
  cases e : decide (σ (stA K inner sa sb xs xs H (L + 1)) = σ (stB K inner sa sb xs xs H (L + 1)))
  · rw [Bool.and_false]; exact Nat.zero_le _
  · have hσ := of_decide_eq_true e
    by_cases hm : stA K inner sa sb xs xs H (L + 1) = stB K inner sa sb xs xs H (L + 1)
    · have hk := two_meet_colK inner κ xs xs H hpk (fun _ _ => rfl) (fun hp => hk0 (hpk _ _ _ hp).symm) L hm
      rw [colR_of_colK κ cl (fun a b h => by simp [cl, h]) _ hk]
      exact Nat.le_refl _
    · have eA : stA K inner sa sb xs xs H (L + 1) = rget K (inner (stA K inner sa sb xs xs H L) (xs.getD L 0)) H := by
        unfold stA; rw [if_neg (by omega), two_step]; rfl
      have eB : stB K inner sa sb xs xs H (L + 1) = rget K (inner (stB K inner sa sb xs xs H L) (xs.getD L 0)) H := by
        unfold stB; rw [if_neg (by omega), two_step]; rfl
      have hp : inner (stB K inner sa sb xs xs H L) (xs.getD L 0) ≠ inner (stA K inner sa sb xs xs H L) (xs.getD L 0) :=
        fun h => hm (by rw [eA, eB, h])
      rw [two_step]
      rw [colR_of_mem cl hsym _ _ _ List.mem_cons_self (List.mem_cons_of_mem _ List.mem_cons_self) hp
        (by show cl _ _ = true; rw [← eA, ← eB]; simp [cl, hσ])]
      exact Nat.le_refl _

/-- The identity table is a permutation table. -/
theorem permB_id {K : Nat} (hK : 0 < K) : permB K (tab K (fun m => m) K) = true ∧ tab K (fun m => m) K < K ^ K :=
  ⟨permB_of_inj (fun i j hi hj e => by
    rwa [rget_tab hK K _ (fun _ h => h) i hi, rget_tab hK K _ (fun _ h => h) j hj] at e),
   tab_lt K _ (fun _ h => h)⟩

/-- **The hypotheses meet a genuine partial-rate sponge at full width**: the
    state `r1 + R1 (r2 + R2 c)` is the permutation's whole input and output,
    `K = R1 R2 C`; the block overwrites `r1`, so the next input
    `x % R1 + R1 ((s / R1) % (R2 C))` lies below `K`; `κ` reads the capacity
    `c`, its fibres `R1 R2`; and permutation tables exist. -/
theorem two_meet_satPT {R1 R2 C : Nat} (hR1 : 0 < R1) (hR2 : 0 < R2) (hC : 0 < C) :
    (∀ s x, x % R1 + R1 * ((s / R1) % (R2 * C)) < R1 * (R2 * C)) ∧
      (∀ x s s', x % R1 + R1 * ((s / R1) % (R2 * C)) = x % R1 + R1 * ((s' / R1) % (R2 * C)) →
        ((s / R1) % (R2 * C)) / R2 = ((s' / R1) % (R2 * C)) / R2) ∧
      (∀ v, sumTo (R1 * (R2 * C)) (fun u => indB (decide (((u / R1) % (R2 * C)) / R2 = v))) ≤ R1 * R2) ∧
      0 < sumTo ((R1 * (R2 * C)) ^ (R1 * (R2 * C))) (fun H => indB (permB (R1 * (R2 * C)) H)) := by
  have hK : 0 < R1 * (R2 * C) := Nat.mul_pos hR1 (Nat.mul_pos hR2 hC)
  obtain ⟨h1, h2, h3⟩ := two_meet_satKP hR1 hR2 hC hR1
  obtain ⟨hp, hl⟩ := permB_id hK
  refine ⟨h1, h2, h3, Nat.lt_of_lt_of_le ?_ (le_sumTo (fun H => indB (permB (R1 * (R2 * C)) H)) _ hl)⟩
  show 0 < indB (permB (R1 * (R2 * C)) (tab (R1 * (R2 * C)) (fun m => m) (R1 * (R2 * C))))
  rw [hp]; exact Nat.one_pos

/-- **Two states apart under the capacity**: with `C ≥ 2`, the states `0`
    and `R1 R2` have capacities `0` and `1`, so `two_meet_countKP`'s `hk0`
    holds at `two_meet_satPT`'s instance. -/
theorem two_meet_satPT_k0 {R1 R2 C : Nat} (hR1 : 0 < R1) (hR2 : 0 < R2) (hC : 1 < C) :
    ((0 / R1) % (R2 * C)) / R2 ≠ (((R1 * R2) / R1) % (R2 * C)) / R2 := by
  have hlt : R2 < R2 * C := by
    calc R2 = R2 * 1 := (Nat.mul_one R2).symm
      _ < R2 * C := Nat.mul_lt_mul_of_pos_left hC hR2
  rw [Nat.zero_div, Nat.zero_mod, Nat.zero_div, Nat.mul_div_cancel_left _ hR1, Nat.mod_eq_of_lt hlt, Nat.div_self hR2]
  exact Nat.zero_ne_one

end Circuit
