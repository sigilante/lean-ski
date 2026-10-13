import Ski.ZK.SpongeRandom

/-!
# Sponge chains under one permutation: the birthday bound

`SpongeRandom` gave each absorption its own round-function table; Plonky3
calls one permutation at every step.  Here both chains read one uniform
table, a step's query possibly repeating an earlier one.

- **Lazy sampling.** A position chosen from the table's other entries
  reads a value in a set of at most `k` it does not fix on at most `k/K`
  of the tables (`fresh_count`).
- **Birthday bound.** `k` adaptive queries (`runAdp`, each position chosen
  from the answers so far) see two distinct positions answer alike on at
  most `(0 + 1 + ⋯ + (k-1)) / K` of the tables (`colP_count`): a new
  collision is an old one, or a fresh answer among the old.
- **Partial-rate absorptions.** A block filling only part of the rate
  leaves old rate entries in the next call, so the position is injective
  only in a projection `κ` of the state, at least the capacity.  Two
  distinct positions answering alike under `κ`, its fibres at most `F`,
  occur on at most `(0 + ⋯ + (k-1)) F / K` of the tables (`colK_count`),
  and chains apart under `κ` that meet saw one (`two_meet_colK`): they meet
  after `L` absorptions on at most `(0 + ⋯ + (2L-1)) / |capacity|` of the
  tables (`two_meet_countK`, `two_meet_satK`).
- **Two chains.** Two sponge chains, their queries alternating as one run
  (`nxt2`, each chain over its own blocks), that query distinct positions
  at the first step and wherever their states differ, and meet, saw such
  a collision (`two_meet_col`).  So chains from distinct states below `K`
  over shared blocks meet after `L ≥ 1` absorptions on at most
  `(0 + ⋯ + (2L-1)) / K`, order `(2L)²/(2K)`, of the tables
  (`two_meet_count`), and so do two digits absorbed from one state at
  distinct positions, then shared blocks (`two_meet_digit`);
  `two_meet_sat` meets the hypotheses.

In the full-overwrite results the state is the capacity, its next value
the table's answer at the block and the capacity (as in `SpongeRandom`),
`1/K` per capacity value; in the partial-rate results the state is the
whole state, the table's answers its next values, and `κ` its capacity,
`F / K = 1 / |capacity|`.  The table stands for the permutation as a
random function.  Not shown: the permutation as a permutation (its PRP/PRF
switching term, over the full width), a squeezed index, and any step to
`SudChallenger`'s `hφsp`, which bounds at every table how many salts reach
one index.
-/

set_option autoImplicit false

namespace Circuit
open ZKF

theorem sumTo_split_pos {n : Nat} (p : Nat → Nat) (hp : ∀ H, p H < n) (T : Nat) (f : Nat → Nat) :
    sumTo T f = sumTo n (fun p0 => sumTo T (fun H => indB (decide (p H = p0)) * f H)) := by
  rw [sumTo_exch (fun p0 H => indB (decide (p H = p0)) * f H) T n]
  refine sumTo_congr _ (fun H _ => ?_)
  have key : ∀ m, sumTo m (fun p0 => indB (decide (p H = p0)) * f H) = if p H < m then f H else 0 := by
    intro m
    induction m with
    | zero => simp [sumTo]
    | succ m ih =>
      show sumTo m _ + indB (decide (p H = m)) * f H = _
      rw [ih]
      by_cases e : p H = m
      · subst e; simp [indB]
      · by_cases hl : p H < m
        · rw [if_pos hl, if_pos (Nat.lt_succ_of_lt hl), decide_eq_false e]; simp [indB]
        · have hl' : ¬ p H < m + 1 := fun h => hl (Nat.lt_of_le_of_ne (Nat.le_of_lt_succ h) e)
          rw [if_neg hl, if_neg hl', decide_eq_false e]; simp [indB]
  rw [key, if_pos (hp H)]

theorem count_mem (K : Nat) : ∀ (S : List Nat), sumTo K (fun c => indB (decide (c ∈ S))) ≤ S.length
  | [] => by simp [indB, sumTo_const]
  | a :: S => by
    have ih := count_mem K S
    have pt : ∀ c, indB (decide (c ∈ a :: S)) ≤ indB (decide (c = a)) + indB (decide (c ∈ S)) := fun c => by
      by_cases h1 : c = a
      · subst h1; simp [indB]
      · by_cases h2 : c ∈ S
        · simp [indB, h1, h2]
        · simp [indB, h1, h2]
    refine Nat.le_trans (sumTo_mono _ (fun c _ => pt c)) ?_
    rw [sumTo_add, List.length_cons, Nat.add_comm S.length]
    exact Nat.add_le_add (sumTo_indEq a K).1 ih

/-- **A fresh position's answer lies in a small invariant set rarely**:
    `K` times the tables where the guard holds and the answer at `p H` lies
    in `S H` is at most `k K^n`, the guard, the position and the set
    unchanged by resetting the table at `p H`. -/
theorem fresh_count {K n k : Nat} (hK : 0 < K) (p : Nat → Nat) (hp : ∀ H, p H < n) (g : Nat → Bool)
    (S : Nat → List Nat) (hS : ∀ H, (S H).length ≤ k)
    (hinv : ∀ H u, u < K → g H = true →
      p (rset K (p H) H u) = p H ∧ S (rset K (p H) H u) = S H ∧ g (rset K (p H) H u) = true) :
    K * sumTo (K ^ n) (fun H => indB (g H && decide (rget K (p H) H ∈ S H))) ≤ k * K ^ n := by
  rw [sumTo_split_pos p hp, sumTo_mul]
  have each : ∀ p0, p0 < n → K * sumTo (K ^ n) (fun H => indB (decide (p H = p0)) * indB (g H && decide (rget K (p H) H ∈ S H))) ≤
      k * sumTo (K ^ n) (fun H => indB (decide (p H = p0))) := by
    intro p0 hp0
    let f := fun (c H : Nat) => indB (decide (p H = p0) && g H && decide (c ∈ S H))
    have e := reprog_swap (n := n) hK hp0 f
    have lhs : K * sumTo (K ^ n) (fun H => indB (decide (p H = p0)) * indB (g H && decide (rget K (p H) H ∈ S H))) ≤
        sumTo (K ^ n) (fun H => sumTo K (fun u => f (rget K p0 H) (rset K p0 H u))) := by
      rw [sumTo_mul]
      refine sumTo_mono _ (fun H _ => ?_)
      rw [← sumTo_const _ K]
      refine sumTo_mono _ (fun u hu => ?_)
      by_cases hpH : p H = p0
      · cases hg : g H
        · simp [indB]
        · obtain ⟨h1, h2, h3⟩ := hinv H u hu hg
          rw [hpH] at h1 h2 h3
          simp only [f, decide_eq_true hpH, h1, h2, h3, Bool.true_and]
          rw [hpH]; simp [indB]
      · simp [indB, hpH]
    refine Nat.le_trans lhs ?_
    rw [e]
    have rhs : ∀ H, sumTo K (fun c => f c H) ≤ k * indB (decide (p H = p0)) := fun H => by
      by_cases hpH : p H = p0
      · cases hg : g H
        · simp only [f, hg, Bool.and_false, Bool.false_and]
          exact Nat.le_trans (Nat.le_of_eq (by rw [show (fun _ : Nat => indB false) = fun _ => 0 from rfl, sumTo_const, Nat.mul_zero])) (Nat.zero_le _)
        · simp only [f, decide_eq_true hpH, hg, Bool.true_and]
          rw [show indB true = 1 from rfl, Nat.mul_one]
          exact Nat.le_trans (count_mem K (S H)) (hS H)
      · simp only [f, decide_eq_false hpH, Bool.false_and]
        rw [show (fun _ : Nat => indB false) = fun _ => 0 from rfl, sumTo_const, Nat.mul_zero]
        exact Nat.zero_le _
    refine Nat.le_trans (sumTo_mono _ (fun H _ => rhs H)) (Nat.le_of_eq ?_)
    rw [sumTo_mul]
  refine Nat.le_trans (sumTo_mono _ each) ?_
  have e := sumTo_split_pos p hp (K ^ n) (fun _ => 1)
  simp only [Nat.mul_one] at e
  rw [← sumTo_mul, ← e, sumTo_const, Nat.mul_one]
  exact Nat.le_refl _

/-- An adaptive run's queries, newest first: each position chosen from the
    answers so far, answered by the table. -/
def runAdp (K : Nat) (nxt : List Nat → Nat) (H : Nat) : Nat → List (Nat × Nat)
  | 0 => []
  | k + 1 =>
    let a := (runAdp K nxt H k).map Prod.snd
    (nxt a, rget K (nxt a) H) :: runAdp K nxt H k

theorem runAdp_length (K : Nat) (nxt : List Nat → Nat) (H : Nat) : ∀ k, (runAdp K nxt H k).length = k
  | 0 => rfl
  | k + 1 => by show (runAdp K nxt H k).length + 1 = k + 1; rw [runAdp_length K nxt H k]

/-- Every answer is the table's at its position. -/
theorem runAdp_ans (K : Nat) (nxt : List Nat → Nat) (H : Nat) : ∀ k, ∀ y ∈ runAdp K nxt H k, y.2 = rget K y.1 H
  | 0, _, h => absurd h List.not_mem_nil
  | k + 1, y, h => by
    rcases List.mem_cons.1 h with e | e
    · rw [e]
    · exact runAdp_ans K nxt H k y e

/-- **Resetting an unqueried position leaves the run as it was.** -/
theorem runAdp_rset {K : Nat} (hK : 0 < K) (nxt : List Nat → Nat) {q u : Nat} (hu : u < K) :
    ∀ k H, q ∉ (runAdp K nxt H k).map Prod.fst → runAdp K nxt (rset K q H u) k = runAdp K nxt H k
  | 0, _, _ => rfl
  | k + 1, H, hq => by
    have hq' : q ∉ (runAdp K nxt H k).map Prod.fst := fun h => hq (List.mem_cons_of_mem _ h)
    have ih := runAdp_rset hK nxt hu k H hq'
    have hne : nxt ((runAdp K nxt H k).map Prod.snd) ≠ q := fun e => hq (by
      show q ∈ (nxt ((runAdp K nxt H k).map Prod.snd) :: (runAdp K nxt H k).map Prod.fst)
      rw [e]; exact List.mem_cons_self)
    show (nxt ((runAdp K nxt (rset K q H u) k).map Prod.snd),
        rget K (nxt ((runAdp K nxt (rset K q H u) k).map Prod.snd)) (rset K q H u)) :: runAdp K nxt (rset K q H u) k =
      (nxt ((runAdp K nxt H k).map Prod.snd), rget K (nxt ((runAdp K nxt H k).map Prod.snd)) H) :: runAdp K nxt H k
    rw [ih, rget_rset_ne hK hne hu]

/-- Two queries at distinct positions with equal answers. -/
def colP : List (Nat × Nat) → Bool
  | [] => false
  | x :: rest => colP rest || rest.any (fun y => y.1 != x.1 && y.2 == x.2)

theorem colP_of_mem : ∀ (l : List (Nat × Nat)) (y z : Nat × Nat), y ∈ l → z ∈ l → y.1 ≠ z.1 → y.2 = z.2 → colP l = true
  | [], _, _, h, _, _, _ => absurd h List.not_mem_nil
  | x :: rest, y, z, hy, hz, hne, heq => by
    show (colP rest || rest.any (fun w => w.1 != x.1 && w.2 == x.2)) = true
    rcases List.mem_cons.1 hy with ey | ey <;> rcases List.mem_cons.1 hz with ez | ez
    · subst ey; subst ez; exact absurd rfl hne
    · subst ey
      have : rest.any (fun w => w.1 != y.1 && w.2 == y.2) = true :=
        List.any_eq_true.2 ⟨z, ez, by
          rw [Bool.and_eq_true]; exact ⟨bne_iff_ne.2 (Ne.symm hne), beq_iff_eq.2 heq.symm⟩⟩
      rw [this, Bool.or_true]
    · subst ez
      have : rest.any (fun w => w.1 != z.1 && w.2 == z.2) = true :=
        List.any_eq_true.2 ⟨y, ey, by
          rw [Bool.and_eq_true]; exact ⟨bne_iff_ne.2 hne, beq_iff_eq.2 heq⟩⟩
      rw [this, Bool.or_true]
    · rw [colP_of_mem rest y z ey ez hne heq, Bool.true_or]

/-- **The birthday bound for an adaptive run**: `k` queries, each position
    chosen from the answers so far, see two distinct positions answer
    alike on at most `(0 + 1 + ⋯ + (k-1)) / K` of the tables. -/
theorem colP_count {K n : Nat} (hK : 0 < K) (nxt : List Nat → Nat) (hnx : ∀ l, nxt l < n) :
    ∀ k, K * sumTo (K ^ n) (fun H => indB (colP (runAdp K nxt H k))) ≤ sumTo k (fun j => j) * K ^ n
  | 0 => by simp [colP, runAdp, indB, sumTo_const]
  | k + 1 => by
    have ih := colP_count hK nxt hnx k
    let p := fun H => nxt ((runAdp K nxt H k).map Prod.snd)
    let g := fun H => !decide (p H ∈ (runAdp K nxt H k).map Prod.fst)
    let S := fun H => (runAdp K nxt H k).map Prod.snd
    have hinv : ∀ H u, u < K → g H = true →
        p (rset K (p H) H u) = p H ∧ S (rset K (p H) H u) = S H ∧ g (rset K (p H) H u) = true := by
      intro H u hu hg
      have hnot : p H ∉ (runAdp K nxt H k).map Prod.fst := by
        intro h; simp only [g, h, decide_true, Bool.not_true] at hg; exact Bool.false_ne_true hg
      have e := runAdp_rset hK nxt hu k H hnot
      refine ⟨by simp only [p, e], by simp only [S, e], ?_⟩
      simp only [g, p, e]; exact hg
    have fc := fresh_count (n := n) (k := k) hK p (fun H => hnx _) g S
      (fun H => by simp only [S, List.length_map, runAdp_length]; exact Nat.le_refl _) hinv
    -- a new collision is an old one or a fresh answer among the old
    have pt : ∀ H, indB (colP (runAdp K nxt H (k + 1))) ≤ indB (colP (runAdp K nxt H k)) +
        indB (g H && decide (rget K (p H) H ∈ S H)) := by
      intro H
      show indB (colP (runAdp K nxt H k) || (runAdp K nxt H k).any (fun y => y.1 != p H && y.2 == rget K (p H) H)) ≤ _
      cases hc : colP (runAdp K nxt H k)
      · simp only [Bool.false_or]
        cases hn : (runAdp K nxt H k).any (fun y => y.1 != p H && y.2 == rget K (p H) H)
        · exact Nat.zero_le _
        · obtain ⟨y, hy, hyc⟩ := List.any_eq_true.1 hn
          simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at hyc
          have hS' : rget K (p H) H ∈ S H := List.mem_map.2 ⟨y, hy, hyc.2⟩
          cases hg : g H
          · -- the position was queried before: its earlier answer collides with `y`
            exfalso
            have hm : p H ∈ (runAdp K nxt H k).map Prod.fst := by
              simp only [g, Bool.not_eq_false', decide_eq_true_eq] at hg; exact hg
            obtain ⟨z, hz, hzp⟩ := List.mem_map.1 hm
            have hza : z.2 = rget K (p H) H := by rw [runAdp_ans K nxt H k z hz, hzp]
            have : colP (runAdp K nxt H k) = true :=
              colP_of_mem _ y z hy hz (by rw [hzp]; exact hyc.1) (by rw [hza]; exact hyc.2)
            rw [hc] at this; exact Bool.false_ne_true this
          · simp [indB, hS']
      · simp only [Bool.true_or]; simp [indB]
    refine Nat.le_trans (Nat.mul_le_mul_left _ (sumTo_mono _ (fun H _ => pt H))) ?_
    rw [sumTo_add, Nat.mul_add]
    refine Nat.le_trans (Nat.add_le_add ih fc) (Nat.le_of_eq ?_)
    show sumTo k (fun j => j) * K ^ n + k * K ^ n = (sumTo k (fun j => j) + k) * K ^ n
    rw [Nat.add_mul]

/-- Two sponge chains under one table, as one adaptive run: queries alternate,
    chain `a` from `sa` over blocks `xa`, then chain `b` from `sb` over `xb`,
    each at its last answer (newest first: the other chain's answer sits
    between). -/
def nxt2 (inner : Nat → Nat → Nat) (sa sb : Nat) (xa xb : List Nat) (l : List Nat) : Nat :=
  if l.length % 2 = 0 then inner (if l.length = 0 then sa else l.getD 1 0) (xa.getD (l.length / 2) 0)
  else inner (if l.length = 1 then sb else l.getD 1 0) (xb.getD (l.length / 2) 0)

theorem nxt2_def (inner : Nat → Nat → Nat) (sa sb : Nat) (xa xb l : List Nat) : nxt2 inner sa sb xa xb l =
    if l.length % 2 = 0 then inner (if l.length = 0 then sa else l.getD 1 0) (xa.getD (l.length / 2) 0)
    else inner (if l.length = 1 then sb else l.getD 1 0) (xb.getD (l.length / 2) 0) := rfl

/-- Chain `a`'s and `b`'s states after `i` steps. -/
def stA (K : Nat) (inner : Nat → Nat → Nat) (sa sb : Nat) (xa xb : List Nat) (H i : Nat) : Nat :=
  if i = 0 then sa else ((runAdp K (nxt2 inner sa sb xa xb) H (2 * i)).map Prod.snd).getD 1 0
def stB (K : Nat) (inner : Nat → Nat → Nat) (sa sb : Nat) (xa xb : List Nat) (H i : Nat) : Nat :=
  if i = 0 then sb else ((runAdp K (nxt2 inner sa sb xa xb) H (2 * i)).map Prod.snd).getD 0 0

theorem two_step (K : Nat) (inner : Nat → Nat → Nat) (sa sb : Nat) (xa xb : List Nat) (H i : Nat) :
    runAdp K (nxt2 inner sa sb xa xb) H (2 * (i + 1)) =
      (inner (stB K inner sa sb xa xb H i) (xb.getD i 0), rget K (inner (stB K inner sa sb xa xb H i) (xb.getD i 0)) H) ::
      (inner (stA K inner sa sb xa xb H i) (xa.getD i 0), rget K (inner (stA K inner sa sb xa xb H i) (xa.getD i 0)) H) ::
      runAdp K (nxt2 inner sa sb xa xb) H (2 * i) := by
  have hl := runAdp_length K (nxt2 inner sa sb xa xb) H (2 * i)
  have h2 : 2 * (i + 1) = (2 * i + 1) + 1 := by omega
  rw [h2]
  show (nxt2 inner sa sb xa xb ((runAdp K (nxt2 inner sa sb xa xb) H (2 * i + 1)).map Prod.snd), _) ::
    (nxt2 inner sa sb xa xb ((runAdp K (nxt2 inner sa sb xa xb) H (2 * i)).map Prod.snd), _) :: _ = _
  have ea : nxt2 inner sa sb xa xb ((runAdp K (nxt2 inner sa sb xa xb) H (2 * i)).map Prod.snd) =
      inner (stA K inner sa sb xa xb H i) (xa.getD i 0) := by
    rw [nxt2_def, List.length_map, hl, if_pos (by omega), show 2 * i / 2 = i by omega]
    unfold stA
    by_cases hi : i = 0
    · rw [if_pos (by omega), if_pos hi]
    · rw [if_neg (by omega), if_neg hi]
  have eb : nxt2 inner sa sb xa xb ((runAdp K (nxt2 inner sa sb xa xb) H (2 * i + 1)).map Prod.snd) =
      inner (stB K inner sa sb xa xb H i) (xb.getD i 0) := by
    rw [nxt2_def, List.length_map, runAdp_length, if_neg (by omega), show (2 * i + 1) / 2 = i by omega]
    unfold stB
    by_cases hi : i = 0
    · rw [if_pos (by omega), if_pos hi]
    · rw [if_neg (by omega), if_neg hi]
      rfl
  rw [eb, ea]

theorem colP_cons (x : Nat × Nat) (l : List (Nat × Nat)) (h : colP l = true) : colP (x :: l) = true := by
  show (colP l || _) = true; rw [h, Bool.true_or]

/-- **Two chains that meet saw a collision**: if at the first step, and at
    every step where their states differ, the two chains query distinct
    positions (`hpos`), chains equal after `i ≥ 1` steps put two distinct
    positions with equal answers in the run. -/
theorem two_meet_col {K : Nat} (inner : Nat → Nat → Nat) {sa sb : Nat} (xa xb : List Nat) (H : Nat)
    (hpos : ∀ i, (i = 0 ∨ stA K inner sa sb xa xb H i ≠ stB K inner sa sb xa xb H i) →
      inner (stB K inner sa sb xa xb H i) (xb.getD i 0) ≠ inner (stA K inner sa sb xa xb H i) (xa.getD i 0)) :
    ∀ i, stA K inner sa sb xa xb H (i + 1) = stB K inner sa sb xa xb H (i + 1) →
      colP (runAdp K (nxt2 inner sa sb xa xb) H (2 * (i + 1))) = true
  | i, h => by
    have eA : stA K inner sa sb xa xb H (i + 1) = rget K (inner (stA K inner sa sb xa xb H i) (xa.getD i 0)) H := by
      unfold stA; rw [if_neg (by omega), two_step]; rfl
    have eB : stB K inner sa sb xa xb H (i + 1) = rget K (inner (stB K inner sa sb xa xb H i) (xb.getD i 0)) H := by
      unfold stB; rw [if_neg (by omega), two_step]; rfl
    rw [two_step]
    by_cases hi : i = 0 ∨ stA K inner sa sb xa xb H i ≠ stB K inner sa sb xa xb H i
    · exact colP_of_mem _ _ _ List.mem_cons_self (List.mem_cons_of_mem _ List.mem_cons_self) (hpos i hi)
        (by rw [← eA, ← eB]; exact h.symm)
    · have hi0 : i ≠ 0 := fun e => hi (Or.inl e)
      have heq : stA K inner sa sb xa xb H i = stB K inner sa sb xa xb H i := Decidable.byContradiction (fun e => hi (Or.inr e))
      obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
      exact colP_cons _ _ (colP_cons _ _ (two_meet_col inner xa xb H hpos j heq))

theorem stA_lt {K : Nat} (hK : 0 < K) (inner : Nat → Nat → Nat) {sa sb : Nat} (hsa : sa < K) (xa xb : List Nat) (H : Nat) :
    ∀ j, stA K inner sa sb xa xb H j < K
  | 0 => hsa
  | j + 1 => by unfold stA; rw [if_neg (by omega), two_step]; exact rget_lt hK _ _
theorem stB_lt {K : Nat} (hK : 0 < K) (inner : Nat → Nat → Nat) {sa sb : Nat} (hsb : sb < K) (xa xb : List Nat) (H : Nat) :
    ∀ j, stB K inner sa sb xa xb H j < K
  | 0 => hsb
  | j + 1 => by unfold stB; rw [if_neg (by omega), two_step]; exact rget_lt hK _ _

/-- **Two sponge chains under one table meet rarely**: from distinct states
    below `K` over shared blocks, after `L + 1` absorptions, they meet on at
    most `(0 + 1 + ⋯ + (2L+1)) / K` of the tables, Plonky3's one
    permutation's birthday term. -/
theorem two_meet_count {K n : Nat} (hK : 0 < K) (inner : Nat → Nat → Nat) (hin : ∀ s x, inner s x < n)
    (hinj : ∀ x s s', s < K → s' < K → inner s x = inner s' x → s = s') {sa sb : Nat} (hsa : sa < K) (hsb : sb < K)
    (hne : sa ≠ sb) (xs : List Nat) (L : Nat) :
    K * sumTo (K ^ n) (fun H => indB (decide (stA K inner sa sb xs xs H (L + 1) = stB K inner sa sb xs xs H (L + 1)))) ≤
      sumTo (2 * (L + 1)) (fun j => j) * K ^ n := by
  refine Nat.le_trans (Nat.mul_le_mul_left _ (sumTo_mono _ (fun H _ => ?_)))
    (colP_count (n := n) hK (nxt2 inner sa sb xs xs) (fun l => by rw [nxt2_def]; split <;> exact hin _ _) (2 * (L + 1)))
  cases e : decide (stA K inner sa sb xs xs H (L + 1) = stB K inner sa sb xs xs H (L + 1))
  · exact Nat.zero_le _
  · have hpos : ∀ i, (i = 0 ∨ stA K inner sa sb xs xs H i ≠ stB K inner sa sb xs xs H i) →
        inner (stB K inner sa sb xs xs H i) (xs.getD i 0) ≠ inner (stA K inner sa sb xs xs H i) (xs.getD i 0) := by
      intro i hi he
      have hst := hinj _ _ _ (stB_lt hK inner hsb xs xs H i) (stA_lt hK inner hsa xs xs H i) he
      rcases hi with hi | hi
      · subst hi; exact hne (by simpa [stA, stB] using hst.symm)
      · exact hi hst.symm
    rw [two_meet_col inner xs xs H hpos L (of_decide_eq_true e)]
    exact Nat.le_refl _

/-- **Two digits absorbed from one state under one table meet rarely**: from
    `iv`, the digits `a`, `b` at distinct positions, then shared blocks,
    the chains meet after `L + 1` absorptions on at most
    `(0 + ⋯ + (2L+1)) / K` of the tables. -/
theorem two_meet_digit {K n : Nat} (hK : 0 < K) (inner : Nat → Nat → Nat) (hin : ∀ s x, inner s x < n)
    (hinj : ∀ x s s', s < K → s' < K → inner s x = inner s' x → s = s') {iv a b : Nat} (hiv : iv < K)
    (hd : inner iv a ≠ inner iv b) (xs : List Nat) (L : Nat) :
    K * sumTo (K ^ n) (fun H =>
        indB (decide (stA K inner iv iv (a :: xs) (b :: xs) H (L + 1) = stB K inner iv iv (a :: xs) (b :: xs) H (L + 1)))) ≤
      sumTo (2 * (L + 1)) (fun j => j) * K ^ n := by
  refine Nat.le_trans (Nat.mul_le_mul_left _ (sumTo_mono _ (fun H _ => ?_)))
    (colP_count (n := n) hK (nxt2 inner iv iv (a :: xs) (b :: xs)) (fun l => by rw [nxt2_def]; split <;> exact hin _ _)
      (2 * (L + 1)))
  cases e : decide (stA K inner iv iv (a :: xs) (b :: xs) H (L + 1) = stB K inner iv iv (a :: xs) (b :: xs) H (L + 1))
  · exact Nat.zero_le _
  · have hpos : ∀ i, (i = 0 ∨ stA K inner iv iv (a :: xs) (b :: xs) H i ≠ stB K inner iv iv (a :: xs) (b :: xs) H i) →
        inner (stB K inner iv iv (a :: xs) (b :: xs) H i) ((b :: xs).getD i 0) ≠
          inner (stA K inner iv iv (a :: xs) (b :: xs) H i) ((a :: xs).getD i 0) := by
      intro i hi he
      rcases hi with hi | hi
      · subst hi; exact hd (by simpa [stA, stB] using he.symm)
      · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := by
          rcases i with _ | j
          · exact absurd (by simp [stA, stB]) hi
          · exact ⟨j, rfl⟩
        have hst := hinj _ _ _ (stB_lt hK inner hiv (a :: xs) (b :: xs) H (j + 1))
          (stA_lt hK inner hiv (a :: xs) (b :: xs) H (j + 1)) (by simpa using he)
        exact hi hst.symm
    rw [two_meet_col inner (a :: xs) (b :: xs) H hpos L (of_decide_eq_true e)]
    exact Nat.le_refl _

/-- **`two_meet_count`'s and `two_meet_digit`'s hypotheses are met** by
    `inner s x = (x % X) K + s % K`: positions below `X K` at every state,
    injective in the state below `K`, distinct digits below `X` at
    distinct positions. -/
theorem two_meet_sat {K X : Nat} (hK : 0 < K) (hX : 0 < X) :
    (∀ s x, (x % X) * K + s % K < X * K) ∧
      (∀ x s s', s < K → s' < K → (x % X) * K + s % K = (x % X) * K + s' % K → s = s') ∧
      (∀ iv a b, a < X → b < X → a ≠ b → (a % X) * K + iv % K ≠ (b % X) * K + iv % K) := by
  refine ⟨fun s x => ?_, fun x s s' hs hs' h => ?_, fun iv a b ha hb hab h => hab ?_⟩
  · calc (x % X) * K + s % K < (x % X) * K + K := Nat.add_lt_add_left (Nat.mod_lt _ hK) _
      _ = (x % X + 1) * K := by rw [Nat.succ_mul]
      _ ≤ X * K := Nat.mul_le_mul_right _ (Nat.mod_lt _ hX)
  · rw [Nat.mod_eq_of_lt hs, Nat.mod_eq_of_lt hs'] at h; omega
  · rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h
    exact Nat.eq_of_mul_eq_mul_right hK (by omega)

/-! ### Collisions under a projection: partial-rate absorptions -/

/-- Two queries at distinct positions whose answers agree under `κ`. -/
def colK (κ : Nat → Nat) : List (Nat × Nat) → Bool
  | [] => false
  | x :: rest => colK κ rest || rest.any (fun y => y.1 != x.1 && κ y.2 == κ x.2)

theorem colK_of_mem (κ : Nat → Nat) : ∀ (l : List (Nat × Nat)) (y z : Nat × Nat), y ∈ l → z ∈ l → y.1 ≠ z.1 →
    κ y.2 = κ z.2 → colK κ l = true
  | [], _, _, h, _, _, _ => absurd h List.not_mem_nil
  | x :: rest, y, z, hy, hz, hne, heq => by
    show (colK κ rest || rest.any (fun w => w.1 != x.1 && κ w.2 == κ x.2)) = true
    rcases List.mem_cons.1 hy with ey | ey <;> rcases List.mem_cons.1 hz with ez | ez
    · subst ey; subst ez; exact absurd rfl hne
    · subst ey
      have : rest.any (fun w => w.1 != y.1 && κ w.2 == κ y.2) = true :=
        List.any_eq_true.2 ⟨z, ez, by rw [Bool.and_eq_true]; exact ⟨bne_iff_ne.2 (Ne.symm hne), beq_iff_eq.2 heq.symm⟩⟩
      rw [this, Bool.or_true]
    · subst ez
      have : rest.any (fun w => w.1 != z.1 && κ w.2 == κ z.2) = true :=
        List.any_eq_true.2 ⟨y, ey, by rw [Bool.and_eq_true]; exact ⟨bne_iff_ne.2 hne, beq_iff_eq.2 heq⟩⟩
      rw [this, Bool.or_true]
    · rw [colK_of_mem κ rest y z ey ez hne heq, Bool.true_or]

theorem colK_cons (κ : Nat → Nat) (x : Nat × Nat) (l : List (Nat × Nat)) (h : colK κ l = true) : colK κ (x :: l) = true := by
  show (colK κ l || _) = true; rw [h, Bool.true_or]

theorem range_map_sum (f : Nat → Bool) : ∀ K, ((List.range K).map (fun u => indB (f u))).sum = sumTo K (fun u => indB (f u))
  | 0 => rfl
  | K + 1 => by rw [List.range_succ, List.map_append, List.sum_append, range_map_sum f K]; simp [sumTo]

/-- The answers below `K` whose projection meets the earlier answers'. -/
def nearK (K : Nat) (κ : Nat → Nat) (as : List Nat) : List Nat :=
  (List.range K).filter (fun u => as.any (fun a => κ u == κ a))

theorem nearK_length {K F : Nat} (κ : Nat → Nat) (hF : ∀ v, sumTo K (fun u => indB (decide (κ u = v))) ≤ F) :
    ∀ as : List Nat, (nearK K κ as).length ≤ as.length * F := by
  intro as
  have hlen : ∀ (l : List Nat) (f : Nat → Bool), (l.filter f).length = (l.map (fun u => indB (f u))).sum := by
    intro l f
    induction l with
    | nil => rfl
    | cons u l ih => cases hf : f u <;> simp [hf, ih, indB] <;> omega
  have hsum := fun f => range_map_sum f K
  unfold nearK
  rw [hlen, hsum]
  induction as with
  | nil => simp [indB, sumTo_const]
  | cons a as ih =>
    have pt : ∀ u, indB ((a :: as).any (fun a' => κ u == κ a')) ≤
        indB (decide (κ u = κ a)) + indB (as.any (fun a' => κ u == κ a')) := fun u => by
      rw [List.any_cons]
      cases h1 : (κ u == κ a) <;> cases h2 : as.any (fun a' => κ u == κ a') <;>
        simp_all [indB]
    refine Nat.le_trans (sumTo_mono _ (fun u _ => pt u)) ?_
    rw [sumTo_add, List.length_cons, Nat.succ_mul, Nat.add_comm (as.length * F)]
    exact Nat.add_le_add (hF _) ih

/-- **The birthday bound under a projection**: `k` adaptive queries see
    two distinct positions whose answers agree under `κ`, its fibres below
    `K` at most `F`, on at most `(0 + ⋯ + (k-1)) F / K` of the tables. -/
theorem colK_count {K n F : Nat} (hK : 0 < K) (κ : Nat → Nat) (hF : ∀ v, sumTo K (fun u => indB (decide (κ u = v))) ≤ F)
    (nxt : List Nat → Nat) (hnx : ∀ l, nxt l < n) :
    ∀ k, K * sumTo (K ^ n) (fun H => indB (colK κ (runAdp K nxt H k))) ≤ sumTo k (fun j => j) * F * K ^ n
  | 0 => by simp [colK, runAdp, indB, sumTo_const]
  | k + 1 => by
    have ih := colK_count hK κ hF nxt hnx k
    let p := fun H => nxt ((runAdp K nxt H k).map Prod.snd)
    let g := fun H => !decide (p H ∈ (runAdp K nxt H k).map Prod.fst)
    let S := fun H => nearK K κ ((runAdp K nxt H k).map Prod.snd)
    have hinv : ∀ H u, u < K → g H = true →
        p (rset K (p H) H u) = p H ∧ S (rset K (p H) H u) = S H ∧ g (rset K (p H) H u) = true := by
      intro H u hu hg
      have hnot : p H ∉ (runAdp K nxt H k).map Prod.fst := by
        intro h; simp only [g, h, decide_true, Bool.not_true] at hg; exact Bool.false_ne_true hg
      have e := runAdp_rset hK nxt hu k H hnot
      refine ⟨by simp only [p, e], by simp only [S, e], ?_⟩
      simp only [g, p, e]; exact hg
    have fc := fresh_count (n := n) (k := k * F) hK p (fun H => hnx _) g S
      (fun H => by
        refine Nat.le_trans (nearK_length κ hF _) ?_
        rw [List.length_map, runAdp_length]; exact Nat.le_refl _) hinv
    have pt : ∀ H, indB (colK κ (runAdp K nxt H (k + 1))) ≤ indB (colK κ (runAdp K nxt H k)) +
        indB (g H && decide (rget K (p H) H ∈ S H)) := by
      intro H
      show indB (colK κ (runAdp K nxt H k) ||
        (runAdp K nxt H k).any (fun y => y.1 != p H && κ y.2 == κ (rget K (p H) H))) ≤ _
      cases hc : colK κ (runAdp K nxt H k)
      · simp only [Bool.false_or]
        cases hn : (runAdp K nxt H k).any (fun y => y.1 != p H && κ y.2 == κ (rget K (p H) H))
        · exact Nat.zero_le _
        · obtain ⟨y, hy, hyc⟩ := List.any_eq_true.1 hn
          simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at hyc
          have hS' : rget K (p H) H ∈ S H := by
            show rget K (p H) H ∈ nearK K κ ((runAdp K nxt H k).map Prod.snd)
            unfold nearK
            rw [List.mem_filter]
            refine ⟨List.mem_range.2 (rget_lt hK _ _), List.any_eq_true.2 ⟨y.2, List.mem_map.2 ⟨y, hy, rfl⟩, ?_⟩⟩
            exact beq_iff_eq.2 hyc.2.symm
          cases hg : g H
          · exfalso
            have hm : p H ∈ (runAdp K nxt H k).map Prod.fst := by
              simp only [g, Bool.not_eq_false', decide_eq_true_eq] at hg; exact hg
            obtain ⟨z, hz, hzp⟩ := List.mem_map.1 hm
            have hza : z.2 = rget K (p H) H := by rw [runAdp_ans K nxt H k z hz, hzp]
            have : colK κ (runAdp K nxt H k) = true :=
              colK_of_mem κ _ y z hy hz (by rw [hzp]; exact hyc.1) (by rw [hza]; exact hyc.2)
            rw [hc] at this; exact Bool.false_ne_true this
          · simp [indB, hS']
      · simp only [Bool.true_or]; simp [indB]
    refine Nat.le_trans (Nat.mul_le_mul_left _ (sumTo_mono _ (fun H _ => pt H))) ?_
    rw [sumTo_add, Nat.mul_add]
    refine Nat.le_trans (Nat.add_le_add ih fc) (Nat.le_of_eq ?_)
    show sumTo k (fun j => j) * F * K ^ n + k * F * K ^ n = (sumTo k (fun j => j) + k) * F * K ^ n
    rw [Nat.add_mul, Nat.add_mul]

/-- **Chains that meet saw a collision under the projection**: positions
    equal only where the states agree under `κ` (`hpk`, a partial-rate
    absorption keeping at least `κ` of the state), the starting states apart
    under `κ`. -/
theorem two_meet_colK {K : Nat} (inner : Nat → Nat → Nat) (κ : Nat → Nat) {sa sb : Nat} (xs : List Nat) (H : Nat)
    (hpk : ∀ x s s', inner s x = inner s' x → κ s = κ s') (hk0 : κ sa ≠ κ sb) :
    ∀ i, stA K inner sa sb xs xs H (i + 1) = stB K inner sa sb xs xs H (i + 1) →
      colK κ (runAdp K (nxt2 inner sa sb xs xs) H (2 * (i + 1))) = true := by
  have eA : ∀ j, stA K inner sa sb xs xs H (j + 1) = rget K (inner (stA K inner sa sb xs xs H j) (xs.getD j 0)) H :=
    fun j => by unfold stA; rw [if_neg (by omega), two_step]; rfl
  have eB : ∀ j, stB K inner sa sb xs xs H (j + 1) = rget K (inner (stB K inner sa sb xs xs H j) (xs.getD j 0)) H :=
    fun j => by unfold stB; rw [if_neg (by omega), two_step]; rfl
  -- a meeting where the positions differ is a collision at this step
  have here : ∀ i, inner (stB K inner sa sb xs xs H i) (xs.getD i 0) ≠ inner (stA K inner sa sb xs xs H i) (xs.getD i 0) →
      stA K inner sa sb xs xs H (i + 1) = stB K inner sa sb xs xs H (i + 1) →
      colK κ (runAdp K (nxt2 inner sa sb xs xs) H (2 * (i + 1))) = true := fun i hp h => by
    rw [two_step]
    exact colK_of_mem κ _ _ _ List.mem_cons_self (List.mem_cons_of_mem _ List.mem_cons_self) hp
      (by rw [← eA, ← eB, h])
  intro i
  induction i with
  | zero =>
    intro h
    refine here 0 (fun hp => hk0 ?_) h
    have := (hpk _ _ _ hp).symm
    simpa [stA, stB] using this
  | succ j ih =>
    intro h
    by_cases hs : stA K inner sa sb xs xs H (j + 1) = stB K inner sa sb xs xs H (j + 1)
    · rw [two_step]; exact colK_cons κ _ _ (colK_cons κ _ _ (ih hs))
    · by_cases hp : inner (stB K inner sa sb xs xs H (j + 1)) (xs.getD (j + 1) 0) =
          inner (stA K inner sa sb xs xs H (j + 1)) (xs.getD (j + 1) 0)
      · have hκ := hpk _ _ _ hp
        have hpj : inner (stB K inner sa sb xs xs H j) (xs.getD j 0) ≠ inner (stA K inner sa sb xs xs H j) (xs.getD j 0) :=
          fun e => hs (by rw [eA, eB, e])
        rw [two_step, two_step]
        refine colK_cons κ _ _ (colK_cons κ _ _ (colK_of_mem κ _ _ _ List.mem_cons_self
          (List.mem_cons_of_mem _ List.mem_cons_self) hpj ?_))
        rw [← eA, ← eB]; exact hκ
      · exact here (j + 1) hp h

/-- **Partial-rate sponge chains under one table meet rarely**: positions
    injective in the projection `κ` only (old rate entries left in), `κ`'s
    fibres below `K` at most `F`, from states apart under `κ`, after `L + 1`
    absorptions the chains meet on at most `(0 + ⋯ + (2L+1)) F / K` of the
    tables: `κ` the capacity, `F / K = 1 / |capacity|`. -/
theorem two_meet_countK {K n F : Nat} (hK : 0 < K) (inner : Nat → Nat → Nat) (hin : ∀ s x, inner s x < n)
    (κ : Nat → Nat) (hF : ∀ v, sumTo K (fun u => indB (decide (κ u = v))) ≤ F)
    (hpk : ∀ x s s', inner s x = inner s' x → κ s = κ s') {sa sb : Nat} (hk0 : κ sa ≠ κ sb) (xs : List Nat) (L : Nat) :
    K * sumTo (K ^ n) (fun H => indB (decide (stA K inner sa sb xs xs H (L + 1) = stB K inner sa sb xs xs H (L + 1)))) ≤
      sumTo (2 * (L + 1)) (fun j => j) * F * K ^ n := by
  refine Nat.le_trans (Nat.mul_le_mul_left _ (sumTo_mono _ (fun H _ => ?_)))
    (colK_count (n := n) hK κ hF (nxt2 inner sa sb xs xs) (fun l => by rw [nxt2_def]; split <;> exact hin _ _) (2 * (L + 1)))
  cases e : decide (stA K inner sa sb xs xs H (L + 1) = stB K inner sa sb xs xs H (L + 1))
  · exact Nat.zero_le _
  · rw [two_meet_colK inner κ xs H hpk hk0 L (of_decide_eq_true e)]
    exact Nat.le_refl _

/-- **The partial-rate hypotheses are met** at every state by a state
    `r + R c`, the capacity `κ s = (s / R) % C` with fibres `R` below `R C`, a
    full overwrite keeping only the capacity:
    `inner s x = (x % X) C + (s / R) % C`. -/
theorem two_meet_satK {R C X : Nat} (hR : 0 < R) (hC : 0 < C) (hX : 0 < X) :
    (∀ s x, (x % X) * C + (s / R) % C < X * C) ∧
      (∀ x s s', (x % X) * C + (s / R) % C = (x % X) * C + (s' / R) % C → (s / R) % C = (s' / R) % C) ∧
      (∀ v, sumTo (R * C) (fun u => indB (decide ((u / R) % C = v))) ≤ R) := by
  refine ⟨fun s x => ?_, fun x s s' h => by omega, fun v => ?_⟩
  · calc (x % X) * C + (s / R) % C < (x % X) * C + C := Nat.add_lt_add_left (Nat.mod_lt _ hC) _
      _ = (x % X + 1) * C := by rw [Nat.succ_mul]
      _ ≤ X * C := Nat.mul_le_mul_right _ (Nat.mod_lt _ hX)
  · rw [sumTo_split R _ C]
    have each : ∀ c, c < C → sumTo R (fun r => indB (decide (((r + R * c) / R) % C = v))) = R * indB (decide (c = v)) :=
      fun c hc => by
      refine Eq.trans (sumTo_congr _ (fun r hr => ?_)) (sumTo_const (indB (decide (c = v))) R)
      show indB (decide (((r + R * c) / R) % C = v)) = indB (decide (c = v))
      rw [Nat.add_mul_div_left _ _ hR, Nat.div_eq_of_lt hr, Nat.zero_add, Nat.mod_eq_of_lt hc]
    rw [sumTo_congr _ (fun c hc => each c hc), ← sumTo_mul]
    calc R * sumTo C (fun c => indB (decide (c = v))) ≤ R * 1 := Nat.mul_le_mul_left _ (sumTo_indEq v C).1
      _ = R := Nat.mul_one R

end Circuit
