import Ski.ZK.SpongeSqueeze

/-!
# A challenge squeezed from the permutation

Plonky3 squeezes each challenge from the sponge's permutation, where the
composites read the fourth from a table `H4` independent of it.  Here the
answer at the squeeze position of a uniform permutation `P` is traded for
an independent uniform state `w`, with `P`'s answer there and `w`
exchanged so that the permutation still agrees with the challenge.  The
composites' distinguisher reads whole tables, so it sees `P` whole, its
inverse included; no separate inverse queries arise.

- **The exchange.** Over the permutation tables, `K` times those where `f`
  holds at a context `ctx P`, `P` and its squeezed answer is at most the
  pairs `(w, P)` where `f` holds at the context, `P` with the squeezed
  answer and `w` exchanged, and `w`; plus the pairs `(P, u)` where
  exchanging `u` with the squeezed answer changes the context
  (`squeeze_swap`).
- **A run's exchanges.** With the context `k` adaptive forward queries and
  the squeeze position the next one, an exchange that touches no answer of
  the run leaves it as it was, so the exchanges that change it number at
  most `k` per table, plus `K` on the tables whose squeezed answer the run
  has already seen (`squeeze_bad_run`).
- **Revisits.** When each position after the first keeps `κ` of the answer
  before it, a revisit gives two answers at distinct positions with equal
  `κ`, or an answer with the first position's `κ` (`revisit_colRV`), on at
  most `(0 + ⋯ + (k-1) + k) F / (K - k)` of the permutation tables
  (`colRV_countP`, `revisit_countP`).  0.8's absorption and its
  empty-buffer squeeze both keep the capacity's tail (`nxt08_κ`), so this
  bound needs no case for squeezes (`squeeze_run`, `squeeze_run08`).  Per
  table the error is `k / K + (0 + ⋯ + k) / (Q (1 - k/K))`, `Q` the
  capacity's tail.
- **A composite's challenge.** A bound over `P`, `H4` and the other tables,
  for every distinguisher, its real view reading `H4` at the run's squeeze
  position and depending on `P` only through the run, gives the bound with
  no `H4`: the real view reads `P` at the squeeze position and the
  simulator programs `P`, exchanging its answer at the simulated position
  with the challenge (`zk_squeeze`).  The distinguisher must find the
  squeeze position from the view in both worlds.  The real view reads `P`
  through the run and the squeezed state alone, so the squeeze must be the
  transcript's last use of `P`.  `zk_squeeze_sat08` meets every hypothesis
  at 0.8's duplex, `k` calls in any order of absorptions and squeezes.
  For `k ≥ K` both sides vanish and the bound says nothing.

Not shown: `zk_squeeze` applied to a Sudoku composite, which needs the
sponge files' chains written as a run of `runAdp`, the composite's fourth
challenge read at a full state, `H4` kept apart from the other tables, and
`n` programmed points of one shared `H4` where `zk_squeeze` exchanges one;
the first three challenges squeezed from the permutation as well.  The hypothesis `hyp` still carries the
index's spread, which `SpongeRoot` through `SpongeAlign` bound with
absorptions only, so 0.8's empty-buffer squeeze stays open there.
-/

set_option autoImplicit false

namespace Circuit
open ZKF

/-- **A sum of indicators picks out the value `x`.** -/
theorem sumTo_pick (c : Nat → Bool) {x : Nat} : ∀ n, x < n →
    sumTo n (fun u => indB (decide (x = u) && c u)) = indB (c x)
  | 0, h => absurd h (Nat.not_lt_zero _)
  | n + 1, h => by
    show sumTo n (fun u => indB (decide (x = u) && c u)) + indB (decide (x = n) && c n) = indB (c x)
    rcases Nat.lt_or_ge x n with hx | hx
    · rw [sumTo_pick c n hx, decide_eq_false (Nat.ne_of_lt hx)]; rfl
    · have e : x = n := Nat.le_antisymm (Nat.le_of_lt_succ h) hx
      subst e
      rw [sumTo_congr x (g := fun _ => 0) (fun u hu => by rw [decide_eq_false (Nat.ne_of_gt hu)]; rfl),
        sumTo_const, Nat.mul_zero, Nat.zero_add, decide_eq_true rfl, Bool.true_and]

theorem swapV_right (a b : Nat) : swapV a b b = a := by
  unfold swapV
  by_cases h : b = a
  · rw [if_pos h, h]
  · rw [if_neg h, if_pos rfl]

theorem indB_le_one (b : Bool) : indB b ≤ 1 := by cases b <;> decide

theorem indB_split (b f g : Bool) : indB (b && f) ≤ indB (b && f && g) + indB (b && !g) := by
  cases b <;> cases f <;> cases g <;> decide

/-- **A squeezed answer traded for an independent value.**  Over the
    permutation tables, `K` times those where `f` holds at the table, its
    context `ctx H` and its answer at the squeeze position `φ (ctx H)` is
    at most the pairs `(w, H)` where `f` holds at the context, the table
    with that answer and `w` exchanged, and `w`; plus the pairs `(H, u)`
    where exchanging `u` with the squeezed answer changes the context. -/
theorem squeeze_swap {α : Type} [DecidableEq α] {K : Nat} (hK : 0 < K) (ctx : Nat → α) (φ : α → Nat)
    (hφ : ∀ c, φ c < K) (f : α → Nat → Nat → Bool) :
    K * sumTo (K ^ K) (fun H => indB (permB K H && f (ctx H) H (rget K (φ (ctx H)) H))) ≤
      sumTo K (fun w => sumTo (K ^ K) (fun H =>
        indB (permB K H && f (ctx H) (vswap K (rget K (φ (ctx H)) H) w H) w))) +
      sumTo (K ^ K) (fun H => sumTo K (fun u =>
        indB (permB K H && !decide (ctx (vswap K u (rget K (φ (ctx H)) H) H) = ctx H)))) := by
  -- the exchanges that keep the context
  let T := fun (H u a : Nat) => indB (decide (rget K (φ (ctx H)) H = a) &&
    (permB K H && f (ctx H) H a && decide (ctx (vswap K u a H) = ctx H)))
  have step1 : ∀ H, K * indB (permB K H && f (ctx H) H (rget K (φ (ctx H)) H)) ≤
      sumTo K (fun u => sumTo K (fun a => T H u a)) +
        sumTo K (fun u => indB (permB K H && !decide (ctx (vswap K u (rget K (φ (ctx H)) H) H) = ctx H))) := fun H => by
    rw [← sumTo_const, ← sumTo_add]
    refine sumTo_mono _ (fun u _ => ?_)
    rw [sumTo_pick (fun a => permB K H && f (ctx H) H a && decide (ctx (vswap K u a H) = ctx H)) K (rget_lt hK _ _)]
    exact indB_split _ _ _
  -- exchanging `u` with `a` sends a kept table to one whose squeezed answer is `u`
  have step2 : ∀ u a, u < K → a < K → sumTo (K ^ K) (fun H => T H u a) ≤
      sumTo (K ^ K) (fun H => indB (decide (rget K (φ (ctx H)) H = u) &&
        (permB K H && f (ctx H) (vswap K u a H) a))) := by
    intro u a hu ha
    rw [← sumTo_perm (fun H => T H u a) (K ^ K) (vswap K u a) (vswap K u a)
      (fun _ _ => vswap_lt hK hu ha _) (fun _ _ => vswap_lt hK hu ha _)
      (fun H hH => vswap_vswap hK hu ha hH) (fun H hH => vswap_vswap hK hu ha hH)]
    refine sumTo_mono _ (fun H hH => ?_)
    cases hs : (decide (rget K (φ (ctx (vswap K u a H))) (vswap K u a H) = a) &&
        (permB K (vswap K u a H) && f (ctx (vswap K u a H)) (vswap K u a H) a &&
          decide (ctx (vswap K u a (vswap K u a H)) = ctx (vswap K u a H))))
    · show indB _ ≤ _; rw [hs]; exact Nat.zero_le _
    · show indB _ ≤ _; rw [hs]
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hs
      obtain ⟨hans, ⟨hP, hf⟩, hce⟩ := hs
      rw [vswap_vswap hK hu ha hH] at hce
      have hP' : permB K H = true := by
        have := permB_vswap hK hu ha hP; rwa [vswap_vswap hK hu ha hH] at this
      have hans' : rget K (φ (ctx H)) H = u := by
        have e := congrArg (swapV u a) hans
        rw [← rget_vswap hK hu ha (hφ _), vswap_vswap hK hu ha hH, ← hce, swapV_right] at e
        exact e
      rw [← hce] at hf
      rw [hans', hP', hf, decide_eq_true rfl]; exact Nat.le_refl _
  rw [sumTo_mul]
  refine Nat.le_trans (sumTo_mono _ (fun H _ => step1 H)) ?_
  rw [sumTo_add]
  refine Nat.add_le_add_right ?_ _
  rw [sumTo_exch (fun H u => sumTo K (fun a => T H u a)) K (K ^ K)]
  rw [sumTo_congr K (fun u _ => sumTo_exch (fun H a => T H u a) K (K ^ K))]
  refine Nat.le_trans (sumTo_mono _ (fun u hu => sumTo_mono _ (fun a ha => step2 u a hu ha))) ?_
  rw [sumTo_exch (fun u a => sumTo (K ^ K) (fun H =>
    indB (decide (rget K (φ (ctx H)) H = u) && (permB K H && f (ctx H) (vswap K u a H) a)))) K K]
  refine Nat.le_of_eq (sumTo_congr K (fun a _ => ?_))
  rw [sumTo_exch (fun u H => indB (decide (rget K (φ (ctx H)) H = u) &&
    (permB K H && f (ctx H) (vswap K u a H) a))) (K ^ K) K]
  refine sumTo_congr _ (fun H _ => ?_)
  exact sumTo_pick (fun u => permB K H && f (ctx H) (vswap K u a H) a) K (rget_lt hK _ _)

/-- **The exchanges that change a run**: for `k` adaptive forward queries
    and the squeeze position `nxt` of their answers, at most `k` per
    permutation table, plus `K` on the tables whose squeezed answer the
    run has already seen. -/
theorem squeeze_bad_run {K : Nat} (hK : 0 < K) (nxt : List Nat → Nat) (hnx : ∀ l, nxt l < K) (k : Nat) :
    sumTo (K ^ K) (fun H => sumTo K (fun u =>
      indB (permB K H && !decide (runAdp K nxt (vswap K u (rget K (nxt ((runAdp K nxt H k).map Prod.snd)) H) H) k =
        runAdp K nxt H k)))) ≤
      k * sumTo (K ^ K) (fun H => indB (permB K H)) +
      K * sumTo (K ^ K) (fun H => indB (permB K H &&
        decide (rget K (nxt ((runAdp K nxt H k).map Prod.snd)) H ∈ (runAdp K nxt H k).map Prod.snd))) := by
  rw [sumTo_mul, sumTo_mul, ← sumTo_add]
  refine sumTo_mono _ (fun H _ => ?_)
  let A := (runAdp K nxt H k).map Prod.snd
  let a := rget K (nxt A) H
  have ha : a < K := rget_lt hK _ _
  cases hP : permB K H
  · refine Nat.le_trans (Nat.le_of_eq (Eq.trans (sumTo_congr _ (fun u _ => ?_)) (sumTo_const 0 K))) (Nat.zero_le _)
    rfl
  · by_cases hs : a ∈ A
    · refine Nat.le_trans ?_ (Nat.le_add_left _ _)
      show _ ≤ K * indB (true && decide (a ∈ A))
      rw [decide_eq_true hs, show indB (true && true) = 1 from rfl, Nat.mul_one]
      exact Nat.le_trans (sumTo_mono _ (fun u _ => indB_le_one _)) (Nat.le_of_eq (Eq.trans (sumTo_const 1 K) (Nat.mul_one K)))
    · refine Nat.le_trans ?_ (Nat.le_add_right _ _)
      show _ ≤ k * indB true
      rw [show indB true = 1 from rfl, Nat.mul_one]
      have pt : ∀ u, u < K → indB (true && !decide (runAdp K nxt (vswap K u a H) k = runAdp K nxt H k)) ≤
          indB (decide (u ∈ A)) := fun u hu => by
        by_cases hu' : u ∈ A
        · rw [decide_eq_true hu']; exact indB_le_one _
        · rw [runAdp_vswap hK hu ha nxt hnx k H hu' hs, decide_eq_true rfl, Bool.not_true, Bool.and_false]
          exact Nat.zero_le _
      refine Nat.le_trans (sumTo_mono _ pt) ?_
      refine Nat.le_trans (count_mem K A) (Nat.le_of_eq ?_)
      show ((runAdp K nxt H k).map Prod.snd).length = k
      rw [List.length_map, runAdp_length]

/-! ### Revisits of a sponge run -/

/-- Two answers of a run at distinct positions related by `cl`, or an
    answer related to one of the values `V`. -/
def colRV (cl : Nat → Nat → Bool) (V : List Nat) (l : List (Nat × Nat)) : Bool :=
  colR cl l || l.any (fun y => V.any (fun v => cl v y.2))

theorem colRV_cons {cl : Nat → Nat → Bool} {V : List Nat} (x : Nat × Nat) {l : List (Nat × Nat)}
    (h : colRV cl V l = true) : colRV cl V (x :: l) = true := by
  simp only [colRV, colR, List.any_cons, Bool.or_eq_true] at h ⊢
  rcases h with h | h
  · exact Or.inl (Or.inl h)
  · exact Or.inr (Or.inr h)

/-- **`colR_countP` with values `V` fixed in advance**: `k` adaptive forward
    queries see two related answers at distinct positions, or an answer
    related to one of `V`, on at most `(0 + ⋯ + (k-1) + k |V|) F / (K - k)`
    of the permutation tables. -/
theorem colRV_countP {K F : Nat} (hK : 0 < K) (cl : Nat → Nat → Bool) (hsym : ∀ a b, cl a b = cl b a)
    (hF : ∀ a, sumTo K (fun u => indB (cl a u)) ≤ F) (V : List Nat) (nxt : List Nat → Nat) (hnx : ∀ l, nxt l < K) :
    ∀ k, (K - k) * sumTo (K ^ K) (fun H => indB (permB K H && colRV cl V (runAdp K nxt H k))) ≤
      (sumTo k (fun j => j) + k * V.length) * F * sumTo (K ^ K) (fun H => indB (permB K H))
  | 0 => by
    refine Nat.le_trans (Nat.le_of_eq ?_) (Nat.zero_le _)
    rw [Nat.sub_zero, sumTo_congr (K ^ K) (g := fun _ => 0) (fun H _ => by
      show indB (permB K H && (false || false)) = 0; rw [Bool.or_false, Bool.and_false]; rfl), sumTo_const, Nat.mul_zero,
      Nat.mul_zero]
  | k + 1 => by
    have ih := colRV_countP hK cl hsym hF V nxt hnx k
    let p := fun H => nxt ((runAdp K nxt H k).map Prod.snd)
    let g := fun H => !decide (p H ∈ (runAdp K nxt H k).map Prod.fst)
    let A := fun H => (runAdp K nxt H k).map Prod.snd
    let S := fun H => nearR K cl ((runAdp K nxt H k).map Prod.snd ++ V)
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
    have fc := fresh_countP (j := k) (k := (k + V.length) * F) hK p (fun H => hnx _) g A S
      (fun H => by simp only [A, List.length_map, runAdp_length]; exact Nat.le_refl _)
      (fun H => by
        refine Nat.le_trans (nearR_length cl hF _) ?_
        rw [List.length_append, List.length_map, runAdp_length]; exact Nat.le_refl _) hfr hinv
    -- a new related answer is an old one, or a fresh answer near an old one or near `V`
    have pt0 : ∀ H, indB (colRV cl V (runAdp K nxt H (k + 1))) ≤ indB (colRV cl V (runAdp K nxt H k)) +
        indB (g H && decide (rget K (p H) H ∈ S H)) := by
      intro H
      let x2 := rget K (p H) H
      let rest := runAdp K nxt H k
      show indB ((colR cl rest || rest.any (fun y => y.1 != p H && cl y.2 x2)) ||
        (V.any (fun v => cl v x2) || rest.any (fun y => V.any (fun v => cl v y.2)))) ≤
        indB (colR cl rest || rest.any (fun y => V.any (fun v => cl v y.2))) + indB (g H && decide (x2 ∈ S H))
      cases hc : colR cl rest
      · cases hv : rest.any (fun y => V.any (fun v => cl v y.2))
        · rw [Bool.false_or, Bool.or_false, Bool.or_false]
          cases hn : (rest.any (fun y => y.1 != p H && cl y.2 x2) || V.any (fun v => cl v x2))
          · exact Nat.zero_le _
          · have hS : x2 ∈ S H := by
              show x2 ∈ nearR K cl ((runAdp K nxt H k).map Prod.snd ++ V)
              unfold nearR
              rw [List.mem_filter]
              refine ⟨List.mem_range.2 (rget_lt hK _ _), ?_⟩
              rcases Bool.or_eq_true _ _ ▸ hn with hn | hn
              · obtain ⟨y, hy, hyc⟩ := List.any_eq_true.1 hn
                rw [Bool.and_eq_true] at hyc
                exact List.any_eq_true.2 ⟨y.2, List.mem_append_left _ (List.mem_map.2 ⟨y, hy, rfl⟩), hyc.2⟩
              · obtain ⟨v, hv', hvc⟩ := List.any_eq_true.1 hn
                exact List.any_eq_true.2 ⟨v, List.mem_append_right _ hv', hvc⟩
            have hg : g H = true := by
              cases hg : g H
              · exfalso
                have hm : p H ∈ (runAdp K nxt H k).map Prod.fst := by
                  simp only [g, Bool.not_eq_false', decide_eq_true_eq] at hg; exact hg
                obtain ⟨z, hz, hzp⟩ := List.mem_map.1 hm
                have hza : z.2 = x2 := by rw [runAdp_ans K nxt H k z hz, hzp]
                rcases Bool.or_eq_true _ _ ▸ hn with hn | hn
                · obtain ⟨y, hy, hyc⟩ := List.any_eq_true.1 hn
                  rw [Bool.and_eq_true, bne_iff_ne] at hyc
                  have : colR cl rest = true :=
                    colR_of_mem cl hsym _ y z hy hz (by rw [hzp]; exact hyc.1) (by rw [hza]; exact hyc.2)
                  rw [hc] at this; exact Bool.false_ne_true this
                · have : rest.any (fun y => V.any (fun v => cl v y.2)) = true :=
                    List.any_eq_true.2 ⟨z, hz, by rw [hza]; exact hn⟩
                  rw [hv] at this; exact Bool.false_ne_true this
              · rfl
            rw [hg, decide_eq_true hS]; exact Nat.le_refl _
        · rw [Bool.or_true, Bool.or_true, Bool.or_true]; exact Nat.le_add_right _ _
      · rw [Bool.true_or, Bool.true_or, Bool.true_or]; exact Nat.le_add_right _ _
    have pt : ∀ H, indB (permB K H && colRV cl V (runAdp K nxt H (k + 1))) ≤
        indB (permB K H && colRV cl V (runAdp K nxt H k)) + indB (permB K H && g H && decide (rget K (p H) H ∈ S H)) := by
      intro H
      cases hP : permB K H
      · exact Nat.zero_le _
      · rw [Bool.true_and, Bool.true_and, Bool.true_and]; exact pt0 H
    have hkk : K - (k + 1) ≤ K - k := Nat.sub_le_sub_left (Nat.le_succ k) K
    refine Nat.le_trans (Nat.mul_le_mul_left _ (sumTo_mono _ (fun H _ => pt H))) ?_
    rw [sumTo_add, Nat.mul_add]
    refine Nat.le_trans (Nat.add_le_add (Nat.le_trans (Nat.mul_le_mul_right _ hkk) ih)
      (Nat.le_trans (Nat.mul_le_mul_right _ hkk) fc)) (Nat.le_of_eq ?_)
    show (sumTo k (fun j => j) + k * V.length) * F * _ + (k + V.length) * F * _ =
      (sumTo k (fun j => j) + k + (k + 1) * V.length) * F * _
    rw [← Nat.add_mul, ← Nat.add_mul, Nat.succ_mul]
    congr 2
    ac_rfl

/-- Each position after the first keeps `κ` of the answer before it, so a
    run's positions are the first, or `κ`-related to an earlier answer. -/
theorem runAdp_pred {K : Nat} (κ : Nat → Nat) (nxt : List Nat → Nat) (hκ : ∀ a l, κ (nxt (a :: l)) = κ a) (H : Nat) :
    ∀ k, ∀ z ∈ runAdp K nxt H (k + 1), z.1 = nxt [] ∨ ∃ y ∈ runAdp K nxt H k, κ z.1 = κ y.2
  | 0, z, hz => by
    rcases List.mem_cons.1 hz with e | e
    · exact Or.inl (by rw [e]; rfl)
    · exact absurd e List.not_mem_nil
  | k + 1, z, hz => by
    rcases List.mem_cons.1 hz with e | e
    · refine Or.inr ⟨_, List.mem_cons_self, ?_⟩
      rw [e]; exact hκ _ _
    · rcases runAdp_pred κ nxt hκ H k z e with h | ⟨y, hy, hk⟩
      · exact Or.inl h
      · exact Or.inr ⟨y, List.mem_cons_of_mem _ hy, hk⟩

/-- **A revisit is a `κ`-collision, or an answer `κ`-related to the first
    position**: when each position after the first keeps `κ` of the answer
    before it, a squeezed answer the run has already seen gives two answers
    at distinct positions with equal `κ`, or an answer with the first
    position's `κ`. -/
theorem revisit_colRV {K : Nat} (κ : Nat → Nat) (nxt : List Nat → Nat) (hnx : ∀ l, nxt l < K)
    (hκ : ∀ a l, κ (nxt (a :: l)) = κ a) {H : Nat} (hP : permB K H = true) :
    ∀ k, rget K (nxt ((runAdp K nxt H k).map Prod.snd)) H ∈ (runAdp K nxt H k).map Prod.snd →
      colRV (fun a b => decide (κ a = κ b)) [nxt []] (runAdp K nxt H k) = true
  | 0, h => by
    change _ ∈ ([] : List Nat) at h
    exact absurd h List.not_mem_nil
  | k + 1, h => by
    let A := (runAdp K nxt H k).map Prod.snd
    let x : Nat × Nat := (nxt A, rget K (nxt A) H)
    let q := nxt ((runAdp K nxt H (k + 1)).map Prod.snd)
    have hq : κ q = κ x.2 := hκ _ _
    obtain ⟨z, hz, hza⟩ := List.mem_map.1 h
    have hzq : z.1 = q := permB_inj hP (runAdp_pos nxt hnx H (k + 1) z hz) (hnx _)
      (by rw [← runAdp_ans K nxt H (k + 1) z hz]; exact hza)
    rcases runAdp_pred κ nxt hκ H k z hz with h1 | ⟨y, hy, hky⟩
    · show ((colR _ (runAdp K nxt H k) || _) || ((decide (κ (nxt []) = κ x.2) || false) || _)) = true
      rw [← hq, ← hzq, h1, decide_eq_true rfl, Bool.true_or, Bool.true_or, Bool.or_true]
    · by_cases hyx : y.1 = x.1
      · refine colRV_cons x (revisit_colRV κ nxt hnx hκ hP k (List.mem_map.2 ⟨y, hy, ?_⟩))
        rw [runAdp_ans K nxt H k y hy, hyx]
      · show ((colR _ (runAdp K nxt H k) || (runAdp K nxt H k).any (fun y => y.1 != x.1 && decide (κ y.2 = κ x.2))) ||
          _) = true
        have : (runAdp K nxt H k).any (fun y => y.1 != x.1 && decide (κ y.2 = κ x.2)) = true :=
          List.any_eq_true.2 ⟨y, hy, by rw [Bool.and_eq_true, bne_iff_ne, decide_eq_true_eq, ← hq, ← hzq, hky]; exact ⟨hyx, rfl⟩⟩
        rw [this, Bool.or_true, Bool.true_or]

/-- **A run rarely revisits**: with each position after the first keeping
    `κ` of the answer before it, `κ`'s fibres below `K` at most `F`, the
    squeezed answer of `k` adaptive forward queries is one the run has
    already seen on at most `(0 + ⋯ + (k-1) + k) F / (K - k)` of the
    permutation tables. -/
theorem revisit_countP {K F : Nat} (hK : 0 < K) (κ : Nat → Nat) (hF : ∀ v, sumTo K (fun u => indB (decide (κ u = v))) ≤ F)
    (nxt : List Nat → Nat) (hnx : ∀ l, nxt l < K) (hκ : ∀ a l, κ (nxt (a :: l)) = κ a) (k : Nat) :
    (K - k) * sumTo (K ^ K) (fun H => indB (permB K H &&
        decide (rget K (nxt ((runAdp K nxt H k).map Prod.snd)) H ∈ (runAdp K nxt H k).map Prod.snd))) ≤
      (sumTo k (fun j => j) + k) * F * sumTo (K ^ K) (fun H => indB (permB K H)) := by
  have h := colRV_countP hK (fun a b => decide (κ a = κ b)) (rel_symm κ) (fib_rel κ hF) [nxt []] nxt hnx k
  rw [show [nxt []].length = 1 from rfl, Nat.mul_one] at h
  refine Nat.le_trans (Nat.mul_le_mul_left _ (sumTo_mono _ (fun H _ => ?_))) h
  cases hP : permB K H
  · exact Nat.zero_le _
  · cases hr : decide (rget K (nxt ((runAdp K nxt H k).map Prod.snd)) H ∈ (runAdp K nxt H k).map Prod.snd)
    · exact Nat.zero_le _
    · rw [revisit_colRV κ nxt hnx hκ hP k (of_decide_eq_true hr)]; exact Nat.le_refl _

/-- **A challenge squeezed from a run, traded for an independent value**:
    `squeeze_swap` at a run's squeeze position, its exchanges that change
    the run counted by `squeeze_bad_run` and `revisit_countP`.  Divided by
    `(K - k) K` times the permutation tables, the error is at most
    `k / K + (0 + ⋯ + (k-1) + k) F / (K - k)`. -/
theorem squeeze_run {K F : Nat} (hK : 0 < K) (κ : Nat → Nat) (hF : ∀ v, sumTo K (fun u => indB (decide (κ u = v))) ≤ F)
    (nxt : List Nat → Nat) (hnx : ∀ l, nxt l < K) (hκ : ∀ a l, κ (nxt (a :: l)) = κ a) (k : Nat)
    (f : List (Nat × Nat) → Nat → Nat → Bool) :
    (K - k) * (K * sumTo (K ^ K) (fun H => indB (permB K H &&
        f (runAdp K nxt H k) H (rget K (nxt ((runAdp K nxt H k).map Prod.snd)) H)))) ≤
      (K - k) * sumTo K (fun w => sumTo (K ^ K) (fun H => indB (permB K H &&
        f (runAdp K nxt H k) (vswap K (rget K (nxt ((runAdp K nxt H k).map Prod.snd)) H) w H) w))) +
      (K - k) * k * sumTo (K ^ K) (fun H => indB (permB K H)) +
      K * ((sumTo k (fun j => j) + k) * F * sumTo (K ^ K) (fun H => indB (permB K H))) := by
  have h1 := squeeze_swap hK (fun H => runAdp K nxt H k) (fun c => nxt (c.map Prod.snd)) (fun _ => hnx _) f
  have h2 := squeeze_bad_run hK nxt hnx k
  have h3 := revisit_countP hK κ hF nxt hnx hκ k
  refine Nat.le_trans (Nat.mul_le_mul_left _ (Nat.le_trans h1 (Nat.add_le_add_left h2 _))) ?_
  rw [Nat.mul_add, Nat.mul_add, ← Nat.mul_assoc, Nat.add_assoc]
  refine Nat.add_le_add_left (Nat.add_le_add_left ?_ _) _
  rw [Nat.mul_left_comm]
  exact Nat.mul_le_mul_left _ h3

/-! ### Plonky3 0.8's duplex -/

/-- The duplex's next position: `p1` first, then each answer absorbing
    the block `blk` chooses from the earlier answers, the block `SQ` a
    squeeze (`inner08s`). -/
def nxt08 (R p Q SQ p1 : Nat) (blk : List Nat → Nat) : List Nat → Nat
  | [] => p1
  | a :: l => inner08s R (p ^ R) p Q SQ a (blk l)

theorem nxt08_lt {R p Q SQ p1 : Nat} (hR : 0 < R) (hp : 0 < p) (hQ : 0 < Q) (h1 : p1 < p ^ R * (p * Q))
    (blk : List Nat → Nat) : ∀ l, nxt08 R p Q SQ p1 blk l < p ^ R * (p * Q)
  | [] => h1
  | _ :: _ => inner08s_lt hR hp hQ _ _

/-- **0.8's absorption and its empty-buffer squeeze both keep the
    capacity's tail.** -/
theorem nxt08_κ {R p Q SQ p1 : Nat} (hR : 0 < R) (hp : 0 < p) (hQ : 0 < Q) (blk : List Nat → Nat) (a : Nat) (l : List Nat) :
    κ08 (p ^ R) p Q (nxt08 R p Q SQ p1 blk (a :: l)) = κ08 (p ^ R) p Q a := by
  show κ08 (p ^ R) p Q (inner08s R (p ^ R) p Q SQ a (blk l)) = κ08 (p ^ R) p Q a
  unfold inner08s; split
  · exact κ08_mod hQ a
  · exact κ08_inner08 hR hp a _

/-- **`squeeze_run` for 0.8's duplex**, absorptions and empty-buffer
    squeezes in any order: the width `K = p^R p Q`, `F = p^R p`, so the
    revisit term is `(0 + ⋯ + (k-1) + k) / (Q (1 - k/K))`, `Q` the
    capacity's tail. -/
theorem squeeze_run08 {R p Q SQ p1 : Nat} (hR : 0 < R) (hp : 0 < p) (hQ : 0 < Q) (h1 : p1 < p ^ R * (p * Q))
    (blk : List Nat → Nat) (k : Nat) (f : List (Nat × Nat) → Nat → Nat → Bool) :
    let K := p ^ R * (p * Q)
    let nxt := nxt08 R p Q SQ p1 blk
    (K - k) * (K * sumTo (K ^ K) (fun H => indB (permB K H &&
        f (runAdp K nxt H k) H (rget K (nxt ((runAdp K nxt H k).map Prod.snd)) H)))) ≤
      (K - k) * sumTo K (fun w => sumTo (K ^ K) (fun H => indB (permB K H &&
        f (runAdp K nxt H k) (vswap K (rget K (nxt ((runAdp K nxt H k).map Prod.snd)) H) w H) w))) +
      (K - k) * k * sumTo (K ^ K) (fun H => indB (permB K H)) +
      K * ((sumTo k (fun j => j) + k) * (p ^ R * p) * sumTo (K ^ K) (fun H => indB (permB K H))) :=
  squeeze_run (Nat.mul_pos (Nat.pow_pos hp) (Nat.mul_pos hp hQ)) (κ08 (p ^ R) p Q)
    (κ08_count (Nat.mul_pos (Nat.pow_pos hp) hp)) _ (nxt08_lt hR hp hQ h1 blk) (nxt08_κ hR hp hQ blk) k f

/-! ### The fourth challenge squeezed from the permutation -/

theorem indB_and (a b : Bool) : indB (a && b) = indB a * indB b := by cases a <;> cases b <;> rfl

/-- `K` times a count over tables read at one entry is `K^n` times the count
    over that entry's values. -/
theorem sumTo_rget_one {K n v : Nat} (hK : 0 < K) (hv : v < n) (g : Nat → Nat) :
    K * sumTo (K ^ n) (fun H => g (rget K v H)) = K ^ n * sumTo K g := by
  have e := reprog_swap (n := n) hK hv (fun c _ => g c)
  rw [sumTo_congr _ (fun H _ => sumTo_const (g (rget K v H)) K), sumTo_const] at e
  rw [sumTo_mul]; exact e

/-- **A composite's challenge squeezed from the permutation.**  The
    hypothesis `hyp` is a composite's bound over a uniform permutation `P`,
    a table `H4` independent of it and the other tables `H`, every
    distinguisher `D` reading all three: the real view reads its challenge
    from `H4` at the squeeze position of `k` adaptive forward queries to
    `P` (the run's blocks chosen by `H` and the draws `x`), and depends on
    `P` only through the run; the simulator programs `H4` at its own
    position `φs` with the challenge `c`.  The conclusion is the bound with
    no `H4`: the real view reads its challenge from `P` at the squeeze
    position, and the simulator programs `P` itself, exchanging its answer
    at `φs` with `c`.  The distinguisher must find the squeeze position from
    the view (`pos`), in both worlds.  The error gains the run's exchanges
    and revisits (`squeeze_run`). -/
theorem zk_squeeze {T X C V : Type} {K F k K4w ε : Nat} (hK : 0 < K) (κ : Nat → Nat)
    (hF : ∀ v, sumTo K (fun u => indB (decide (κ u = v))) ≤ F)
    (ST : (T → Nat) → Nat) (hST : Lin ST) (sm : (X → Nat) → Nat) (hsm : Lin sm)
    (SC : (C → Nat) → Nat) (hSC : Lin SC)
    (nxt : T → X → List Nat → Nat) (hnx : ∀ H x l, nxt H x l < K) (hκ : ∀ H x a l, κ (nxt H x (a :: l)) = κ a)
    (rv : List (Nat × Nat) → T → X → Nat → V) (pg : T → C → X → T) (φs : Nat → T → C → X → Nat)
    (sv : Nat → T → Nat → C → X → V) (pos : Nat → T → V → Nat)
    (hpr : ∀ P H x w, pos P H (rv (runAdp K (nxt H x) P k) H x w) = nxt H x ((runAdp K (nxt H x) P k).map Prod.snd))
    (hps : ∀ P H c c' x, pos P (pg H c' x) (sv P H c c' x) = φs P H c' x)
    (hyp : ∀ D : Nat → Nat → T → V → Bool,
      K4w * ST (fun H => sm (fun x => sumTo (K ^ K) (fun P => indB (permB K P) * sumTo (K ^ K) (fun H4 =>
        indB (D P H4 H (rv (runAdp K (nxt H x) P k) H x
          (rget K (nxt H x ((runAdp K (nxt H x) P k).map Prod.snd)) H4))))))) ≤
      ST (fun H => sumTo K (fun c => SC (fun c' => sm (fun x => sumTo (K ^ K) (fun P => indB (permB K P) *
        sumTo (K ^ K) (fun H4 => indB (D P (rset K (φs P H c' x) H4 c) (pg H c' x) (sv P H c c' x)))))))) + ε)
    (E : Nat → T → V → Bool) :
    K4w * (K ^ K * ((K - k) * (K * ST (fun H => sm (fun x => sumTo (K ^ K) (fun P => indB (permB K P &&
        E P H (rv (runAdp K (nxt H x) P k) H x (rget K (nxt H x ((runAdp K (nxt H x) P k).map Prod.snd)) P))))))))) ≤
      (K - k) * (K * (K ^ K * ST (fun H => sumTo K (fun c => SC (fun c' => sm (fun x => sumTo (K ^ K) (fun P =>
        indB (permB K P && E (vswap K (rget K (φs P H c' x) P) c P) (pg H c' x) (sv P H c c' x))))))))) +
      (K - k) * (K * ε) +
      K4w * (K ^ K * (ST (fun _ => sm (fun _ => 1)) * (((K - k) * k + K * ((sumTo k (fun j => j) + k) * F)) *
        sumTo (K ^ K) (fun P => indB (permB K P))))) := by
  let DE : Nat → Nat → T → V → Bool := fun P H4 H' v =>
    E (vswap K (rget K (pos P H' v) P) (rget K (pos P H' v) H4) P) H' v
  have h := hyp DE
  let Err := ((K - k) * k + K * ((sumTo k (fun j => j) + k) * F)) * sumTo (K ^ K) (fun P => indB (permB K P))
  -- the ideal count of `squeeze_run`, per `H` and `x`
  let B := fun (H : T) (x : X) => sumTo K (fun w => sumTo (K ^ K) (fun P => indB (permB K P &&
    E (vswap K (rget K (nxt H x ((runAdp K (nxt H x) P k).map Prod.snd)) P) w P) H (rv (runAdp K (nxt H x) P k) H x w))))
  -- the real side of `hyp` at `DE` is the ideal count
  have hR : ∀ H x, K * sumTo (K ^ K) (fun P => indB (permB K P) * sumTo (K ^ K) (fun H4 =>
      indB (DE P H4 H (rv (runAdp K (nxt H x) P k) H x
        (rget K (nxt H x ((runAdp K (nxt H x) P k).map Prod.snd)) H4))))) = K ^ K * B H x := by
    intro H x
    show _ = K ^ K * sumTo K (fun w => sumTo (K ^ K) (fun P => _))
    rw [sumTo_exch _ (K ^ K) K, sumTo_mul, sumTo_mul]
    refine sumTo_congr _ (fun P _ => ?_)
    have e1 : ∀ H4, DE P H4 H (rv (runAdp K (nxt H x) P k) H x (rget K (nxt H x ((runAdp K (nxt H x) P k).map Prod.snd)) H4)) =
        E (vswap K (rget K (nxt H x ((runAdp K (nxt H x) P k).map Prod.snd)) P)
          (rget K (nxt H x ((runAdp K (nxt H x) P k).map Prod.snd)) H4) P) H
          (rv (runAdp K (nxt H x) P k) H x (rget K (nxt H x ((runAdp K (nxt H x) P k).map Prod.snd)) H4)) := fun H4 => by
      show E (vswap K (rget K (pos P H _) P) (rget K (pos P H _) H4) P) H _ = _
      rw [hpr]
    rw [sumTo_congr _ (fun H4 _ => congrArg indB (e1 H4)), Nat.mul_left_comm,
      sumTo_rget_one hK (hnx H x _) (fun w => indB (E (vswap K (rget K (nxt H x ((runAdp K (nxt H x) P k).map Prod.snd)) P) w P) H
        (rv (runAdp K (nxt H x) P k) H x w))),
      sumTo_congr K (fun w _ => indB_and _ _), ← sumTo_mul]
    exact Nat.mul_left_comm _ _ _
  -- the simulated side of `hyp` at `DE` programs the permutation
  have hS : ∀ H c c' x, c < K → sumTo (K ^ K) (fun P => indB (permB K P) *
      sumTo (K ^ K) (fun H4 => indB (DE P (rset K (φs P H c' x) H4 c) (pg H c' x) (sv P H c c' x)))) =
      K ^ K * sumTo (K ^ K) (fun P => indB (permB K P && E (vswap K (rget K (φs P H c' x) P) c P) (pg H c' x) (sv P H c c' x))) := by
    intro H c c' x hc
    rw [sumTo_mul]
    refine sumTo_congr _ (fun P _ => ?_)
    have e1 : ∀ H4, DE P (rset K (φs P H c' x) H4 c) (pg H c' x) (sv P H c c' x) =
        E (vswap K (rget K (φs P H c' x) P) c P) (pg H c' x) (sv P H c c' x) := fun H4 => by
      show E (vswap K (rget K (pos P _ _) P) (rget K (pos P _ _) (rset K (φs P H c' x) H4 c)) P) _ _ = _
      rw [hps, rget_rset hK hc]
    rw [sumTo_congr _ (fun H4 _ => congrArg indB (e1 H4)), sumTo_const, indB_and]
    exact Nat.mul_left_comm _ _ _
  -- `squeeze_run` at each `H` and `x`
  have hq : ∀ H x, (K - k) * (K * sumTo (K ^ K) (fun P => indB (permB K P &&
      E P H (rv (runAdp K (nxt H x) P k) H x (rget K (nxt H x ((runAdp K (nxt H x) P k).map Prod.snd)) P))))) ≤
      (K - k) * B H x + Err := fun H x => by
    have := squeeze_run hK κ hF (nxt H x) (hnx H x) (hκ H x) k (fun c P' w => E P' H (rv c H x w))
    refine Nat.le_trans this (Nat.le_of_eq ?_)
    rw [Nat.add_assoc]; congr 1
    show _ = ((K - k) * k + K * ((sumTo k (fun j => j) + k) * F)) * sumTo (K ^ K) (fun P => indB (permB K P))
    rw [Nat.add_mul ((K - k) * k), Nat.mul_assoc K]
  have smm : ∀ {f g : X → Nat}, (∀ x, f x ≤ g x) → sm f ≤ sm g := fun h => sm_mono sm hsm h
  have stm : ∀ {f g : T → Nat}, (∀ H, f H ≤ g H) → ST f ≤ ST g := fun h => sm_mono ST hST h
  -- the real count of `hyp` at `DE`, per `H` and `x`
  let R4 := fun (H : T) (x : X) => sumTo (K ^ K) (fun P => indB (permB K P) * sumTo (K ^ K) (fun H4 =>
    indB (DE P H4 H (rv (runAdp K (nxt H x) P k) H x (rget K (nxt H x ((runAdp K (nxt H x) P k).map Prod.snd)) H4)))))
  -- the real count of the conclusion, per `H` and `x`
  let A := fun (H : T) (x : X) => sumTo (K ^ K) (fun P => indB (permB K P &&
    E P H (rv (runAdp K (nxt H x) P k) H x (rget K (nxt H x ((runAdp K (nxt H x) P k).map Prod.snd)) P))))
  -- the simulated count of the conclusion, per `H`, `c`, `c'` and `x`
  let SP := fun (H : T) (c : Nat) (c' : C) (x : X) => sumTo (K ^ K) (fun P =>
    indB (permB K P && E (vswap K (rget K (φs P H c' x) P) c P) (pg H c' x) (sv P H c c' x)))
  have e1 : K4w * (K ^ K * ((K - k) * (K * ST (fun H => sm (fun x => A H x))))) =
      K4w * (K ^ K * ST (fun H => sm (fun x => (K - k) * (K * A H x)))) := by
    refine congrArg (fun t => K4w * (K ^ K * t)) ?_
    rw [← smK ST hST, ← smK ST hST]
    refine congrArg ST (funext fun H => ?_)
    rw [smK sm hsm, smK sm hsm]
  have e3a : ∀ H, sm (fun x => (K - k) * B H x + Err) = (K - k) * sm (fun x => B H x) + Err * sm (fun _ => 1) := by
    intro H; rw [sm_add sm hsm, smK sm hsm, smC sm hsm]
  have e3b : ∀ H, K ^ K * sm (fun x => B H x) = K * sm (fun x => R4 H x) := by
    intro H; rw [← smK sm hsm, ← smK sm hsm]; exact congrArg sm (funext fun x => (hR H x).symm)
  have e3 : K4w * (K ^ K * ST (fun H => sm (fun x => (K - k) * B H x + Err))) =
      (K - k) * (K * (K4w * ST (fun H => sm (fun x => R4 H x)))) +
        K4w * (K ^ K * (ST (fun _ => sm (fun _ => 1)) * Err)) := by
    rw [congrArg ST (funext e3a), sm_add ST hST, smK ST hST, smK ST hST, Nat.mul_add, Nat.mul_add,
      ← Nat.mul_assoc (K ^ K) (K - k), Nat.mul_comm (K ^ K) (K - k), Nat.mul_assoc (K - k) (K ^ K),
      ← smK ST hST (K ^ K), congrArg ST (funext e3b), smK ST hST, Nat.mul_comm Err]
    congr 1
    rw [Nat.mul_left_comm K4w (K - k), Nat.mul_left_comm K4w K]
  have e5 : ST (fun H => sumTo K (fun c => SC (fun c' => sm (fun x => sumTo (K ^ K) (fun P => indB (permB K P) *
      sumTo (K ^ K) (fun H4 => indB (DE P (rset K (φs P H c' x) H4 c) (pg H c' x) (sv P H c c' x)))))))) =
      K ^ K * ST (fun H => sumTo K (fun c => SC (fun c' => sm (fun x => SP H c c' x)))) := by
    rw [← smK ST hST]
    refine congrArg ST (funext fun H => ?_)
    rw [sumTo_mul]
    refine sumTo_congr _ (fun c hc => ?_)
    rw [← smK SC hSC]
    refine congrArg SC (funext fun c' => ?_)
    rw [← smK sm hsm]
    exact congrArg sm (funext fun x => hS H c c' x hc)
  calc K4w * (K ^ K * ((K - k) * (K * ST (fun H => sm (fun x => A H x)))))
      = K4w * (K ^ K * ST (fun H => sm (fun x => (K - k) * (K * A H x)))) := e1
    _ ≤ K4w * (K ^ K * ST (fun H => sm (fun x => (K - k) * B H x + Err))) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (stm (fun H => smm (fun x => hq H x))))
    _ = (K - k) * (K * (K4w * ST (fun H => sm (fun x => R4 H x)))) +
        K4w * (K ^ K * (ST (fun _ => sm (fun _ => 1)) * Err)) := e3
    _ ≤ (K - k) * (K * (ST (fun H => sumTo K (fun c => SC (fun c' => sm (fun x => sumTo (K ^ K) (fun P => indB (permB K P) *
        sumTo (K ^ K) (fun H4 => indB (DE P (rset K (φs P H c' x) H4 c) (pg H c' x) (sv P H c c' x)))))))) + ε)) +
        K4w * (K ^ K * (ST (fun _ => sm (fun _ => 1)) * Err)) :=
        Nat.add_le_add_right (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h)) _
    _ = _ := by
        rw [e5, Nat.mul_add, Nat.mul_add]

/-- **`zk_squeeze`'s hypotheses hold together, at 0.8's duplex**: `k`
    absorptions and empty-buffer squeezes in any order (`nxt08`), one
    challenge, the view the challenge itself, the simulator programming the
    table at the run's squeeze position with its challenge, so `hyp` holds
    exactly (`oracle_reprog_get`).  The conclusion says the permutation and
    its answer at the run's squeeze position look as the permutation does
    with that answer exchanged for a uniform state, up to the run's
    exchanges and revisits. -/
theorem zk_squeeze_sat08 {R p Q SQ p1 : Nat} (hR : 0 < R) (hp : 0 < p) (hQ : 0 < Q) (h1 : p1 < p ^ R * (p * Q))
    (blk : List Nat → Nat) (k : Nat) (E : Nat → Unit → Nat → Bool) :
    let K := p ^ R * (p * Q)
    let nxt := nxt08 R p Q SQ p1 blk
    K * (K ^ K * ((K - k) * (K * sumTo (K ^ K) (fun P => indB (permB K P &&
        E P () (rget K (nxt ((runAdp K nxt P k).map Prod.snd)) P)))))) ≤
      (K - k) * (K * (K ^ K * sumTo K (fun c => sumTo (K ^ K) (fun P =>
        indB (permB K P && E (vswap K (rget K (nxt ((runAdp K nxt P k).map Prod.snd)) P) c P) () c))))) +
      (K - k) * (K * 0) +
      K * (K ^ K * (1 * (((K - k) * k + K * ((sumTo k (fun j => j) + k) * (p ^ R * p))) *
        sumTo (K ^ K) (fun P => indB (permB K P))))) := by
  intro K nxt
  have hK : 0 < K := Nat.mul_pos (Nat.pow_pos hp) (Nat.mul_pos hp hQ)
  have hnx := nxt08_lt (SQ := SQ) hR hp hQ h1 blk
  have hyp : ∀ D : Nat → Nat → Unit → Nat → Bool,
      K * sumTo (K ^ K) (fun P => indB (permB K P) * sumTo (K ^ K) (fun H4 =>
        indB (D P H4 () (rget K (nxt ((runAdp K nxt P k).map Prod.snd)) H4)))) ≤
        sumTo K (fun c => sumTo (K ^ K) (fun P => indB (permB K P) *
          sumTo (K ^ K) (fun H4 => indB (D P (rset K (nxt ((runAdp K nxt P k).map Prod.snd)) H4 c) () c)))) + 0 :=
    fun D => by
    rw [Nat.add_zero, sumTo_exch _ (K ^ K) K, sumTo_mul]
    refine Nat.le_of_eq (sumTo_congr _ (fun P _ => ?_))
    rw [← sumTo_mul, Nat.mul_left_comm, sumTo_exch _ (K ^ K) K,
      oracle_reprog_get hK (hnx _) (fun H4 c => indB (D P H4 () c))]
  exact zk_squeeze (T := Unit) (X := Unit) (C := Unit) (k := k) hK (κ08 (p ^ R) p Q)
    (κ08_count (Nat.mul_pos (Nat.pow_pos hp) hp)) (fun f => f ()) (fun _ _ => rfl)
    (fun f => f ()) (fun _ _ => rfl) (fun f => f ()) (fun _ _ => rfl)
    (fun _ _ => nxt) (fun _ _ => hnx) (fun _ _ => nxt08_κ (SQ := SQ) (p1 := p1) hR hp hQ blk)
    (fun _ _ _ w => w) (fun H _ _ => H) (fun P _ _ _ => nxt ((runAdp K nxt P k).map Prod.snd)) (fun _ _ c _ _ => c)
    (fun P _ _ => nxt ((runAdp K nxt P k).map Prod.snd))
    (fun _ _ _ _ => rfl) (fun _ _ _ _ _ => rfl) hyp E

end Circuit
