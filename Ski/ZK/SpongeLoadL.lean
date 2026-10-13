import Ski.ZK.SpongeLoad

/-!
# The load over several absorptions

`SpongeLoad` bounds the index's preimage one absorption after the first
commitment.  Here the index is the state `L + 1` absorptions after it,
the later blocks any of `X^L` lists.

- **The joint run.** The `n1` chains run as one adaptive run, step-major
  (`nxtJ`), its queries the chains' positions in order (`runJ_eq`); its
  hits on a set count the distinct queried positions whose answers lie in
  it (`hitN_eq_sum`).
- **The ancestry.** The chains reaching `v` occupy fewer positions at
  each later step; going one step back, each position's predecessors share
  a capacity value (`hpk`), so on a table where every capacity value holds
  fewer than `m` of the run's hits they number at most `m - 1` times as
  many (`anc_step`).  The first positions are distinct (`hd`) and the last
  is one, so at most `(m - 1)^L` chains reach `v` (`preimage_good`);
  `loadML` adds `n1` where some capacity value holds `m` hits
  (`preimage_loadML`).
- **Every later transcript.** A union over the `X^L` block lists gives
  `loadMA`, a bound at the table for every later block list
  (`preimage_loadMA`), and `δs' = δs loadMA` meets `SudChallenger`'s
  `hsp1` and `hφsp` (`loadA_hsp`).  Averaged over a uniform permutation,
  with `k = n1 (L + 1)` queries,
  `m! (K - k)^m E[loadMA] ≤ m! (K - k)^m (m - 1)^L + n1 X^L Kc (k F)^m`
  (`loadMA_countP`, `loadA_δs_countP`).
- **The composite.** `sud_interleaveS` with this index, averaged over the
  permutation, with a number for its error (`sud_interleaveLA`,
  `sud_interleaveLAN`).

Size.  With `F / K` one over the capacity's size and `n1 F / (K - k)` near
`1`, the ratio `k F / (K - k)` is near `L + 1`, and the bound asks
`m! ≥ n1 X^L Kc (L + 1)^m`.  With `n1 = Kc = X = 2^248` the smallest such
`m` is about `154`, `211`, `268` for `L = 1, 2, 3`, so `E[loadMA]` is about
`2^7`, `2^15`, `2^24`, against `n1 = 2^248`.  The bound grows as `m^L`: it
suits a few absorptions, not a whole transcript.

Limits, as in `SpongeLoad`: the state before the first commitment is
fixed, the first commitment fills one aligned block, `H4` stays independent
of the permutation, and the later blocks do not depend on the salt.
-/

set_option autoImplicit false

namespace Circuit
open ZKF

/-- The joint run of the `n1` chains, step-major: query `ℓ` is chain
    `ℓ % n1` at step `ℓ / n1`, from `iv` at step `0`, else from that
    chain's previous answer, `n1` answers back. -/
def nxtJ (inner : Nat → Nat → Nat) (iv n1 : Nat) (xs : List Nat) (l : List Nat) : Nat :=
  if l.length < n1 then inner iv l.length else inner (l.getD (n1 - 1) 0) (xs.getD (l.length / n1 - 1) 0)

/-- Query `t`'s position: chain `t % n1` at step `t / n1`. -/
def posJ (K : Nat) (inner : Nat → Nat → Nat) (iv n1 : Nat) (xs : List Nat) (H t : Nat) : Nat :=
  inner (chain1 K inner iv ((t % n1) :: xs) H (t / n1)) (((t % n1) :: xs).getD (t / n1) 0)

theorem rget_posJ (K : Nat) (inner : Nat → Nat → Nat) (iv n1 : Nat) (xs : List Nat) (H t : Nat) :
    rget K (posJ K inner iv n1 xs H t) H = chain1 K inner iv ((t % n1) :: xs) H (t / n1 + 1) := rfl

/-- **The joint run is the chains' queries in order.** -/
theorem runJ_eq (K : Nat) (inner : Nat → Nat → Nat) (iv : Nat) {n1 : Nat} (hn1 : 0 < n1) (xs : List Nat) (H : Nat) :
    ∀ ℓ, runAdp K (nxtJ inner iv n1 xs) H ℓ =
      (List.range ℓ).reverse.map (fun t => (posJ K inner iv n1 xs H t, rget K (posJ K inner iv n1 xs H t) H))
  | 0 => rfl
  | ℓ + 1 => by
    have ih := runJ_eq K inner iv hn1 xs H ℓ
    show (nxtJ inner iv n1 xs ((runAdp K (nxtJ inner iv n1 xs) H ℓ).map Prod.snd), _) :: runAdp K (nxtJ inner iv n1 xs) H ℓ = _
    rw [List.range_succ, List.reverse_append, List.map_append, ih]
    have hp : nxtJ inner iv n1 xs ((((List.range ℓ).reverse.map (fun t => (posJ K inner iv n1 xs H t,
        rget K (posJ K inner iv n1 xs H t) H))).map Prod.snd)) = posJ K inner iv n1 xs H ℓ := by
      unfold nxtJ
      rw [List.length_map, List.length_map, List.length_reverse, List.length_range]
      by_cases hl : ℓ < n1
      · rw [if_pos hl]
        unfold posJ
        rw [Nat.mod_eq_of_lt hl, Nat.div_eq_of_lt hl]; rfl
      · rw [if_neg hl]
        have hge : n1 ≤ ℓ := Nat.le_of_not_lt hl
        have hidx : n1 - 1 < ℓ := by omega
        rw [List.map_map, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_reverse (by
          rw [List.length_range]; exact hidx), List.getElem?_range (by rw [List.length_range]; omega)]
        rw [List.length_range]
        show inner (rget K (posJ K inner iv n1 xs H (ℓ - 1 - (n1 - 1))) H) (xs.getD (ℓ / n1 - 1) 0) = _
        have e1 : ℓ - 1 - (n1 - 1) = ℓ - n1 := by omega
        rw [e1, rget_posJ]
        have hq : ℓ / n1 = (ℓ - n1) / n1 + 1 := by
          rw [← Nat.sub_add_cancel hge, Nat.add_div_right _ hn1, Nat.sub_add_cancel hge]
        have hr : (ℓ - n1) % n1 = ℓ % n1 := by
          conv => rhs; rw [← Nat.sub_add_cancel hge]
          rw [Nat.add_mod_right]
        unfold posJ
        rw [hr, hq]
        rfl
    rw [hp]; rfl

theorem sumTo_point (a : Nat) {x : Nat} : ∀ n, x < n → sumTo n (fun p => indB (decide (p = x)) * a) = a
  | 0, h => absurd h (Nat.not_lt_zero _)
  | n + 1, h => by
    show sumTo n _ + indB (decide (n = x)) * a = a
    rcases Nat.lt_or_ge x n with hx | hx
    · rw [sumTo_point a n hx, decide_eq_false (Nat.ne_of_gt hx)]; simp [indB]
    · have e : x = n := Nat.le_antisymm (Nat.le_of_lt_succ h) hx
      subst e
      have z : sumTo x (fun p => indB (decide (p = x)) * a) = 0 :=
        Eq.trans (sumTo_congr _ (fun p hp => by rw [decide_eq_false (Nat.ne_of_lt hp)]; simp [indB]))
          (Eq.trans (sumTo_const 0 x) (Nat.mul_zero x))
      rw [z, decide_eq_true rfl]; simp [indB]

/-- **Hits are the distinct queried positions whose answers lie in `T`.** -/
theorem hitN_eq_sum {K : Nat} (T : List Nat) (H : Nat) :
    ∀ l : List (Nat × Nat), (∀ y ∈ l, y.2 = rget K y.1 H ∧ y.1 < K) →
      hitN T l = sumTo K (fun p => indB (decide (p ∈ l.map Prod.fst) && decide (rget K p H ∈ T)))
  | [] => fun _ => by
    show 0 = _
    exact (Eq.trans (sumTo_congr _ (fun p _ => rfl)) (Eq.trans (sumTo_const 0 K) (Nat.mul_zero K))).symm
  | x :: rest => fun h => by
    have hx := h x List.mem_cons_self
    have ih := hitN_eq_sum T H rest (fun y hy => h y (List.mem_cons_of_mem _ hy))
    show hitN T rest + indB (!decide (x.1 ∈ rest.map Prod.fst) && decide (x.2 ∈ T)) = _
    rw [ih, hx.1]
    have pt : ∀ p, indB (decide (p ∈ (x :: rest).map Prod.fst) && decide (rget K p H ∈ T)) =
        indB (decide (p ∈ rest.map Prod.fst) && decide (rget K p H ∈ T)) +
          indB (decide (p = x.1)) * indB (!decide (x.1 ∈ rest.map Prod.fst) && decide (rget K x.1 H ∈ T)) := fun p => by
      by_cases e : p = x.1
      · rw [e]
        by_cases hm : x.1 ∈ rest.map Prod.fst
        · have : x.1 ∈ (x :: rest).map Prod.fst := List.mem_cons_of_mem _ hm
          rw [decide_eq_true this, decide_eq_true hm]; simp [indB]
        · have : x.1 ∈ (x :: rest).map Prod.fst := List.mem_cons_self
          rw [decide_eq_true this, decide_eq_false hm]; simp [indB]
      · have iff : p ∈ (x :: rest).map Prod.fst ↔ p ∈ rest.map Prod.fst := by
          rw [List.map_cons, List.mem_cons]; exact ⟨fun h => h.resolve_left e, Or.inr⟩
        by_cases hm : p ∈ rest.map Prod.fst
        · rw [decide_eq_true (iff.2 hm), decide_eq_true hm, decide_eq_false e]; simp [indB]
        · rw [decide_eq_false (fun h' => hm (iff.1 h')), decide_eq_false hm, decide_eq_false e]; simp [indB]
    rw [sumTo_congr _ (fun p _ => pt p), sumTo_add, sumTo_point _ K hx.2]

/-- At most one argument below `n` meets `Q`: its count is at most one. -/
theorem sum_le_one {Q : Nat → Bool} : ∀ n, (∀ a b, a < n → b < n → Q a = true → Q b = true → a = b) →
    sumTo n (fun c => indB (Q c)) ≤ 1
  | 0, _ => Nat.zero_le _
  | n + 1, h => by
    show sumTo n _ + indB (Q n) ≤ 1
    cases hq : Q n
    · rw [show indB false = 0 from rfl, Nat.add_zero]
      exact sum_le_one n (fun a b ha hb => h a b (Nat.lt_succ_of_lt ha) (Nat.lt_succ_of_lt hb))
    · have z : sumTo n (fun c => indB (Q c)) = 0 :=
        Eq.trans (sumTo_congr _ (fun c hc => by
          cases hc' : Q c
          · rfl
          · exact absurd (h c n (Nat.lt_succ_of_lt hc) (Nat.lt_succ_self n) hc' hq) (Nat.ne_of_lt hc)))
          (Eq.trans (sumTo_const 0 n) (Nat.mul_zero n))
      rw [z]; exact Nat.le_refl _

/-- **Counting through a map**: the arguments below `n` meeting `P`, sent
    injectively below `K`, are at most their images. -/
theorem count_inj {K : Nat} (P : Nat → Bool) (f : Nat → Nat) (hf : ∀ c, f c < K) (n : Nat)
    (hinj : ∀ a b, a < n → b < n → P a = true → P b = true → f a = f b → a = b) :
    sumTo n (fun c => indB (P c)) ≤
      sumTo K (fun p => indB ((List.range n).any (fun c => P c && f c == p))) := by
  have e : ∀ c, indB (P c) = sumTo K (fun p => indB (decide (p = f c)) * indB (P c)) := fun c =>
    (sumTo_point _ K (hf c)).symm
  rw [sumTo_congr _ (fun c _ => e c), sumTo_exch _ K n]
  refine sumTo_mono _ (fun p _ => ?_)
  cases hany : (List.range n).any (fun c => P c && f c == p)
  · refine Nat.le_of_eq (Eq.trans (sumTo_congr _ (fun c hc => ?_)) (Eq.trans (sumTo_const 0 n) (Nat.mul_zero n)))
    have hc' := List.any_eq_false.1 hany c (List.mem_range.2 hc)
    cases hP : P c
    · show indB (decide (p = f c)) * 0 = 0; exact Nat.mul_zero _
    · have hne : p ≠ f c := match Nat.decEq p (f c) with
        | isTrue e => absurd (by rw [hP, e, beq_iff_eq.2 rfl]; rfl) hc'
        | isFalse h => h
      rw [decide_eq_false hne]; exact Nat.zero_mul _
  · rw [show indB true = 1 from rfl]
    refine Nat.le_trans (Nat.le_of_eq (sumTo_congr _ (fun c _ => indB_and' _ _))) (sum_le_one n (fun a b ha hb h1 h2 => ?_))
    rw [Bool.and_eq_true, decide_eq_true_eq] at h1 h2
    exact hinj a b ha hb h1.2 h2.2 (h1.1.symm.trans h2.1)

section Ancestry
variable {K : Nat} (inner : Nat → Nat → Nat) (iv n1 : Nat) (xs : List Nat) (H L v : Nat)

/-- Chain `c`'s query at step `i`. -/
def stepPos (i c : Nat) : Nat := inner (chain1 K inner iv (c :: xs) H i) ((c :: xs).getD i 0)

/-- The positions at step `i` of the chains reaching `v` after `L + 1`
    absorptions. -/
def posB (i p : Nat) : Bool :=
  (List.range n1).any (fun c => decide (chain1 K inner iv (c :: xs) H (L + 1) = v) &&
    stepPos (K := K) inner iv xs H i c == p)

theorem stepPos_succ (i c : Nat) :
    stepPos (K := K) inner iv xs H (i + 1) c = inner (rget K (stepPos (K := K) inner iv xs H i c) H) (xs.getD i 0) := rfl

theorem posJ_stepPos {n1 : Nat} (i c : Nat) (hc : c < n1) :
    posJ K inner iv n1 xs H (i * n1 + c) = stepPos (K := K) inner iv xs H i c := by
  have hn : 0 < n1 := Nat.lt_of_le_of_lt (Nat.zero_le _) hc
  have e1 : (i * n1 + c) % n1 = c := by rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hc]
  have e2 : (i * n1 + c) / n1 = i := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt hc, Nat.zero_add]
  unfold posJ stepPos; rw [e1, e2]

theorem stepPos_mem {n1 : Nat} (hn1 : 0 < n1) (i c : Nat) (hc : c < n1) (hi : i ≤ L) :
    stepPos (K := K) inner iv xs H i c ∈ (runAdp K (nxtJ inner iv n1 xs) H (n1 * (L + 1))).map Prod.fst := by
  rw [runJ_eq K inner iv hn1 xs H, List.map_map]
  refine List.mem_map.2 ⟨i * n1 + c, List.mem_reverse.2 (List.mem_range.2 ?_), ?_⟩
  · calc i * n1 + c < i * n1 + n1 := Nat.add_lt_add_left hc _
      _ = (i + 1) * n1 := (Nat.succ_mul i n1).symm
      _ ≤ (L + 1) * n1 := Nat.mul_le_mul_right _ (Nat.succ_le_succ hi)
      _ = n1 * (L + 1) := Nat.mul_comm _ _
  · exact posJ_stepPos inner iv xs H i c hc

end Ancestry

section AncestryBound
variable {K : Nat} (inner : Nat → Nat → Nat) (hin : ∀ s x, inner s x < K) (κ : Nat → Nat) {Kc : Nat}
  (hκ : ∀ u, κ u < Kc) (hpk : ∀ x s s', inner s x = inner s' x → κ s = κ s') (iv : Nat) {n1 : Nat} (hn1 : 0 < n1)
  (xs : List Nat) (H L v m : Nat)

include hin in
theorem runJ_ok (y : Nat × Nat) (hy : y ∈ runAdp K (nxtJ inner iv n1 xs) H (n1 * (L + 1))) :
    y.2 = rget K y.1 H ∧ y.1 < K :=
  ⟨runAdp_ans K _ H _ y hy, runAdp_pos _ (fun l => by unfold nxtJ; split <;> exact hin _ _) H _ y hy⟩

include hin hκ hpk hn1 in
/-- **One step back through the ancestry**: on a table where every capacity
    value holds fewer than `m` of the joint run's hits, the positions at
    step `i` of the chains reaching `v` number at most `m - 1` times those
    at step `i + 1`. -/
theorem anc_step (hgood : ∀ v0, v0 < Kc →
      hitN (fib K κ v0) (runAdp K (nxtJ inner iv n1 xs) H (n1 * (L + 1))) < m)
    (i : Nat) (hi : i < L) :
    sumTo K (fun p => indB (posB (K := K) inner iv n1 xs H L v i p)) ≤
      (m - 1) * sumTo K (fun p => indB (posB (K := K) inner iv n1 xs H L v (i + 1) p)) := by
  let g := fun p => inner (rget K p H) (xs.getD i 0)
  have e : ∀ p, indB (posB (K := K) inner iv n1 xs H L v i p) =
      sumTo K (fun q => indB (decide (q = g p)) * indB (posB (K := K) inner iv n1 xs H L v i p)) := fun p =>
    (sumTo_point _ K (hin _ _)).symm
  rw [sumTo_congr _ (fun p _ => e p), sumTo_exch _ K K, sumTo_mul]
  refine sumTo_mono _ (fun q _ => ?_)
  -- a position of the ancestry at step `i` is some reaching chain's query
  have anc : ∀ p, posB (K := K) inner iv n1 xs H L v i p = true →
      ∃ c, c < n1 ∧ chain1 K inner iv (c :: xs) H (L + 1) = v ∧ stepPos (K := K) inner iv xs H i c = p := fun p h => by
    obtain ⟨c, hc, hcp⟩ := List.any_eq_true.1 h
    rw [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hcp
    exact ⟨c, List.mem_range.1 hc, hcp.1, hcp.2⟩
  cases hq : posB (K := K) inner iv n1 xs H L v (i + 1) q
  · refine Nat.le_of_eq (Eq.trans (sumTo_congr _ (fun p _ => ?_)) (Eq.trans (sumTo_const 0 K) ?_))
    · cases hp : posB (K := K) inner iv n1 xs H L v i p
      · simp [indB]
      · by_cases hqp : q = g p
        · exfalso
          obtain ⟨c, hc, hv, hcp⟩ := anc p hp
          have : posB (K := K) inner iv n1 xs H L v (i + 1) q = true :=
            List.any_eq_true.2 ⟨c, List.mem_range.2 hc, by
              rw [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, stepPos_succ, hcp]; exact ⟨hv, hqp.symm⟩⟩
          rw [hq] at this; exact Bool.false_ne_true this
        · rw [decide_eq_false hqp]; simp [indB]
    · simp [indB]
  · rw [show indB true = 1 from rfl, Nat.mul_one]
    rcases Nat.lt_or_ge (sumTo K (fun p => indB (decide (q = g p)) * indB (posB (K := K) inner iv n1 xs H L v i p))) 1
      with h0 | h1
    · exact Nat.le_trans (Nat.le_of_lt_succ h0) (Nat.zero_le _)
    obtain ⟨p0, hp0, hpos⟩ := sum_pos_exists _ K h1
    have hp0' : q = g p0 ∧ posB (K := K) inner iv n1 xs H L v i p0 = true := by
      by_cases a : q = g p0
      · cases b : posB (K := K) inner iv n1 xs H L v i p0
        · rw [b] at hpos; simp [indB] at hpos
        · exact ⟨a, rfl⟩
      · rw [decide_eq_false a] at hpos; simp [indB] at hpos
    let v0 := κ (rget K p0 H)
    have pt : ∀ p, p < K → indB (decide (q = g p)) * indB (posB (K := K) inner iv n1 xs H L v i p) ≤
        indB (decide (p ∈ (runAdp K (nxtJ inner iv n1 xs) H (n1 * (L + 1))).map Prod.fst) &&
          decide (rget K p H ∈ fib K κ v0)) := fun p hp => by
      by_cases a : q = g p
      · cases b : posB (K := K) inner iv n1 xs H L v i p
        · simp [indB]
        · obtain ⟨c, hc, _, hcp⟩ := anc p b
          have hm : p ∈ (runAdp K (nxtJ inner iv n1 xs) H (n1 * (L + 1))).map Prod.fst :=
            hcp ▸ stepPos_mem inner iv xs H L hn1 i c hc (Nat.le_of_lt hi)
          have hk : κ (rget K p H) = v0 := hpk _ _ _ (a.symm.trans hp0'.1)
          have hf : rget K p H ∈ fib K κ v0 :=
            List.mem_filter.2 ⟨List.mem_range.2 (rget_lt (Nat.lt_of_le_of_lt (Nat.zero_le _) hp) _ _), beq_iff_eq.2 hk⟩
          rw [decide_eq_true a, decide_eq_true hm, decide_eq_true hf]; exact Nat.le_refl _
      · rw [decide_eq_false a]; simp [indB]
    refine Nat.le_trans (sumTo_mono _ pt) ?_
    rw [← hitN_eq_sum (fib K κ v0) H _ (runJ_ok inner hin iv xs H L)]
    exact Nat.le_pred_of_lt (hgood v0 (hκ _))

end AncestryBound

/-- **The chains reaching `v` after `L + 1` absorptions**, on a permutation
    table where every capacity value holds fewer than `m` of the joint
    run's hits, number at most `(m - 1)^L`. -/
theorem preimage_good {K : Nat} (inner : Nat → Nat → Nat) (hin : ∀ s x, inner s x < K) (κ : Nat → Nat) {Kc : Nat}
    (hκ : ∀ u, κ u < Kc) (hpk : ∀ x s s', inner s x = inner s' x → κ s = κ s') (iv : Nat) {n1 : Nat} (hn1 : 0 < n1)
    (hd : ∀ a b, a < n1 → b < n1 → a ≠ b → inner iv a ≠ inner iv b) (xs : List Nat) {H : Nat} (hP : permB K H = true)
    (L v m : Nat) (hgood : ∀ v0, v0 < Kc →
      hitN (fib K κ v0) (runAdp K (nxtJ inner iv n1 xs) H (n1 * (L + 1))) < m) :
    sumTo n1 (fun c => indB (decide (chain1 K inner iv (c :: xs) H (L + 1) = v))) ≤ (m - 1) ^ L := by
  let N := fun i => sumTo K (fun p => indB (posB (K := K) inner iv n1 xs H L v i p))
  -- the reaching chains' first positions are distinct
  have base : sumTo n1 (fun c => indB (decide (chain1 K inner iv (c :: xs) H (L + 1) = v))) ≤ N 0 :=
    count_inj (K := K) (fun c => decide (chain1 K inner iv (c :: xs) H (L + 1) = v))
      (fun c => stepPos (K := K) inner iv xs H 0 c) (fun c => hin _ _) n1
      (fun a b ha hb _ _ e => Decidable.byContradiction (fun hne => hd a b ha hb hne e))
  -- at the last step they share one position
  have top : N L ≤ 1 := by
    refine sum_le_one K (fun p p' hp hp' h1 h2 => ?_)
    obtain ⟨c, hc, hcp⟩ := List.any_eq_true.1 h1
    obtain ⟨c', hc', hcp'⟩ := List.any_eq_true.1 h2
    rw [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hcp hcp'
    have r : rget K p H = rget K p' H := by
      rw [← hcp.2, ← hcp'.2]
      show chain1 K inner iv (c :: xs) H (L + 1) = chain1 K inner iv (c' :: xs) H (L + 1)
      rw [hcp.1, hcp'.1]
    exact permB_inj hP hp hp' r
  have down : ∀ j, j ≤ L → N (L - j) ≤ (m - 1) ^ j := by
    intro j
    induction j with
    | zero => intro _; rw [Nat.sub_zero, Nat.pow_zero]; exact top
    | succ j ih =>
      intro hj
      have hstep := anc_step inner hin κ hκ hpk iv hn1 xs H L v m hgood (L - (j + 1)) (by omega)
      have e : L - (j + 1) + 1 = L - j := by omega
      rw [e] at hstep
      calc N (L - (j + 1)) ≤ (m - 1) * N (L - j) := hstep
        _ ≤ (m - 1) * (m - 1) ^ j := Nat.mul_le_mul_left _ (ih (Nat.le_of_succ_le hj))
        _ = (m - 1) ^ (j + 1) := by rw [Nat.pow_succ, Nat.mul_comm]
  have := down L (Nat.le_refl _)
  rw [Nat.sub_self] at this
  exact Nat.le_trans base this

/-- The load bound over `L + 1` absorptions: `(m - 1)^L`, or `n1` where some
    capacity value holds `m` of the joint run's hits. -/
def loadML (K : Nat) (inner : Nat → Nat → Nat) (iv n1 : Nat) (xs : List Nat) (κ : Nat → Nat) (Kc L m H : Nat) : Nat :=
  (m - 1) ^ L + n1 * sumTo Kc (fun v0 => indB (decide (m ≤ hitN (fib K κ v0) (runAdp K (nxtJ inner iv n1 xs) H (n1 * (L + 1))))))

theorem preimage_loadML {K : Nat} (inner : Nat → Nat → Nat) (hin : ∀ s x, inner s x < K) (κ : Nat → Nat) {Kc : Nat}
    (hκ : ∀ u, κ u < Kc) (hpk : ∀ x s s', inner s x = inner s' x → κ s = κ s') (iv : Nat) {n1 : Nat} (hn1 : 0 < n1)
    (hd : ∀ a b, a < n1 → b < n1 → a ≠ b → inner iv a ≠ inner iv b) (xs : List Nat) {H : Nat} (hP : permB K H = true)
    (L v m : Nat) :
    sumTo n1 (fun c => indB (decide (chain1 K inner iv (c :: xs) H (L + 1) = v))) ≤ loadML K inner iv n1 xs κ Kc L m H := by
  unfold loadML
  rcases Nat.lt_or_ge (sumTo Kc (fun v0 => indB (decide (m ≤ hitN (fib K κ v0)
      (runAdp K (nxtJ inner iv n1 xs) H (n1 * (L + 1))))))) 1 with h0 | h1
  · have hgood : ∀ v0, v0 < Kc → hitN (fib K κ v0) (runAdp K (nxtJ inner iv n1 xs) H (n1 * (L + 1))) < m := by
      intro v0 hv0
      refine Nat.lt_of_not_le (fun hm => ?_)
      have := le_sumTo (fun v0 => indB (decide (m ≤ hitN (fib K κ v0)
        (runAdp K (nxtJ inner iv n1 xs) H (n1 * (L + 1)))))) Kc hv0
      rw [decide_eq_true hm] at this
      exact absurd (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.zero_lt_one) this) (Nat.le_of_lt_succ h0)) (Nat.lt_irrefl _)
    exact Nat.le_trans (preimage_good inner hin κ hκ hpk iv hn1 hd xs hP L v m hgood) (Nat.le_add_right _ _)
  · have h2 : sumTo n1 (fun c => indB (decide (chain1 K inner iv (c :: xs) H (L + 1) = v))) ≤ n1 :=
      Nat.le_trans (sumTo_mono _ (fun c _ => indB_le _)) (Nat.le_of_eq (by rw [sumTo_const, Nat.mul_one]))
    exact Nat.le_trans h2 (Nat.le_trans (Nat.le_mul_of_pos_right _ h1) (Nat.le_add_left _ _))

/-- The load bound for every later transcript: `(m - 1)^L`, or `n1` where,
    for some of the `X^L` lists of later blocks, some capacity value holds
    `m` of the joint run's hits. -/
def loadMA (K : Nat) (inner : Nat → Nat → Nat) (iv n1 : Nat) (κ : Nat → Nat) (Kc X L m H : Nat) : Nat :=
  (m - 1) ^ L + n1 * sumTo (X ^ L) (fun i => sumTo Kc (fun v0 => indB (decide (m ≤
    hitN (fib K κ v0) (runAdp K (nxtJ inner iv n1 (xsOf X L i)) H (n1 * (L + 1)))))))

theorem preimage_loadMA {K : Nat} (inner : Nat → Nat → Nat) (hin : ∀ s x, inner s x < K) (κ : Nat → Nat) {Kc : Nat}
    (hκ : ∀ u, κ u < Kc) (hpk : ∀ x s s', inner s x = inner s' x → κ s = κ s') (iv : Nat) {n1 : Nat} (hn1 : 0 < n1)
    (hd : ∀ a b, a < n1 → b < n1 → a ≠ b → inner iv a ≠ inner iv b) {X : Nat} (hX : 0 < X) (L : Nat) (xs : List Nat)
    (hxs : ∀ i, i < L → xs.getD i 0 < X) {H : Nat} (hP : permB K H = true) (v m : Nat) :
    sumTo n1 (fun c => indB (decide (chain1 K inner iv (c :: xs) H (L + 1) = v))) ≤ loadMA K inner iv n1 κ Kc X L m H := by
  obtain ⟨i, hi, hag⟩ := xsOf_cover hX xs hxs
  have hch : ∀ c, chain1 K inner iv (c :: xs) H (L + 1) = chain1 K inner iv (c :: xsOf X L i) H (L + 1) :=
    fun c => chain1_congr K inner iv _ _ H (L + 1) (fun j hj => by
      cases j with
      | zero => rfl
      | succ j => exact hag j (Nat.lt_of_succ_lt_succ hj))
  rw [sumTo_congr _ (fun c _ => by rw [hch c])]
  refine Nat.le_trans (preimage_loadML inner hin κ hκ hpk iv hn1 hd (xsOf X L i) hP L v m) ?_
  unfold loadML loadMA
  refine Nat.add_le_add_left (Nat.mul_le_mul_left _ ?_) _
  exact le_sumTo (fun i => sumTo Kc (fun v0 => indB (decide (m ≤
    hitN (fib K κ v0) (runAdp K (nxtJ inner iv n1 (xsOf X L i)) H (n1 * (L + 1))))))) _ hi

/-- **`SudChallenger`'s spread hypotheses at every permutation table, `L + 1`
    absorptions**: the index `φ m w` the state after the first commitment
    `m % n1` and the later blocks `enc (m / n1) w`, each below `X`; the
    table's `δs' = δs loadMA` meets `hsp1` and `hφsp` for every `d`, `rest`,
    `w` and `v` (`m ≥ 2`). -/
theorem loadA_hsp {D W : Type} {K NS1 n1 δs Kc X : Nat} (inner : Nat → Nat → Nat) (hin : ∀ s x, inner s x < K)
    (κ : Nat → Nat) (hκ : ∀ u, κ u < Kc) (hpk : ∀ x s s', inner s x = inner s' x → κ s = κ s') (iv : Nat)
    (hd : ∀ a b, a < n1 → b < n1 → a ≠ b → inner iv a ≠ inner iv b) (hX : 0 < X) (L : Nat)
    (enc : Nat → W → List Nat) (henc : ∀ r w i, i < L → (enc r w).getD i 0 < X)
    (Com1 : D → Nat → Nat) (hr1 : ∀ d σ, Com1 d σ < n1)
    (hsp1 : ∀ d v, sumTo NS1 (fun σ => indB (decide (Com1 d σ = v))) ≤ δs) {m : Nat} (hm : 2 ≤ m) {H : Nat}
    (hP : permB K H = true) :
    (∀ d v, sumTo NS1 (fun σ => indB (decide (Com1 d σ = v))) ≤ δs * loadMA K inner iv n1 κ Kc X L m H) ∧
      (∀ d rest w v, sumTo NS1 (fun σ1 => indB (decide
        ((fun m' w => chain1 K inner iv ((m' % n1) :: enc (m' / n1) w) H (L + 1)) (Com1 d σ1 + n1 * rest) w = v))) ≤
        δs * loadMA K inner iv n1 κ Kc X L m H) := by
  have h1 : 1 ≤ loadMA K inner iv n1 κ Kc X L m H :=
    Nat.le_trans (Nat.one_le_pow _ _ (Nat.le_sub_of_add_le hm)) (Nat.le_add_right _ _)
  refine ⟨fun d v => Nat.le_trans (hsp1 d v) (Nat.le_trans (Nat.le_of_eq (Nat.mul_one δs).symm)
    (Nat.mul_le_mul_left _ h1)), fun d rest w v => ?_⟩
  have hn1 : 0 < n1 := Nat.lt_of_le_of_lt (Nat.zero_le _) (hr1 d 0)
  have em : ∀ σ1, (Com1 d σ1 + n1 * rest) % n1 = Com1 d σ1 ∧ (Com1 d σ1 + n1 * rest) / n1 = rest := fun σ1 =>
    ⟨by rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (hr1 d σ1)],
     by rw [Nat.add_mul_div_left _ _ hn1, Nat.div_eq_of_lt (hr1 d σ1), Nat.zero_add]⟩
  let φ := fun c => chain1 K inner iv (c :: enc rest w) H (L + 1)
  have e : ∀ σ1, (fun m' w => chain1 K inner iv ((m' % n1) :: enc (m' / n1) w) H (L + 1)) (Com1 d σ1 + n1 * rest) w =
      φ (Com1 d σ1) := fun σ1 => by
    show chain1 K inner iv (((Com1 d σ1 + n1 * rest) % n1) :: enc ((Com1 d σ1 + n1 * rest) / n1) w) H (L + 1) = _
    rw [(em σ1).1, (em σ1).2]
  rw [sumTo_congr _ (fun σ1 _ => by rw [e σ1]), sumTo_split_pos (Com1 d) (hr1 d)]
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
  exact Nat.mul_le_mul_left _ (preimage_loadMA inner hin κ hκ hpk iv hn1 hd hX L (enc rest w) (henc rest w) hP v m)

/-- **`loadMA` averaged over a uniform permutation**: with
    `k = n1 (L + 1)` queries, `m! (K - k)^m` times the summed `loadMA` is at
    most `m! (K - k)^m (m - 1)^L + n1 X^L Kc (k F)^m` per permutation
    table. -/
theorem loadMA_countP {K F : Nat} (hK : 0 < K) (inner : Nat → Nat → Nat) (hin : ∀ s x, inner s x < K) (κ : Nat → Nat)
    (hF : ∀ v, sumTo K (fun u => indB (decide (κ u = v))) ≤ F) (iv n1 Kc X L m : Nat) :
    fact m * ((K - n1 * (L + 1)) ^ m * sumTo (K ^ K) (fun H => indB (permB K H) * loadMA K inner iv n1 κ Kc X L m H)) ≤
      (fact m * ((K - n1 * (L + 1)) ^ m * (m - 1) ^ L) + n1 * (X ^ L * (Kc * (n1 * (L + 1) * F) ^ m))) *
        sumTo (K ^ K) (fun H => indB (permB K H)) := by
  have hnx : ∀ xs l, nxtJ inner iv n1 xs l < K := fun xs l => by unfold nxtJ; split <;> exact hin _ _
  let bad := fun i v0 H => indB (permB K H && decide (m ≤ hitN (fib K κ v0)
    (runAdp K (nxtJ inner iv n1 (xsOf X L i)) H (n1 * (L + 1)))))
  have e : ∀ H, indB (permB K H) * loadMA K inner iv n1 κ Kc X L m H = indB (permB K H) * (m - 1) ^ L +
      n1 * sumTo (X ^ L) (fun i => sumTo Kc (fun v0 => bad i v0 H)) := by
    intro H
    unfold loadMA
    rw [Nat.mul_add, Nat.mul_left_comm, sumTo_mul]
    congr 2
    refine sumTo_congr _ (fun i _ => ?_)
    rw [sumTo_mul]
    exact sumTo_congr _ (fun v0 _ => indB_and' _ _)
  have tail : ∀ i v0, fact m * ((K - n1 * (L + 1)) ^ m * sumTo (K ^ K) (fun H => bad i v0 H)) ≤
      (n1 * (L + 1) * F) ^ m * sumTo (K ^ K) (fun H => indB (permB K H)) := fun i v0 =>
    hitN_tail hK (fib K κ v0) (fib_length κ hF v0) (nxtJ inner iv n1 (xsOf X L i)) (hnx _) (n1 * (L + 1)) m
  have e2 : sumTo (K ^ K) (fun H => indB (permB K H) * (m - 1) ^ L) =
      (m - 1) ^ L * sumTo (K ^ K) (fun H => indB (permB K H)) := by
    rw [sumTo_mul]; exact sumTo_congr _ (fun H _ => Nat.mul_comm _ _)
  rw [sumTo_congr _ (fun H _ => e H), sumTo_add, e2, ← sumTo_mul]
  rw [sumTo_exch (fun H i => sumTo Kc (fun v0 => bad i v0 H)) (X ^ L) (K ^ K)]
  rw [sumTo_congr (X ^ L) (fun i _ => sumTo_exch (fun H v0 => bad i v0 H) Kc (K ^ K))]
  generalize hPi : sumTo (K ^ K) (fun H => indB (permB K H)) = Pi0 at *
  have hs : fact m * ((K - n1 * (L + 1)) ^ m * sumTo (X ^ L) (fun i => sumTo Kc (fun v0 =>
      sumTo (K ^ K) (fun H => bad i v0 H)))) ≤ X ^ L * (Kc * ((n1 * (L + 1) * F) ^ m * Pi0)) := by
    rw [sumTo_mul, sumTo_mul]
    refine Nat.le_trans (sumTo_mono _ (fun i _ => ?_)) (Nat.le_of_eq (sumTo_const _ (X ^ L)))
    rw [sumTo_mul, sumTo_mul]
    exact Nat.le_trans (sumTo_mono _ (fun v0 _ => tail i v0)) (Nat.le_of_eq (sumTo_const _ Kc))
  calc fact m * ((K - n1 * (L + 1)) ^ m * ((m - 1) ^ L * Pi0 + n1 * sumTo (X ^ L) (fun i => sumTo Kc (fun v0 =>
        sumTo (K ^ K) (fun H => bad i v0 H)))))
      = fact m * ((K - n1 * (L + 1)) ^ m * (m - 1) ^ L) * Pi0 + n1 * (fact m * ((K - n1 * (L + 1)) ^ m *
        sumTo (X ^ L) (fun i => sumTo Kc (fun v0 => sumTo (K ^ K) (fun H => bad i v0 H))))) := by
        rw [Nat.mul_add, Nat.mul_add]
        congr 1
        · rw [← Nat.mul_assoc, ← Nat.mul_assoc, ← Nat.mul_assoc]
        · ac_rfl
    _ ≤ fact m * ((K - n1 * (L + 1)) ^ m * (m - 1) ^ L) * Pi0 + n1 * (X ^ L * (Kc * ((n1 * (L + 1) * F) ^ m * Pi0))) :=
        Nat.add_le_add_left (Nat.mul_le_mul_left _ hs) _
    _ = _ := by rw [Nat.add_mul]; ac_rfl

theorem loadA_δs_countP {K F : Nat} (hK : 0 < K) (inner : Nat → Nat → Nat) (hin : ∀ s x, inner s x < K) (κ : Nat → Nat)
    (hF : ∀ v, sumTo K (fun u => indB (decide (κ u = v))) ≤ F) (iv n1 Kc X L m δs : Nat) :
    fact m * (K - n1 * (L + 1)) ^ m * sumTo (K ^ K) (fun H => indB (permB K H) * (δs * loadMA K inner iv n1 κ Kc X L m H)) ≤
      δs * ((fact m * ((K - n1 * (L + 1)) ^ m * (m - 1) ^ L) + n1 * (X ^ L * (Kc * (n1 * (L + 1) * F) ^ m))) *
        sumTo (K ^ K) (fun H => indB (permB K H))) := by
  have h := loadMA_countP hK inner hin κ hF iv n1 Kc X L m
  rw [sumTo_congr _ (fun H _ => Nat.mul_left_comm _ _ _), ← sumTo_mul, Nat.mul_left_comm, Nat.mul_assoc]
  exact Nat.mul_le_mul_left _ h

/-- The fourth table's index `L + 1` absorptions after the first
    commitment, under the permutation `H`. -/
def loadφA {W : Type} (K : Nat) (inner : Nat → Nat → Nat) (iv n1 L : Nat) (enc : Nat → W → List Nat) (H : Nat) :
    Nat → Nat → W → Nat :=
  fun _ m w => chain1 K inner iv ((m % n1) :: enc (m / n1) w) H (L + 1)

/-- The spread the permutation `H` gives proof `ix`: `δ0 ix loadMA`. -/
def δsLA (K : Nat) (inner : Nat → Nat → Nat) (iv n1 : Nat) (κ : Nat → Nat) (Kc X L m : Nat) (δ0 : Nat → Nat)
    (H ix : Nat) : Nat :=
  δ0 ix * loadMA K inner iv n1 κ Kc X L m H

section
open B Air Stmt Mach Sudoku SudokuText Compose CompM Wit

set_option maxRecDepth 100000 in
/-- **`sud_interleaveS` averaged over a uniform permutation, the index
    `L + 1` absorptions after the first commitment** (`loadφA`): at each
    permutation table `P` with `δsLA P = δ0 loadMA` (`loadA_hsp`); the error
    the permutation-weighted sum of the tables' errors (`zkbT_avgW`). -/
theorem sud_interleaveLA {V Wv P1 P2 P3 W1 W2 W3 : Type} {kr kq : Nat} (φ1 : Nat → Nat → W1 → Nat) (nx1 : Nat → Nat → Nat → List Nat → Nat × Nat × W1) (G1 : Nat → Nat → Nat → List (List (List F)) → Nat → List Nat → P1) (φ2 : Nat → Nat → W2 → Nat) (nx2 : Nat → Nat → Nat → List Nat → Nat × Nat × W2) (G2 : Nat → Nat → Nat → List (List (List F)) → Nat → List Nat → P2) (φ3 : Nat → Nat → W3 → Nat) (nx3 : Nat → Nat → Nat → List Nat → Nat × Nat × W3) (G3 : Nat → Nat → Nat → List (List (List (List F))) × List (List (List F)) → Nat → List Nat → P3)
     (off : EF → String → EF) {puzzle : ∀ ix : Nat, List Nat} (hc : ∀ ix : Nat, CluesOK (cluesOf (puzzle ix))) {ρ : ∀ ix : Nat, Nat → Bool} {A : ∀ ix : Nat, List Cell} {k : ∀ ix : Nat, Nat} {row : ∀ ix : Nat, Nat → Air.Row} (hA : ∀ ix : Nat, AcceptsFrom (A ix) (stmtMachine (ρ ix) 729 (sudokuExpr (cluesOf (puzzle ix))) ACC REJ) (k ix) (row ix)) (hacc : ∀ ix : Nat, rd (A ix) ((row ix) ((k ix) - 1)).ctr ((row ix) ((k ix) - 1)).hd = some (.atom ACC)) (hlen : ∀ ix : Nat, (A ix).length = 2 ^ 16) (hk : ∀ ix : Nat, (k ix) ≤ 2 ^ 16) {tP : ∀ ix : Nat, Nat} (htp : ∀ ix : Nat, (tP ix) = progTp (stmtMachine (fun _ => false) 729 (sudokuExpr (cluesOf (puzzle ix))) ACC REJ).heap) (S16 S10 SP : ∀ ix : Nat, Nat → List F) (qv : ∀ ix : Nat, EF → EF → List EF → F → List F → List F → List EF) (wm wc ww wp : ∀ ix : Nat, Nat → List (EF → EF → List F)) {Lwm Lwc Lww Lwp : ∀ ix : Nat, Nat} (hlwm : ∀ ix : Nat, ∀ c, ((wm ix) c).length = (Lwm ix)) (hlwc : ∀ ix : Nat, ∀ c, ((wc ix) c).length = (Lwc ix)) (hlww : ∀ ix : Nat, ∀ c, ((ww ix) c).length = (Lww ix)) (hlwp : ∀ ix : Nat, ∀ c, ((wp ix) c).length = (Lwp ix)) {K2 K4 : Nat} (hK2 : 0 < K2) (hK4 : 0 < K4) (hS16 : ∀ ix : Nat, ∀ c4, ∀ x ∈ (S16 ix) c4, x ∉ cosetL 1 (bbGen 16) (2 ^ 16)) (hS10 : ∀ ix : Nat, ∀ c4, ∀ x ∈ (S10 ix) c4, x ∉ cosetL 1 (bbGen 10) (2 ^ 10)) (hSP : ∀ ix : Nat, ∀ c4, ∀ x ∈ (SP ix) c4, x ∉ cosetL 1 (bbGen ((tP ix) + 1)) (2 ^ ((tP ix) + 1))) (hsz16 : ∀ ix : Nat, ∀ c4, 2 * ((S16 ix) c4).length + 8 ≤ 2 ^ 16) (hsz : ∀ ix : Nat, ∀ c4, 2 * ((S10 ix) c4).length + 8 ≤ 2 ^ 10) (hszP : ∀ ix : Nat, ∀ c4, 2 * ((SP ix) c4).length + 8 ≤ 2 ^ ((tP ix) + 1)) {ncw : ∀ ix : Nat, Nat} (αd : ∀ ix : Nat, Nat → EF) {B4 : ∀ ix : Nat, Nat} (hB4 : ∀ ix : Nat, sumTo K4 (fun c4 => indB (!genB ((αd ix) c4))) ≤ (B4 ix)) (fri : ∀ ix : Nat, Nat → EF → EF → List (EF → EF) → V) (hncw : ∀ ix : Nat, 4 ≤ (ncw ix)) (NR2 : ∀ ix : Nat, Nat) (Rb : ∀ ix : Nat, Nat → EF → EF → Nat → List (EF → EF)) (Ro : ∀ ix : Nat, Nat → EF → EF → Nat → Wv) {n1 n2 n3 : Nat} {NS1 NS2 NS3 : ∀ ix : Nat, Nat} (Com1 : ∀ ix : Nat, List (List (List F)) → Nat → Nat) (hc1 : ∀ ix : Nat, ComHides (NS1 ix) (Com1 ix)) (hp1 : ∀ ix : Nat, ∀ c4 T1 T2 T3 T4 M, ComPfHides (NS1 ix) (Com1 ix) ((pfRdM (Q4 * Q4) K2 Q4 K4 n1 kr (φ1 ix) (nx1 ix) (G1 ix)) c4 T1 T2 T3 T4 M) (opF ((sudGroups (tP ix) ((S16 ix) c4) ((S10 ix) c4) ((SP ix) c4) EF.zero (qv ix)).map (·.base.S)) [0, 2, 4, 6])) (hr1 : ∀ ix : Nat, ∀ d σ, (Com1 ix) d σ < n1) (d1 : ∀ ix : Nat, List (List (List F))) (Com2 : ∀ ix : Nat, List (List (List F)) → Nat → Nat) (hc2 : ∀ ix : Nat, ComHides (NS2 ix) (Com2 ix)) (hp2 : ∀ ix : Nat, ∀ c4 T1 T2 T3 T4 M, ComPfHides (NS2 ix) (Com2 ix) ((pfRdM (Q4 * Q4) K2 Q4 K4 n1 kr (φ2 ix) (nx2 ix) (G2 ix)) c4 T1 T2 T3 T4 M) (opF ((sudGroups (tP ix) ((S16 ix) c4) ((S10 ix) c4) ((SP ix) c4) EF.zero (qv ix)).map (·.base.S)) [1, 3, 5, 7])) (hr2 : ∀ ix : Nat, ∀ d σ, (Com2 ix) d σ < n2) (d2 : ∀ ix : Nat, List (List (List F))) (Com3 : ∀ ix : Nat, List (List (List (List F))) × List (List (List F)) → Nat → Nat) (hc3 : ∀ ix : Nat, ComHides (NS3 ix) (Com3 ix)) (hp3 : ∀ ix : Nat, ∀ c4 T1 T2 T3 T4 M, ComPfHides (NS3 ix) (Com3 ix) ((pfRdM (Q4 * Q4) K2 Q4 K4 n1 kr (φ3 ix) (nx3 ix) (G3 ix)) c4 T1 T2 T3 T4 M) (fun d => (opQ (sudSsT ((S16 ix) c4) ((S10 ix) c4) ((SP ix) c4)) d.1, opCw (sudSsC (tP ix) ((S16 ix) c4) ((S10 ix) c4) ((SP ix) c4)) d.2))) (hr3 : ∀ ix : Nat, ∀ d σ, (Com3 ix) d σ < n3) (d3 : ∀ ix : Nat, List (List (List (List F))) × List (List (List F)))
    {Kp : Nat} (hKp : 0 < Kp) (inner : Nat → Nat → Nat) (hin : ∀ s x, inner s x < Kp) (κ : Nat → Nat) {Kc : Nat}
    (hκ : ∀ u, κ u < Kc) (hpk : ∀ x s s', inner s x = inner s' x → κ s = κ s') (iv : Nat)
    (hd : ∀ a b, a < n1 → b < n1 → a ≠ b → inner iv a ≠ inner iv b)
    {X : Nat} (hX : 0 < X) (L : Nat) (enc : Nat → Option (List (List (List EF)) × List (List (List (List EF))) × List (List (List EF))) → List Nat) (henc : ∀ r w i, i < L → (enc r w).getD i 0 < X) (δ0 : Nat → Nat)
    (hsp1 : ∀ ix d v, sumTo (NS1 ix) (fun σ => indB (decide (Com1 ix d σ = v))) ≤ δ0 ix) {m : Nat} (hm : 2 ≤ m)
    (isQ : Nat → Bool) (nxtQ : Nat → List Nat → Nat × Nat × Unit) :
    ∀ n, ZKBT (fun (f : Nat × (Nat × Nat × Nat × Nat) → Nat) => sumTo (Kp ^ Kp) (fun P => indB (permB Kp P) *
        (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo (K4 ^ Kp) (fun H4 => sumTo ((Q4 * Q4) ^ n1) (fun H1 => sumTo (K2 ^ (n1 * n2)) (fun H2 => sumTo (Q4 ^ (n1 * (n2 * n3))) (fun H3 => f (H1, H2, H3, H4)))))) (fun H => f (P, H))))
      (KPowD (fun _ => (K4 * (Q4 * Q4 * (K2 * Q4)))) n)
      (smPowD (X := fun _ => Nat × Nat × Nat × (Nat → Tup)) (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc 0) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).sm 2) n)
      (scPowD (C := fun _ => Nat × Nat × Nat × Nat) (fun _ => (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo K4 (fun c4 => sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo Q4 (fun c3 => f (c1, c2, c3, c4))))))) n)
      (fun PH x => (rvPowD (mixRv (Q4 * Q4) K2 Q4 K4 kq isQ nxtQ
        (fun i => read4T (Q4 * Q4) K2 Q4 K4 ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc PH.1) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).m1 ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc PH.1) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).m2 ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc PH.1) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).m3 ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc PH.1) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).q ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc PH.1) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).out)) n) PH.2 x)
      (fun PH c x => (PH.1, (pgPowD (pgRd (Q4 * Q4) K2 Q4 K4 (fun i => !isQ i) (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc PH.1) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).pts) (fun _ c => c)) n) PH.2 c x))
      (fun PH c x => (svPowDT (pgRd (Q4 * Q4) K2 Q4 K4 (fun i => !isQ i) (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc PH.1) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).pts) (fun _ c => c))
        (mixSv (Q4 * Q4) K2 Q4 K4 kq isQ nxtQ (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc PH.1) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).sv)) n) PH.2 c x)
      (sumTo (Kp ^ Kp) (fun P => indB (permB Kp P) * (errPowD (fun _ => (K4 * (Q4 * Q4 * (K2 * Q4)))) (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).sm 2) (fun _ => (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo K4 (fun c4 => sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo Q4 (fun c3 => f (c1, c2, c3, c4))))))) (fun i => cond (isQ i) 0 ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).ε)
        (fun n => (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo K4 (fun c4 => sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo Q4 (fun c3 => f (c1, c2, c3, c4)))))) (fun _ => (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo (K4 ^ Kp) (fun H4 => sumTo ((Q4 * Q4) ^ n1) (fun H1 => sumTo (K2 ^ (n1 * n2)) (fun H2 => sumTo (Q4 ^ (n1 * (n2 * n3))) (fun H3 => f (H1, H2, H3, H4)))))) (fun _ => smPowD (X := fun _ => Nat × Nat × Nat × (Nat → Tup)) (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).sm 2) n
          (fun _ => rSum (fun i => cond (isQ i) kq (4 + 3 * kr)) n *
            cond (isQ n) 0 (((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) n).NS * (((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) n).NR * (Q4 ^ 2 * δsLA Kp inner iv n1 κ Kc X L m δ0 P n))))))) n))) := by
  intro n
  exact zkbT_avgW (fun P => indB (permB Kp P)) (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo (K4 ^ Kp) (fun H4 => sumTo ((Q4 * Q4) ^ n1) (fun H1 => sumTo (K2 ^ (n1 * n2)) (fun H2 => sumTo (Q4 ^ (n1 * (n2 * n3))) (fun H3 => f (H1, H2, H3, H4)))))) (smPowD (X := fun _ => Nat × Nat × Nat × (Nat → Tup)) (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc 0) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).sm 2) n) (scPowD (C := fun _ => Nat × Nat × Nat × Nat) (fun _ => (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo K4 (fun c4 => sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo Q4 (fun c3 => f (c1, c2, c3, c4))))))) n)
    (fun P => (rvPowD (mixRv (Q4 * Q4) K2 Q4 K4 kq isQ nxtQ
        (fun i => read4T (Q4 * Q4) K2 Q4 K4 ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).m1 ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).m2 ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).m3 ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).q ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).out)) n)) (fun P => (pgPowD (pgRd (Q4 * Q4) K2 Q4 K4 (fun i => !isQ i) (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).pts) (fun _ c => c)) n)) (fun P => (svPowDT (pgRd (Q4 * Q4) K2 Q4 K4 (fun i => !isQ i) (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).pts) (fun _ c => c))
        (mixSv (Q4 * Q4) K2 Q4 K4 kq isQ nxtQ (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).sv)) n))
    (fun P => (errPowD (fun _ => (K4 * (Q4 * Q4 * (K2 * Q4)))) (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).sm 2) (fun _ => (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo K4 (fun c4 => sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo Q4 (fun c3 => f (c1, c2, c3, c4))))))) (fun i => cond (isQ i) 0 ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).ε)
        (fun n => (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo K4 (fun c4 => sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo Q4 (fun c3 => f (c1, c2, c3, c4)))))) (fun _ => (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo (K4 ^ Kp) (fun H4 => sumTo ((Q4 * Q4) ^ n1) (fun H1 => sumTo (K2 ^ (n1 * n2)) (fun H2 => sumTo (Q4 ^ (n1 * (n2 * n3))) (fun H3 => f (H1, H2, H3, H4)))))) (fun _ => smPowD (X := fun _ => Nat × Nat × Nat × (Nat → Tup)) (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).sm 2) n
          (fun _ => rSum (fun i => cond (isQ i) kq (4 + 3 * kr)) n *
            cond (isQ n) 0 (((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) n).NS * (((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) n).NR * (Q4 ^ 2 * δsLA Kp inner iv n1 κ Kc X L m δ0 P n))))))) n)) (fun P _ hw =>
    sud_interleaveS φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3 off hc hA hacc hlen hk htp S16 S10 SP qv wm wc ww wp hlwm hlwc hlww hlwp
      hK2 hK4 (loadφA Kp inner iv n1 L enc P) (fun _ _ _ => rget_lt hKp _ _) hS16 hS10 hSP hsz16 hsz hszP αd hB4 fri hncw NR2 Rb Ro
      Com1 hc1 hp1 hr1 d1 Com2 hc2 hp2 hr2 d2 Com3 hc3 hp3 hr3 d3 (δsLA Kp inner iv n1 κ Kc X L m δ0 P)
      (fun ix => (loadA_hsp inner hin κ hκ hpk iv hd hX L enc henc (Com1 ix) (hr1 ix) (hsp1 ix) hm (permB_of_indB hw)).1)
      (fun ix => (loadA_hsp inner hin κ hκ hpk iv hd hX L enc henc (Com1 ix) (hr1 ix) (hsp1 ix) hm (permB_of_indB hw)).2) isQ nxtQ n)


set_option maxHeartbeats 1600000 in
set_option maxRecDepth 100000 in
/-- **`sud_interleaveLA` with a number for its error**:
    `Kq = m! (Kp - n1 (L+1))^m` times the averaged real count is at most `Kq`
    times the averaged simulation plus `errPowD` at the errors `Kq W ε` and
    each spread `δ0 i (m! (Kp - n1 (L+1))^m (m - 1)^L + n1 X^L Kc
    (n1 (L+1) F)^m) W`, `W` the number of permutation tables
    (`avg_err_bound`, `loadA_δs_countP`). -/
theorem sud_interleaveLAN {V Wv P1 P2 P3 W1 W2 W3 : Type} {kr kq : Nat} (φ1 : Nat → Nat → W1 → Nat) (nx1 : Nat → Nat → Nat → List Nat → Nat × Nat × W1) (G1 : Nat → Nat → Nat → List (List (List F)) → Nat → List Nat → P1) (φ2 : Nat → Nat → W2 → Nat) (nx2 : Nat → Nat → Nat → List Nat → Nat × Nat × W2) (G2 : Nat → Nat → Nat → List (List (List F)) → Nat → List Nat → P2) (φ3 : Nat → Nat → W3 → Nat) (nx3 : Nat → Nat → Nat → List Nat → Nat × Nat × W3) (G3 : Nat → Nat → Nat → List (List (List (List F))) × List (List (List F)) → Nat → List Nat → P3)
     (off : EF → String → EF) {puzzle : ∀ ix : Nat, List Nat} (hc : ∀ ix : Nat, CluesOK (cluesOf (puzzle ix))) {ρ : ∀ ix : Nat, Nat → Bool} {A : ∀ ix : Nat, List Cell} {k : ∀ ix : Nat, Nat} {row : ∀ ix : Nat, Nat → Air.Row} (hA : ∀ ix : Nat, AcceptsFrom (A ix) (stmtMachine (ρ ix) 729 (sudokuExpr (cluesOf (puzzle ix))) ACC REJ) (k ix) (row ix)) (hacc : ∀ ix : Nat, rd (A ix) ((row ix) ((k ix) - 1)).ctr ((row ix) ((k ix) - 1)).hd = some (.atom ACC)) (hlen : ∀ ix : Nat, (A ix).length = 2 ^ 16) (hk : ∀ ix : Nat, (k ix) ≤ 2 ^ 16) {tP : ∀ ix : Nat, Nat} (htp : ∀ ix : Nat, (tP ix) = progTp (stmtMachine (fun _ => false) 729 (sudokuExpr (cluesOf (puzzle ix))) ACC REJ).heap) (S16 S10 SP : ∀ ix : Nat, Nat → List F) (qv : ∀ ix : Nat, EF → EF → List EF → F → List F → List F → List EF) (wm wc ww wp : ∀ ix : Nat, Nat → List (EF → EF → List F)) {Lwm Lwc Lww Lwp : ∀ ix : Nat, Nat} (hlwm : ∀ ix : Nat, ∀ c, ((wm ix) c).length = (Lwm ix)) (hlwc : ∀ ix : Nat, ∀ c, ((wc ix) c).length = (Lwc ix)) (hlww : ∀ ix : Nat, ∀ c, ((ww ix) c).length = (Lww ix)) (hlwp : ∀ ix : Nat, ∀ c, ((wp ix) c).length = (Lwp ix)) {K2 K4 : Nat} (hK2 : 0 < K2) (hK4 : 0 < K4) (hS16 : ∀ ix : Nat, ∀ c4, ∀ x ∈ (S16 ix) c4, x ∉ cosetL 1 (bbGen 16) (2 ^ 16)) (hS10 : ∀ ix : Nat, ∀ c4, ∀ x ∈ (S10 ix) c4, x ∉ cosetL 1 (bbGen 10) (2 ^ 10)) (hSP : ∀ ix : Nat, ∀ c4, ∀ x ∈ (SP ix) c4, x ∉ cosetL 1 (bbGen ((tP ix) + 1)) (2 ^ ((tP ix) + 1))) (hsz16 : ∀ ix : Nat, ∀ c4, 2 * ((S16 ix) c4).length + 8 ≤ 2 ^ 16) (hsz : ∀ ix : Nat, ∀ c4, 2 * ((S10 ix) c4).length + 8 ≤ 2 ^ 10) (hszP : ∀ ix : Nat, ∀ c4, 2 * ((SP ix) c4).length + 8 ≤ 2 ^ ((tP ix) + 1)) {ncw : ∀ ix : Nat, Nat} (αd : ∀ ix : Nat, Nat → EF) {B4 : ∀ ix : Nat, Nat} (hB4 : ∀ ix : Nat, sumTo K4 (fun c4 => indB (!genB ((αd ix) c4))) ≤ (B4 ix)) (fri : ∀ ix : Nat, Nat → EF → EF → List (EF → EF) → V) (hncw : ∀ ix : Nat, 4 ≤ (ncw ix)) (NR2 : ∀ ix : Nat, Nat) (Rb : ∀ ix : Nat, Nat → EF → EF → Nat → List (EF → EF)) (Ro : ∀ ix : Nat, Nat → EF → EF → Nat → Wv) {n1 n2 n3 : Nat} {NS1 NS2 NS3 : ∀ ix : Nat, Nat} (Com1 : ∀ ix : Nat, List (List (List F)) → Nat → Nat) (hc1 : ∀ ix : Nat, ComHides (NS1 ix) (Com1 ix)) (hp1 : ∀ ix : Nat, ∀ c4 T1 T2 T3 T4 M, ComPfHides (NS1 ix) (Com1 ix) ((pfRdM (Q4 * Q4) K2 Q4 K4 n1 kr (φ1 ix) (nx1 ix) (G1 ix)) c4 T1 T2 T3 T4 M) (opF ((sudGroups (tP ix) ((S16 ix) c4) ((S10 ix) c4) ((SP ix) c4) EF.zero (qv ix)).map (·.base.S)) [0, 2, 4, 6])) (hr1 : ∀ ix : Nat, ∀ d σ, (Com1 ix) d σ < n1) (d1 : ∀ ix : Nat, List (List (List F))) (Com2 : ∀ ix : Nat, List (List (List F)) → Nat → Nat) (hc2 : ∀ ix : Nat, ComHides (NS2 ix) (Com2 ix)) (hp2 : ∀ ix : Nat, ∀ c4 T1 T2 T3 T4 M, ComPfHides (NS2 ix) (Com2 ix) ((pfRdM (Q4 * Q4) K2 Q4 K4 n1 kr (φ2 ix) (nx2 ix) (G2 ix)) c4 T1 T2 T3 T4 M) (opF ((sudGroups (tP ix) ((S16 ix) c4) ((S10 ix) c4) ((SP ix) c4) EF.zero (qv ix)).map (·.base.S)) [1, 3, 5, 7])) (hr2 : ∀ ix : Nat, ∀ d σ, (Com2 ix) d σ < n2) (d2 : ∀ ix : Nat, List (List (List F))) (Com3 : ∀ ix : Nat, List (List (List (List F))) × List (List (List F)) → Nat → Nat) (hc3 : ∀ ix : Nat, ComHides (NS3 ix) (Com3 ix)) (hp3 : ∀ ix : Nat, ∀ c4 T1 T2 T3 T4 M, ComPfHides (NS3 ix) (Com3 ix) ((pfRdM (Q4 * Q4) K2 Q4 K4 n1 kr (φ3 ix) (nx3 ix) (G3 ix)) c4 T1 T2 T3 T4 M) (fun d => (opQ (sudSsT ((S16 ix) c4) ((S10 ix) c4) ((SP ix) c4)) d.1, opCw (sudSsC (tP ix) ((S16 ix) c4) ((S10 ix) c4) ((SP ix) c4)) d.2))) (hr3 : ∀ ix : Nat, ∀ d σ, (Com3 ix) d σ < n3) (d3 : ∀ ix : Nat, List (List (List (List F))) × List (List (List F)))
    {Kp : Nat} (hKp : 0 < Kp) (inner : Nat → Nat → Nat) (hin : ∀ s x, inner s x < Kp) (κ : Nat → Nat) {Kc : Nat}
    (hκ : ∀ u, κ u < Kc) (hpk : ∀ x s s', inner s x = inner s' x → κ s = κ s') (iv : Nat)
    (hd : ∀ a b, a < n1 → b < n1 → a ≠ b → inner iv a ≠ inner iv b)
    {X : Nat} (hX : 0 < X) (L : Nat) (enc : Nat → Option (List (List (List EF)) × List (List (List (List EF))) × List (List (List EF))) → List Nat) (henc : ∀ r w i, i < L → (enc r w).getD i 0 < X) (δ0 : Nat → Nat) {F : Nat} (hF : ∀ v, sumTo Kp (fun u => indB (decide (κ u = v))) ≤ F)
    (hsp1 : ∀ ix d v, sumTo (NS1 ix) (fun σ => indB (decide (Com1 ix d σ = v))) ≤ δ0 ix) {m : Nat} (hm : 2 ≤ m)
    (isQ : Nat → Bool) (nxtQ : Nat → List Nat → Nat × Nat × Unit) :
    ∀ n (E : Nat × (Nat × Nat × Nat × Nat) → _ → Bool),
      (fact m * (Kp - n1 * (L + 1)) ^ m) * ((KPowD (fun _ => (K4 * (Q4 * Q4 * (K2 * Q4)))) n) * (fun (f : Nat × (Nat × Nat × Nat × Nat) → Nat) => sumTo (Kp ^ Kp) (fun P => indB (permB Kp P) * (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo (K4 ^ Kp) (fun H4 => sumTo ((Q4 * Q4) ^ n1) (fun H1 => sumTo (K2 ^ (n1 * n2)) (fun H2 => sumTo (Q4 ^ (n1 * (n2 * n3))) (fun H3 => f (H1, H2, H3, H4)))))) (fun H => f (P, H)))) (fun H => (smPowD (X := fun _ => Nat × Nat × Nat × (Nat → Tup)) (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc 0) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).sm 2) n) (fun x => indB (E H ((fun PH x => (rvPowD (mixRv (Q4 * Q4) K2 Q4 K4 kq isQ nxtQ
        (fun i => read4T (Q4 * Q4) K2 Q4 K4 ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc PH.1) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).m1 ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc PH.1) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).m2 ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc PH.1) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).m3 ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc PH.1) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).q ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc PH.1) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).out)) n) PH.2 x) H x))))) ≤
        (fact m * (Kp - n1 * (L + 1)) ^ m) * (fun (f : Nat × (Nat × Nat × Nat × Nat) → Nat) => sumTo (Kp ^ Kp) (fun P => indB (permB Kp P) * (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo (K4 ^ Kp) (fun H4 => sumTo ((Q4 * Q4) ^ n1) (fun H1 => sumTo (K2 ^ (n1 * n2)) (fun H2 => sumTo (Q4 ^ (n1 * (n2 * n3))) (fun H3 => f (H1, H2, H3, H4)))))) (fun H => f (P, H)))) (fun H => (scPowD (C := fun _ => Nat × Nat × Nat × Nat) (fun _ => (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo K4 (fun c4 => sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo Q4 (fun c3 => f (c1, c2, c3, c4))))))) n) (fun c => (smPowD (X := fun _ => Nat × Nat × Nat × (Nat → Tup)) (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc 0) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).sm 2) n) (fun x => indB (E ((fun PH c x => (PH.1, (pgPowD (pgRd (Q4 * Q4) K2 Q4 K4 (fun i => !isQ i) (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc PH.1) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).pts) (fun _ c => c)) n) PH.2 c x)) H c x) ((fun PH c x => (svPowDT (pgRd (Q4 * Q4) K2 Q4 K4 (fun i => !isQ i) (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc PH.1) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).pts) (fun _ c => c))
        (mixSv (Q4 * Q4) K2 Q4 K4 kq isQ nxtQ (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc PH.1) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).sv)) n) PH.2 c x) H c x))))) +
        errPowD (fun _ => (K4 * (Q4 * Q4 * (K2 * Q4)))) (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc 0) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).sm 2) (fun _ => (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo K4 (fun c4 => sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo Q4 (fun c3 => f (c1, c2, c3, c4))))))) (fun i => (fact m * (Kp - n1 * (L + 1)) ^ m) * (sumTo (Kp ^ Kp) (fun P => indB (permB Kp P))) * (fun i => cond (isQ i) 0 ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc 0) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).ε) i) (fun i => (fun n x => (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo K4 (fun c4 => sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo Q4 (fun c3 => f (c1, c2, c3, c4)))))) (fun _ => (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo (K4 ^ Kp) (fun H4 => sumTo ((Q4 * Q4) ^ n1) (fun H1 => sumTo (K2 ^ (n1 * n2)) (fun H2 => sumTo (Q4 ^ (n1 * (n2 * n3))) (fun H3 => f (H1, H2, H3, H4)))))) (fun _ => smPowD (X := fun _ => Nat × Nat × Nat × (Nat → Tup)) (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc 0) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).sm 2) n
          (fun _ => rSum (fun i => cond (isQ i) kq (4 + 3 * kr)) n *
            cond (isQ n) 0 (((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc 0) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) n).NS * (((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc 0) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) n).NR * (Q4 ^ 2 * x))))))) i ((fun i => δ0 i * ((fact m * ((Kp - n1 * (L + 1)) ^ m * (m - 1) ^ L) + n1 * (X ^ L * (Kc * (n1 * (L + 1) * F) ^ m))) * (sumTo (Kp ^ Kp) (fun P => indB (permB Kp P))))) i)) n := by
  intro n E
  have h := sud_interleaveLA (kq := kq) φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3 off hc hA hacc hlen hk htp S16 S10 SP qv wm wc ww wp hlwm hlwc hlww hlwp hK2 hK4 hS16 hS10 hSP hsz16 hsz hszP αd hB4 fri hncw NR2 Rb Ro Com1 hc1 hp1 hr1 d1 Com2 hc2 hp2 hr2 d2 Com3 hc3 hp3 hr3 d3 hKp inner hin κ hκ hpk iv hd hX L enc henc δ0 hsp1 hm isQ nxtQ n
  have hb := (avg_err_bound (fun _ => (K4 * (Q4 * Q4 * (K2 * Q4)))) (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc 0) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).sm 2) (fun _ => (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo K4 (fun c4 => sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo Q4 (fun c3 => f (c1, c2, c3, c4))))))) (fun i => cond (isQ i) 0 ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc 0) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).ε) (Kp ^ Kp) (fun P => indB (permB Kp P))
      (fun P i => δsLA Kp inner iv n1 κ Kc X L m δ0 P i) (fun n x => (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo K4 (fun c4 => sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo Q4 (fun c3 => f (c1, c2, c3, c4)))))) (fun _ => (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo (K4 ^ Kp) (fun H4 => sumTo ((Q4 * Q4) ^ n1) (fun H1 => sumTo (K2 ^ (n1 * n2)) (fun H2 => sumTo (Q4 ^ (n1 * (n2 * n3))) (fun H3 => f (H1, H2, H3, H4)))))) (fun _ => smPowD (X := fun _ => Nat × Nat × Nat × (Nat → Tup)) (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc 0) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).sm 2) n
          (fun _ => rSum (fun i => cond (isQ i) kq (4 + 3 * kr)) n *
            cond (isQ n) 0 (((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc 0) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) n).NS * (((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc 0) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) n).NR * (Q4 ^ 2 * x)))))))
      (fun i x => wrap_scale (lin_sum4 _ _ _ _) (lin_sum4 _ _ _ _) (lin_smPowD (fun _ => lin_sm _ _ _ _) i) _ _ _ _ _ x)
      (fact m * (Kp - n1 * (L + 1)) ^ m) (fun i => δ0 i * ((fact m * ((Kp - n1 * (L + 1)) ^ m * (m - 1) ^ L) + n1 * (X ^ L * (Kc * (n1 * (L + 1) * F) ^ m))) * (sumTo (Kp ^ Kp) (fun P => indB (permB Kp P))))) (fun i => loadA_δs_countP hKp inner hin κ hF iv n1 Kc X L m (δ0 i)) n)
  exact zkbT_err_le h _ _ hb E

end

end Circuit
