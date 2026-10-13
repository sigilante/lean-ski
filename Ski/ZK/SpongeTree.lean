import Ski.ZK.SpongeLoadL

/-!
# Chains that all meet saw near-collisions

`SpongeLoadL` bounds an index's preimage by `(m - 1)^L` over `L` later
blocks, exponential in `L`.  Here a tuple argument gives a bound
polynomial in `L`, for domain-separated absorptions.

- **Chains that all meet saw near-collisions.** `t` chains from distinct
  first positions, whose positions never repeat across steps (`hsep`), and
  which all reach one state, make at least `t - 1` fresh answers equal under
  `κ` to an earlier one in their own joint run (`allMeet_near`): step by
  step, a block's distinct positions are at most its distinct projections
  plus its near-collisions (`block_count`), and the projections at most the
  next step's positions (`hpk`).  So, averaged over a uniform permutation,
  they all meet on at most `((0 + ⋯ + (L t - 1)) F)^(t-1) / ((t-1)!
  (K - L t)^(t-1))` of the tables (`allMeet_countP`, through `nearN_tail`).
- **Tuples.** An index reached by `s` first commitments gives
  `s (s-1) ⋯ (s-t+1)` injective meeting `t`-tuples (`ffac_le`,
  `ffac_preimage`), so by Markov the preimage is below `s0` except on
  tables where the meeting tuples (`meetM`) reach `s0 (s0-1) ⋯ (s0-t+1)`
  (`loadT`, `preimage_loadT`, `meetM_countP`, `loadT_countP`).
- **Tags.** Domain separation is a tag on positions fixed by the block
  (`hτ`): first commitments tag `0`, the later block `m` tag `m + 1`
  (`sep_of_tags`).  A union over the tagged later block lists gives
  `loadTA` for every tagged later transcript (`preimage_loadTA`,
  `loadTA_hsp`), averaged in `loadTA_countP`.  `tag_satPT` meets `hτ` and
  `h0` at the full-width instance, the tag the block's range; `htag` stays a
  condition on the encoding, met by later blocks in `[(m+1) Y, (m+2) Y)`
  with `(L + 1) Y ≤ R1`.
- **The composite.** `sud_interleaveS` with this index, averaged over the
  permutation, with a number for its error (`sud_interleaveLT`,
  `sud_interleaveLTN`).

Size.  The tags take room in the rate: first commitments below `Y`, so
`n1 ≤ R1 / (L + 1)`.  The bound grows with `n1`, so `n1 = Kc = X = 2^248`
with `n1 F / K` near `1` overstates it; there, optimizing `t` and `s0`
makes `E[loadTA]` about `2^11`, `2^15`, `2^20`, `2^29` for
`L = 1, 3, 10, 100`, growing as `L^3`; `SpongeLoadL`'s bound is about
`2^7`, `2^24` at `L = 1, 3` and exponential beyond.

Limits.  The later blocks must carry step tags, which Plonky3's
challenger does not add, and the tags shrink the first commitment's space
below the rate.  The composites say nothing unless `Kp > L t` and
`s0 ≥ t`. the other limits are `SpongeLoad`'s: the state
before the first commitment is fixed, the first commitment fills one aligned
block, `H4` stays independent of the permutation, and the later blocks do
not depend on the salt.
-/

set_option autoImplicit false

namespace Circuit
open ZKF

/-- The joint run of `n1` chains with first blocks `cf j`, step-major. -/
def nxtS (inner : Nat → Nat → Nat) (iv n1 : Nat) (cf : Nat → Nat) (xs : List Nat) (l : List Nat) : Nat :=
  if l.length < n1 then inner iv (cf l.length) else inner (l.getD (n1 - 1) 0) (xs.getD (l.length / n1 - 1) 0)

/-- Query `t`'s position: chain `t % n1` at step `t / n1`. -/
def posS (K : Nat) (inner : Nat → Nat → Nat) (iv n1 : Nat) (cf : Nat → Nat) (xs : List Nat) (H t : Nat) : Nat :=
  inner (chain1 K inner iv (cf (t % n1) :: xs) H (t / n1)) ((cf (t % n1) :: xs).getD (t / n1) 0)

theorem rget_posS (K : Nat) (inner : Nat → Nat → Nat) (iv n1 : Nat) (cf : Nat → Nat) (xs : List Nat) (H t : Nat) :
    rget K (posS K inner iv n1 cf xs H t) H = chain1 K inner iv (cf (t % n1) :: xs) H (t / n1 + 1) := rfl

/-- **The joint run is the chains' queries in order.** -/
theorem runS_eq (K : Nat) (inner : Nat → Nat → Nat) (iv : Nat) {n1 : Nat} (hn1 : 0 < n1) (cf : Nat → Nat) (xs : List Nat) (H : Nat) :
    ∀ ℓ, runAdp K (nxtS inner iv n1 cf xs) H ℓ =
      (List.range ℓ).reverse.map (fun t => (posS K inner iv n1 cf xs H t, rget K (posS K inner iv n1 cf xs H t) H))
  | 0 => rfl
  | ℓ + 1 => by
    have ih := runS_eq K inner iv hn1 cf xs H ℓ
    show (nxtS inner iv n1 cf xs ((runAdp K (nxtS inner iv n1 cf xs) H ℓ).map Prod.snd), _) :: runAdp K (nxtS inner iv n1 cf xs) H ℓ = _
    rw [List.range_succ, List.reverse_append, List.map_append, ih]
    have hp : nxtS inner iv n1 cf xs ((((List.range ℓ).reverse.map (fun t => (posS K inner iv n1 cf xs H t,
        rget K (posS K inner iv n1 cf xs H t) H))).map Prod.snd)) = posS K inner iv n1 cf xs H ℓ := by
      unfold nxtS
      rw [List.length_map, List.length_map, List.length_reverse, List.length_range]
      by_cases hl : ℓ < n1
      · rw [if_pos hl]
        unfold posS
        rw [Nat.mod_eq_of_lt hl, Nat.div_eq_of_lt hl]; rfl
      · rw [if_neg hl]
        have hge : n1 ≤ ℓ := Nat.le_of_not_lt hl
        have hidx : n1 - 1 < ℓ := by omega
        rw [List.map_map, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_reverse (by
          rw [List.length_range]; exact hidx), List.getElem?_range (by rw [List.length_range]; omega)]
        rw [List.length_range]
        show inner (rget K (posS K inner iv n1 cf xs H (ℓ - 1 - (n1 - 1))) H) (xs.getD (ℓ / n1 - 1) 0) = _
        have e1 : ℓ - 1 - (n1 - 1) = ℓ - n1 := by omega
        rw [e1, rget_posS]
        have hq : ℓ / n1 = (ℓ - n1) / n1 + 1 := by
          rw [← Nat.sub_add_cancel hge, Nat.add_div_right _ hn1, Nat.sub_add_cancel hge]
        have hr : (ℓ - n1) % n1 = ℓ % n1 := by
          conv => rhs; rw [← Nat.sub_add_cancel hge]
          rw [Nat.add_mod_right]
        unfold posS
        rw [hr, hq]
        rfl
    rw [hp]; rfl


/-- Adding one element `x < n` to a set counts it once if it is new. -/
theorem sumTo_or (f : Nat → Bool) {x n : Nat} (hx : x < n) :
    sumTo n (fun p => indB ((x == p) || f p)) = sumTo n (fun p => indB (f p)) + indB (!f x) := by
  have pt : ∀ p, indB ((x == p) || f p) = indB (f p) + indB (decide (p = x)) * indB (!f x) := fun p => by
    by_cases e : p = x
    · rw [e, beq_iff_eq.2 rfl, decide_eq_true rfl]; cases f x <;> rfl
    · have hb : (x == p) = false := by
        cases h : (x == p)
        · rfl
        · exact absurd (beq_iff_eq.1 h).symm e
      rw [hb, decide_eq_false e, Bool.false_or]; simp [indB]
  rw [sumTo_congr _ (fun p _ => pt p), sumTo_add, sumTo_point _ n hx]

/-- The positions of a list of queries. -/
def posIn (B : List (Nat × Nat)) (p : Nat) : Bool := B.any (fun e => e.1 == p)

/-- The projections of a list of queries' answers. -/
def clIn (κ : Nat → Nat) (B : List (Nat × Nat)) (v0 : Nat) : Bool := B.any (fun e => κ e.2 == v0)

theorem posIn_cons (e : Nat × Nat) (B : List (Nat × Nat)) (p : Nat) : posIn (e :: B) p = ((e.1 == p) || posIn B p) := by
  unfold posIn; rw [List.any_cons]

theorem clIn_cons (κ : Nat → Nat) (e : Nat × Nat) (B : List (Nat × Nat)) (v0 : Nat) :
    clIn κ (e :: B) v0 = ((κ e.2 == v0) || clIn κ B v0) := by
  unfold clIn; rw [List.any_cons]

theorem posIn_iff (B : List (Nat × Nat)) (p : Nat) : posIn B p = true ↔ p ∈ B.map Prod.fst := by
  unfold posIn
  rw [List.any_eq_true, List.mem_map]
  exact ⟨fun ⟨e, he, h⟩ => ⟨e, he, beq_iff_eq.1 h⟩, fun ⟨e, he, h⟩ => ⟨e, he, beq_iff_eq.2 h⟩⟩

/-- **A block's new positions are its new projections plus its
    near-collisions**: queries `Bn` (newest first) after a history `G`, no
    position of `Bn` in `G`; their distinct positions are at most their
    distinct projections under `κ` plus the fresh answers near an earlier
    one they add (`nearN`, near meaning equal under `κ`). -/
theorem block_count {K Kc : Nat} (κ : Nat → Nat) (hκ : ∀ u, κ u < Kc) (G : List (Nat × Nat)) :
    ∀ Bn : List (Nat × Nat), (∀ e ∈ Bn, e.1 < K ∧ e.2 < K ∧ e.1 ∉ G.map Prod.fst) →
      sumTo K (fun p => indB (posIn Bn p)) + nearN K (fun a b => decide (κ a = κ b)) G ≤
        sumTo Kc (fun v0 => indB (clIn κ Bn v0)) + nearN K (fun a b => decide (κ a = κ b)) (Bn ++ G)
  | [], _ => by
    have z : ∀ n (f : Nat → Bool), (∀ x, f x = false) → sumTo n (fun x => indB (f x)) = 0 := fun n f hf =>
      Eq.trans (sumTo_congr _ (fun x _ => by rw [hf x]; rfl)) (Eq.trans (sumTo_const 0 n) (Nat.mul_zero n))
    rw [z K (posIn []) (fun _ => rfl), z Kc (clIn κ []) (fun _ => rfl), List.nil_append]; exact Nat.le_refl _
  | e :: Bn, h => by
    have he := h e List.mem_cons_self
    have ih := block_count κ hκ G Bn (fun x hx => h x (List.mem_cons_of_mem _ hx))
    have e1 : sumTo K (fun p => indB (posIn (e :: Bn) p)) = sumTo K (fun p => indB (posIn Bn p)) + indB (!posIn Bn e.1) := by
      rw [← sumTo_or (posIn Bn) he.1]; exact sumTo_congr _ (fun p _ => by rw [posIn_cons])
    have e2 : sumTo Kc (fun v0 => indB (clIn κ (e :: Bn) v0)) =
        sumTo Kc (fun v0 => indB (clIn κ Bn v0)) + indB (!clIn κ Bn (κ e.2)) := by
      rw [← sumTo_or (clIn κ Bn) (hκ e.2)]; exact sumTo_congr _ (fun v0 _ => by rw [clIn_cons])
    rw [e1, e2]
    show _ ≤ _ + (nearN K _ (Bn ++ G) + indB (!decide (e.1 ∈ (Bn ++ G).map Prod.fst) &&
      decide (e.2 ∈ nearR K (fun a b => decide (κ a = κ b)) ((Bn ++ G).map Prod.snd))))
    cases hp : posIn Bn e.1
    · -- a new position: fresh in the whole run
      have hf : e.1 ∉ (Bn ++ G).map Prod.fst := by
        rw [List.map_append, List.mem_append, not_or]
        exact ⟨fun hm => by rw [(posIn_iff Bn e.1).2 hm] at hp; exact Bool.noConfusion hp, he.2.2⟩
      rw [decide_eq_false hf, Bool.not_false, Bool.true_and]
      cases hc : clIn κ Bn (κ e.2)
      · -- a new projection
        show _ + indB true + _ ≤ _ + indB true + _
        have := Nat.add_le_add_right ih 1
        omega
      · -- an old projection: the answer is near an earlier one
        obtain ⟨e', he', hk⟩ := List.any_eq_true.1 hc
        have hn : e.2 ∈ nearR K (fun a b => decide (κ a = κ b)) ((Bn ++ G).map Prod.snd) := by
          unfold nearR
          refine List.mem_filter.2 ⟨List.mem_range.2 he.2.1, List.any_eq_true.2 ⟨e'.2, ?_, ?_⟩⟩
          · exact List.mem_map.2 ⟨e', List.mem_append.2 (Or.inl he'), rfl⟩
          · exact decide_eq_true (beq_iff_eq.1 hk)
        rw [decide_eq_true hn]
        show _ + indB true + _ ≤ _ + indB false + (_ + indB true)
        have : indB true = 1 := rfl
        have : indB false = 0 := rfl
        omega
    · show _ + indB false + _ ≤ _ + _ + (_ + _)
      have : indB false = 0 := rfl
      have := Nat.zero_le (indB (!clIn κ Bn (κ e.2)))
      have := Nat.zero_le (indB (!decide (e.1 ∈ (Bn ++ G).map Prod.fst) &&
        decide (e.2 ∈ nearR K (fun a b => decide (κ a = κ b)) ((Bn ++ G).map Prod.snd))))
      omega

/-- Step `i`'s queries, newest first. -/
def blockS (K : Nat) (inner : Nat → Nat → Nat) (iv n1 : Nat) (cf : Nat → Nat) (xs : List Nat) (H i : Nat) :
    List (Nat × Nat) :=
  (List.range n1).reverse.map (fun j => (posS K inner iv n1 cf xs H (i * n1 + j),
    rget K (posS K inner iv n1 cf xs H (i * n1 + j)) H))

theorem runS_block (K : Nat) (inner : Nat → Nat → Nat) (iv : Nat) {n1 : Nat} (hn1 : 0 < n1) (cf : Nat → Nat)
    (xs : List Nat) (H i : Nat) :
    runAdp K (nxtS inner iv n1 cf xs) H ((i + 1) * n1) =
      blockS K inner iv n1 cf xs H i ++ runAdp K (nxtS inner iv n1 cf xs) H (i * n1) := by
  rw [runS_eq K inner iv hn1 cf xs H, runS_eq K inner iv hn1 cf xs H, Nat.succ_mul, List.range_add,
    List.reverse_append, List.map_append]
  unfold blockS
  rw [← List.map_reverse, List.map_map]
  rfl

theorem posIn_blockS (K : Nat) (inner : Nat → Nat → Nat) (iv n1 : Nat) (cf : Nat → Nat) (xs : List Nat) (H i p : Nat) :
    posIn (blockS K inner iv n1 cf xs H i) p = true ↔ ∃ j, j < n1 ∧ posS K inner iv n1 cf xs H (i * n1 + j) = p := by
  rw [posIn_iff]
  unfold blockS
  rw [List.map_map, List.mem_map]
  exact ⟨fun ⟨j, hj, e⟩ => ⟨j, List.mem_range.1 (List.mem_reverse.1 hj), e⟩,
    fun ⟨j, hj, e⟩ => ⟨j, List.mem_reverse.2 (List.mem_range.2 hj), e⟩⟩

theorem posS_step (K : Nat) (inner : Nat → Nat → Nat) (iv : Nat) {n1 : Nat} (hn1 : 0 < n1) (cf : Nat → Nat)
    (xs : List Nat) (H i j : Nat) (hj : j < n1) :
    posS K inner iv n1 cf xs H (i * n1 + j) = inner (chain1 K inner iv (cf j :: xs) H i) ((cf j :: xs).getD i 0) := by
  have e1 : (i * n1 + j) % n1 = j := by rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]
  have e2 : (i * n1 + j) / n1 = i := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hn1, Nat.div_eq_of_lt hj, Nat.zero_add]
  unfold posS; rw [e1, e2]

theorem posS_next (K : Nat) (inner : Nat → Nat → Nat) (iv : Nat) {n1 : Nat} (hn1 : 0 < n1) (cf : Nat → Nat)
    (xs : List Nat) (H i j : Nat) (hj : j < n1) :
    posS K inner iv n1 cf xs H ((i + 1) * n1 + j) = inner (rget K (posS K inner iv n1 cf xs H (i * n1 + j)) H) (xs.getD i 0) := by
  rw [posS_step K inner iv hn1 cf xs H (i + 1) j hj, posS_step K inner iv hn1 cf xs H i j hj]; rfl

/-- **Chains that all meet saw near-collisions**: `n1` chains from distinct
    first positions (`hd`), positions never repeating across steps
    (`hsep`, a domain-separated absorption), all reaching one state after
    `L + 1` absorptions on a permutation table; then their joint run over
    the first `L` steps has at least `n1 - 1` fresh answers equal under `κ`
    to an earlier one. -/
theorem allMeet_near {K Kc : Nat} (inner : Nat → Nat → Nat) (hin : ∀ s x, inner s x < K) (κ : Nat → Nat)
    (hκ : ∀ u, κ u < Kc) (hpk : ∀ x s s', inner s x = inner s' x → κ s = κ s') (iv : Nat) {n1 : Nat} (hn1 : 0 < n1)
    (cf : Nat → Nat) (hd : ∀ a b, a < n1 → b < n1 → a ≠ b → inner iv (cf a) ≠ inner iv (cf b)) (xs : List Nat)
    {H : Nat} (hP : permB K H = true) (L : Nat)
    (hsep : ∀ i i' j j', i' < i → i ≤ L → j < n1 → j' < n1 →
      posS K inner iv n1 cf xs H (i * n1 + j) ≠ posS K inner iv n1 cf xs H (i' * n1 + j'))
    {v : Nat} (hall : ∀ j, j < n1 → chain1 K inner iv (cf j :: xs) H (L + 1) = v) :
    n1 ≤ 1 + nearN K (fun a b => decide (κ a = κ b)) (runAdp K (nxtS inner iv n1 cf xs) H (L * n1)) := by
  have hK : 0 < K := Nat.lt_of_le_of_lt (Nat.zero_le _) (hin 0 0)
  let cl := fun a b => decide (κ a = κ b)
  let N := fun i => sumTo K (fun p => indB (posIn (blockS K inner iv n1 cf xs H i) p))
  let run := fun i => runAdp K (nxtS inner iv n1 cf xs) H (i * n1)
  -- the projections of step i's answers are at most step i+1's positions
  have clN : ∀ i, sumTo Kc (fun v0 => indB (clIn κ (blockS K inner iv n1 cf xs H i) v0)) ≤ N (i + 1) := by
    intro i
    let R := fun q v0 => (List.range n1).any (fun j => κ (rget K (posS K inner iv n1 cf xs H (i * n1 + j)) H) == v0 &&
      posS K inner iv n1 cf xs H ((i + 1) * n1 + j) == q)
    have one : ∀ v0, indB (clIn κ (blockS K inner iv n1 cf xs H i) v0) ≤
        sumTo K (fun q => indB (posIn (blockS K inner iv n1 cf xs H (i + 1)) q && R q v0)) := by
      intro v0
      cases hc : clIn κ (blockS K inner iv n1 cf xs H i) v0
      · exact Nat.zero_le _
      · obtain ⟨e, he, hk⟩ := List.any_eq_true.1 hc
        unfold blockS at he
        rw [List.mem_map] at he
        obtain ⟨j, hj, rfl⟩ := he
        have hj' : j < n1 := List.mem_range.1 (List.mem_reverse.1 hj)
        have hq0 : posS K inner iv n1 cf xs H ((i + 1) * n1 + j) < K := hin _ _
        have h1 : posIn (blockS K inner iv n1 cf xs H (i + 1)) (posS K inner iv n1 cf xs H ((i + 1) * n1 + j)) = true :=
          (posIn_blockS K inner iv n1 cf xs H (i + 1) _).2 ⟨j, hj', rfl⟩
        have h2 : R (posS K inner iv n1 cf xs H ((i + 1) * n1 + j)) v0 = true := List.any_eq_true.2 ⟨j, List.mem_range.2 hj', by
          rw [Bool.and_eq_true]; exact ⟨hk, beq_iff_eq.2 rfl⟩⟩
        have key : indB (posIn (blockS K inner iv n1 cf xs H (i + 1)) (posS K inner iv n1 cf xs H ((i + 1) * n1 + j)) &&
            R (posS K inner iv n1 cf xs H ((i + 1) * n1 + j)) v0) = 1 := by rw [h1, h2]; rfl
        exact Nat.le_trans (Nat.le_of_eq key.symm)
          (le_sumTo (fun q => indB (posIn (blockS K inner iv n1 cf xs H (i + 1)) q && R q v0)) K hq0)
    refine Nat.le_trans (sumTo_mono _ (fun v0 _ => one v0)) ?_
    rw [sumTo_exch _ K Kc]
    refine sumTo_mono _ (fun q _ => ?_)
    cases hq : posIn (blockS K inner iv n1 cf xs H (i + 1)) q
    · exact Nat.le_of_eq (Eq.trans (sumTo_congr _ (fun v0 _ => rfl)) (Eq.trans (sumTo_const 0 Kc) (Nat.mul_zero Kc)))
    · refine Nat.le_trans (Nat.le_of_eq (sumTo_congr _ (fun v0 _ => by rw [Bool.true_and]))) (sum_le_one Kc ?_)
      intro v0 v1 _ _ h0 h1
      obtain ⟨j0, hj0, e0⟩ := List.any_eq_true.1 h0
      obtain ⟨j1, hj1, e1⟩ := List.any_eq_true.1 h1
      rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at e0 e1
      rw [posS_next K inner iv hn1 cf xs H i j0 (List.mem_range.1 hj0)] at e0
      rw [posS_next K inner iv hn1 cf xs H i j1 (List.mem_range.1 hj1)] at e1
      rw [← e0.1, ← e1.1]
      exact hpk _ _ _ (e0.2.trans e1.2.symm)
  -- one step: block i adds at most its near-collisions
  have step : ∀ i, i < L → N i + nearN K cl (run i) ≤ N (i + 1) + nearN K cl (run (i + 1)) := by
    intro i hi
    have hb := block_count (K := K) κ hκ (run i) (blockS K inner iv n1 cf xs H i) (fun e he => by
      unfold blockS at he
      rw [List.mem_map] at he
      obtain ⟨j, hj, rfl⟩ := he
      have hj' : j < n1 := List.mem_range.1 (List.mem_reverse.1 hj)
      refine ⟨hin _ _, rget_lt hK _ _, fun hm => ?_⟩
      show False
      have hm' : posS K inner iv n1 cf xs H (i * n1 + j) ∈ ((List.range (i * n1)).reverse.map (fun t =>
          (posS K inner iv n1 cf xs H t, rget K (posS K inner iv n1 cf xs H t) H))).map Prod.fst := by
        rw [← runS_eq K inner iv hn1 cf xs H]; exact hm
      rw [List.map_map, List.mem_map] at hm'
      obtain ⟨t, ht, et⟩ := hm'
      have ht' : t < i * n1 := List.mem_range.1 (List.mem_reverse.1 ht)
      have hdt : t = (t / n1) * n1 + t % n1 := by rw [Nat.mul_comm]; exact (Nat.div_add_mod t n1).symm
      have hi' : t / n1 < i := (Nat.div_lt_iff_lt_mul hn1).2 ht'
      exact hsep i (t / n1) j (t % n1) hi' (Nat.le_of_lt hi) hj' (Nat.mod_lt _ hn1) (by rw [← hdt]; exact et.symm))
    rw [← runS_block K inner iv hn1 cf xs H i] at hb
    exact Nat.le_trans hb (Nat.add_le_add_right (clN i) _)
  have tele : ∀ i, i ≤ L → N 0 ≤ N i + nearN K cl (run i) := by
    intro i
    induction i with
    | zero => intro _; show N 0 ≤ N 0 + nearN K cl (runAdp K (nxtS inner iv n1 cf xs) H (0 * n1)); rw [Nat.zero_mul]
              exact Nat.le_add_right _ _
    | succ i ih => intro hi; exact Nat.le_trans (ih (Nat.le_of_succ_le hi)) (step i (Nat.lt_of_succ_le hi))
  -- the first positions are distinct
  have base : n1 ≤ N 0 := by
    have hc := count_inj (K := K) (fun _ => true) (fun j => posS K inner iv n1 cf xs H (0 * n1 + j)) (fun _ => hin _ _) n1
      (fun a b ha hb _ _ e => Decidable.byContradiction (fun hne => hd a b ha hb hne (by
        rw [posS_step K inner iv hn1 cf xs H 0 a ha, posS_step K inner iv hn1 cf xs H 0 b hb] at e; exact e)))
    refine Nat.le_trans (Nat.le_of_eq ?_) (Nat.le_trans hc (sumTo_mono _ (fun p _ => ?_)))
    · exact (Eq.trans (sumTo_congr _ (fun _ _ => rfl)) (Eq.trans (sumTo_const 1 n1) (Nat.mul_one n1))).symm
    · cases h : (List.range n1).any (fun c => true && posS K inner iv n1 cf xs H (0 * n1 + c) == p)
      · exact Nat.zero_le _
      · obtain ⟨j, hj, hjp⟩ := List.any_eq_true.1 h
        rw [Bool.true_and, beq_iff_eq] at hjp
        rw [(posIn_blockS K inner iv n1 cf xs H 0 p).2 ⟨j, List.mem_range.1 hj, hjp⟩]; exact Nat.le_refl _
  -- the last positions coincide
  have top : N L ≤ 1 := by
    refine sum_le_one K (fun p p' hp hp' h1 h2 => ?_)
    obtain ⟨j, hj, e⟩ := (posIn_blockS K inner iv n1 cf xs H L p).1 h1
    obtain ⟨j', hj', e'⟩ := (posIn_blockS K inner iv n1 cf xs H L p').1 h2
    refine permB_inj hP hp hp' ?_
    rw [← e, ← e', rget_posS, rget_posS]
    have a1 : (L * n1 + j) % n1 = j := by rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]
    have a2 : (L * n1 + j) / n1 = L := by rw [Nat.add_comm, Nat.add_mul_div_right _ _ hn1, Nat.div_eq_of_lt hj, Nat.zero_add]
    have b1 : (L * n1 + j') % n1 = j' := by rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj']
    have b2 : (L * n1 + j') / n1 = L := by rw [Nat.add_comm, Nat.add_mul_div_right _ _ hn1, Nat.div_eq_of_lt hj', Nat.zero_add]
    rw [a1, a2, b1, b2, hall j hj, hall j' hj']
  have := tele L (Nat.le_refl _)
  calc n1 ≤ N 0 := base
    _ ≤ N L + nearN K cl (run L) := this
    _ ≤ 1 + nearN K cl (run L) := Nat.add_le_add_right top _

/-- **Chains that all meet are rare**: over the permutation tables, `n1`
    chains from distinct first positions, positions never repeating across
    steps at any table, all reach one state after `L + 1` absorptions on at
    most `((0 + ⋯ + (L n1 - 1)) F)^(n1-1) / ((n1-1)! (K - L n1)^(n1-1))` of
    them (`allMeet_near`, `nearN_tail`). -/
theorem allMeet_countP {K Kc F : Nat} (hK : 0 < K) (inner : Nat → Nat → Nat) (hin : ∀ s x, inner s x < K) (κ : Nat → Nat)
    (hκ : ∀ u, κ u < Kc) (hF : ∀ v, sumTo K (fun u => indB (decide (κ u = v))) ≤ F)
    (hpk : ∀ x s s', inner s x = inner s' x → κ s = κ s') (iv : Nat) {n1 : Nat} (hn1 : 0 < n1)
    (cf : Nat → Nat) (hd : ∀ a b, a < n1 → b < n1 → a ≠ b → inner iv (cf a) ≠ inner iv (cf b)) (xs : List Nat) (L : Nat)
    (hsep : ∀ H, ∀ i i' j j', i' < i → i ≤ L → j < n1 → j' < n1 →
      posS K inner iv n1 cf xs H (i * n1 + j) ≠ posS K inner iv n1 cf xs H (i' * n1 + j')) :
    fact (n1 - 1) * ((K - L * n1) ^ (n1 - 1) * sumTo (K ^ K) (fun H => indB (permB K H &&
        (List.range n1).all (fun j => chain1 K inner iv (cf j :: xs) H (L + 1) == chain1 K inner iv (cf 0 :: xs) H (L + 1))))) ≤
      (sumTo (L * n1) (fun j => j) * F) ^ (n1 - 1) * sumTo (K ^ K) (fun H => indB (permB K H)) := by
  have hnx : ∀ l, nxtS inner iv n1 cf xs l < K := fun l => by unfold nxtS; split <;> exact hin _ _
  refine Nat.le_trans (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (sumTo_mono _ (fun H _ => ?_))))
    (nearN_tail hK (fun a b => decide (κ a = κ b)) (rel_symm κ) (fib_rel κ hF) (nxtS inner iv n1 cf xs) hnx (L * n1) (n1 - 1))
  cases hP : permB K H
  · exact Nat.zero_le _
  cases ha : (List.range n1).all (fun j => chain1 K inner iv (cf j :: xs) H (L + 1) == chain1 K inner iv (cf 0 :: xs) H (L + 1))
  · exact Nat.zero_le _
  · have hall : ∀ j, j < n1 → chain1 K inner iv (cf j :: xs) H (L + 1) = chain1 K inner iv (cf 0 :: xs) H (L + 1) :=
      fun j hj => beq_iff_eq.1 (List.all_eq_true.1 ha j (List.mem_range.2 hj))
    have hm := allMeet_near inner hin κ hκ hpk iv hn1 cf hd xs hP L (hsep H) hall
    have : n1 - 1 ≤ nearN K (fun a b => decide (κ a = κ b)) (runAdp K (nxtS inner iv n1 cf xs) H (L * n1)) := by omega
    rw [decide_eq_true this]; exact Nat.le_refl _

/-! ### Injective tuples of chains -/

/-- The falling factorial `s (s - 1) ⋯ (s - t + 1)`. -/
def ffac (s : Nat) : Nat → Nat
  | 0 => 1
  | t + 1 => ffac s t * (s - t)

/-- The tuple `a < n1^t` has distinct digits. -/
def injT (n1 : Nat) : Nat → Nat → Bool
  | 0, _ => true
  | t + 1, a => injT n1 t (a / n1) && !(List.range t).any (fun j => rget n1 j (a / n1) == a % n1)

/-- Every digit of `a` meets `S`. -/
def allT (n1 : Nat) (S : Nat → Bool) : Nat → Nat → Bool
  | 0, _ => true
  | t + 1, a => S (a % n1) && allT n1 S t (a / n1)

theorem rget_split {n1 r q : Nat} (hr : r < n1) (j : Nat) :
    rget n1 0 (r + n1 * q) = r ∧ rget n1 (j + 1) (r + n1 * q) = rget n1 j q := by
  have hn : 0 < n1 := Nat.lt_of_le_of_lt (Nat.zero_le _) hr
  refine ⟨?_, ?_⟩
  · rw [rget_zero', Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr]
  · rw [rget_succ', Nat.add_mul_div_left _ _ hn, Nat.div_eq_of_lt hr, Nat.zero_add]

theorem split_mod_div {n1 r q : Nat} (hr : r < n1) : (r + n1 * q) % n1 = r ∧ (r + n1 * q) / n1 = q := by
  have hn : 0 < n1 := Nat.lt_of_le_of_lt (Nat.zero_le _) hr
  exact ⟨by rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr],
    by rw [Nat.add_mul_div_left _ _ hn, Nat.div_eq_of_lt hr, Nat.zero_add]⟩

/-- **Distinct digits differ.** -/
theorem injT_ne {n1 : Nat} (hn : 0 < n1) : ∀ t a, injT n1 t a = true → ∀ i j, i < t → j < t → i ≠ j →
    rget n1 i a ≠ rget n1 j a
  | 0, _, _, i, _, hi, _, _ => absurd hi (Nat.not_lt_zero _)
  | t + 1, a, h, i, j, hi, hj, hij => by
    have h' : injT n1 t (a / n1) = true ∧ (List.range t).any (fun j => rget n1 j (a / n1) == a % n1) = false := by
      have := h; unfold injT at this
      rw [Bool.and_eq_true, Bool.not_eq_true'] at this; exact this
    have hr : ∀ k, rget n1 (k + 1) a = rget n1 k (a / n1) := fun k => rget_succ' n1 k a
    have h0 : rget n1 0 a = a % n1 := rget_zero' n1 a
    have notin : ∀ k, k < t → rget n1 k (a / n1) ≠ a % n1 := fun k hk e => by
      have := List.any_eq_false.1 h'.2 k (List.mem_range.2 hk)
      exact this (beq_iff_eq.2 e)
    cases i with
    | zero =>
      cases j with
      | zero => exact absurd rfl hij
      | succ j => rw [h0, hr]; exact fun e => notin j (Nat.lt_of_succ_lt_succ hj) e.symm
    | succ i =>
      cases j with
      | zero => rw [h0, hr]; exact notin i (Nat.lt_of_succ_lt_succ hi)
      | succ j =>
        rw [hr, hr]
        exact injT_ne hn t (a / n1) h'.1 i j (Nat.lt_of_succ_lt_succ hi) (Nat.lt_of_succ_lt_succ hj)
          (fun e => hij (by rw [e]))

theorem allT_mem {n1 : Nat} (S : Nat → Bool) : ∀ t a, allT n1 S t a = true → ∀ j, j < t → S (rget n1 j a) = true
  | 0, _, _, _, hj => absurd hj (Nat.not_lt_zero _)
  | t + 1, a, h, j, hj => by
    have h' : S (a % n1) = true ∧ allT n1 S t (a / n1) = true := by
      have := h; unfold allT at this; rw [Bool.and_eq_true] at this; exact this
    cases j with
    | zero => rw [rget_zero']; exact h'.1
    | succ j => rw [rget_succ']; exact allT_mem S t (a / n1) h'.2 j (Nat.lt_of_succ_lt_succ hj)

theorem rget_lt_n {n1 : Nat} (hn : 0 < n1) (j a : Nat) : rget n1 j a < n1 := rget_lt hn j a

/-- **A set of `s` values below `n1` holds at least `s (s-1) ⋯ (s-t+1)`
    tuples of `t` distinct values.** -/
theorem ffac_le {n1 : Nat} (hn : 0 < n1) (S : Nat → Bool) :
    ∀ t, ffac (sumTo n1 (fun c => indB (S c))) t ≤ sumTo (n1 ^ t) (fun a => indB (injT n1 t a && allT n1 S t a))
  | 0 => by show 1 ≤ sumTo 1 _; show 1 ≤ 0 + indB (true && true); exact Nat.le_refl _
  | t + 1 => by
    have ih := ffac_le hn S t
    let s := sumTo n1 (fun c => indB (S c))
    rw [Nat.pow_succ, Nat.mul_comm, sumTo_split n1 _ (n1 ^ t)]
    -- each injective tuple in `S` extends by the `s - t` values of `S` it misses
    have each : ∀ q, (s - t) * indB (injT n1 t q && allT n1 S t q) ≤
        sumTo n1 (fun r => indB (injT n1 (t + 1) (r + n1 * q) && allT n1 S (t + 1) (r + n1 * q))) := by
      intro q
      cases hq : (injT n1 t q && allT n1 S t q)
      · rw [show indB false = 0 from rfl, Nat.mul_zero]; exact Nat.zero_le _
      · rw [show indB true = 1 from rfl, Nat.mul_one]
        rw [Bool.and_eq_true] at hq
        let D := (List.range t).map (fun j => rget n1 j q)
        have hcount : s ≤ sumTo n1 (fun r => indB (S r && !decide (r ∈ D))) + t := by
          have pt : ∀ r, indB (S r) ≤ indB (S r && !decide (r ∈ D)) + indB (decide (r ∈ D)) := fun r => by
            cases S r <;> cases decide (r ∈ D) <;> simp [indB]
          refine Nat.le_trans (sumTo_mono _ (fun r _ => pt r)) ?_
          rw [sumTo_add]
          refine Nat.add_le_add_left (Nat.le_trans (count_mem n1 D) ?_) _
          rw [List.length_map, List.length_range]; exact Nat.le_refl _
        refine Nat.le_trans (Nat.sub_le_of_le_add hcount) (sumTo_mono _ (fun r hr => ?_))
        have e1 := split_mod_div (q := q) hr
        cases hS : S r
        · simp [indB]
        cases hD : decide (r ∈ D)
        · have hnot : (List.range t).any (fun j => rget n1 j q == r) = false := by
            cases h : (List.range t).any (fun j => rget n1 j q == r)
            · rfl
            · exfalso
              obtain ⟨j, hj, e⟩ := List.any_eq_true.1 h
              have : r ∈ D := List.mem_map.2 ⟨j, hj, beq_iff_eq.1 e⟩
              rw [decide_eq_true this] at hD; exact Bool.noConfusion hD
          have i1 : injT n1 (t + 1) (r + n1 * q) = true := by
            show (injT n1 t ((r + n1 * q) / n1) && !(List.range t).any (fun j => rget n1 j ((r + n1 * q) / n1) == (r + n1 * q) % n1)) = true
            rw [e1.1, e1.2, hq.1, hnot]; rfl
          have a1 : allT n1 S (t + 1) (r + n1 * q) = true := by
            show (S ((r + n1 * q) % n1) && allT n1 S t ((r + n1 * q) / n1)) = true
            rw [e1.1, e1.2, hS, hq.2]; rfl
          rw [i1, a1]; exact Nat.le_refl _
        · simp [indB]
    show ffac s t * (s - t) ≤ _
    calc ffac s t * (s - t) = (s - t) * ffac s t := Nat.mul_comm _ _
      _ ≤ (s - t) * sumTo (n1 ^ t) (fun a => indB (injT n1 t a && allT n1 S t a)) := Nat.mul_le_mul_left _ ih
      _ = sumTo (n1 ^ t) (fun q => (s - t) * indB (injT n1 t q && allT n1 S t q)) := sumTo_mul _ _ _
      _ ≤ _ := sumTo_mono _ (fun q _ => each q)

theorem ffac_mono {s s' : Nat} (h : s ≤ s') : ∀ t, ffac s t ≤ ffac s' t
  | 0 => Nat.le_refl _
  | t + 1 => Nat.mul_le_mul (ffac_mono h t) (Nat.sub_le_sub_right h t)

/-! ### The preimage through tuples that all meet -/

/-- The injective `t`-tuples of first commitments below `n1` whose chains
    all meet after `L + 1` absorptions. -/
def meetM (K : Nat) (inner : Nat → Nat → Nat) (iv n1 : Nat) (xs : List Nat) (L t H : Nat) : Nat :=
  sumTo (n1 ^ t) (fun a => indB (injT n1 t a && (List.range t).all (fun j =>
    chain1 K inner iv (rget n1 j a :: xs) H (L + 1) == chain1 K inner iv (rget n1 0 a :: xs) H (L + 1))))

/-- **At every table, an index's preimage `s` gives `s (s-1) ⋯ (s-t+1)` meeting
    tuples.** -/
theorem ffac_preimage (K : Nat) (inner : Nat → Nat → Nat) (iv : Nat) {n1 : Nat} (hn : 0 < n1) (xs : List Nat)
    (L t H v : Nat) :
    ffac (sumTo n1 (fun c => indB (decide (chain1 K inner iv (c :: xs) H (L + 1) = v)))) t ≤
      meetM K inner iv n1 xs L t H := by
  refine Nat.le_trans (ffac_le hn (fun c => decide (chain1 K inner iv (c :: xs) H (L + 1) = v)) t)
    (sumTo_mono _ (fun a _ => ?_))
  cases hi : injT n1 t a
  · exact Nat.zero_le _
  cases ha : allT n1 (fun c => decide (chain1 K inner iv (c :: xs) H (L + 1) = v)) t a
  · exact Nat.zero_le _
  · have hm := allT_mem _ t a ha
    have hall : (List.range t).all (fun j =>
        chain1 K inner iv (rget n1 j a :: xs) H (L + 1) == chain1 K inner iv (rget n1 0 a :: xs) H (L + 1)) = true := by
      refine List.all_eq_true.2 (fun j hj => beq_iff_eq.2 ?_)
      have hj' := List.mem_range.1 hj
      have h0 : 0 < t := Nat.lt_of_le_of_lt (Nat.zero_le _) hj'
      rw [of_decide_eq_true (hm j hj'), of_decide_eq_true (hm 0 h0)]
    rw [hall]; exact Nat.le_refl _

/-- The load bound through `t`-tuples: `s0 - 1`, or `n1` where the meeting
    tuples reach `s0 (s0-1) ⋯ (s0-t+1)`. -/
def loadT (K : Nat) (inner : Nat → Nat → Nat) (iv n1 : Nat) (xs : List Nat) (L t s0 H : Nat) : Nat :=
  (s0 - 1) + n1 * indB (decide (ffac s0 t ≤ meetM K inner iv n1 xs L t H))

theorem preimage_loadT (K : Nat) (inner : Nat → Nat → Nat) (iv : Nat) {n1 : Nat} (hn : 0 < n1) (xs : List Nat)
    (L t s0 H v : Nat) :
    sumTo n1 (fun c => indB (decide (chain1 K inner iv (c :: xs) H (L + 1) = v))) ≤ loadT K inner iv n1 xs L t s0 H := by
  unfold loadT
  by_cases hb : ffac s0 t ≤ meetM K inner iv n1 xs L t H
  · rw [decide_eq_true hb, show indB true = 1 from rfl, Nat.mul_one]
    exact Nat.le_trans (Nat.le_trans (sumTo_mono _ (fun c _ => indB_le _)) (Nat.le_of_eq (by rw [sumTo_const, Nat.mul_one])))
      (Nat.le_add_left _ _)
  · rw [decide_eq_false hb, show indB false = 0 from rfl, Nat.mul_zero, Nat.add_zero]
    refine Nat.le_pred_of_lt (Nat.lt_of_not_le (fun hs => hb ?_))
    exact Nat.le_trans (ffac_mono hs t) (ffac_preimage K inner iv hn xs L t H v)

/-- **Meeting tuples averaged over a uniform permutation**: with
    domain-separated absorptions (`hsepC`), `(t-1)! (K - L t)^(t-1)` times
    the summed `meetM` is at most `n1^t ((0 + ⋯ + (L t - 1)) F)^(t-1)` per
    permutation table. -/
theorem meetM_countP {K Kc F : Nat} (hK : 0 < K) (inner : Nat → Nat → Nat) (hin : ∀ s x, inner s x < K) (κ : Nat → Nat)
    (hκ : ∀ u, κ u < Kc) (hF : ∀ v, sumTo K (fun u => indB (decide (κ u = v))) ≤ F)
    (hpk : ∀ x s s', inner s x = inner s' x → κ s = κ s') (iv : Nat) {n1 : Nat} (hn : 0 < n1)
    (hd : ∀ a b, a < n1 → b < n1 → a ≠ b → inner iv a ≠ inner iv b) (xs : List Nat) (L : Nat)
    (hsepC : ∀ H c c' i i', c < n1 → c' < n1 → i' < i → i ≤ L →
      inner (chain1 K inner iv (c :: xs) H i) ((c :: xs).getD i 0) ≠ inner (chain1 K inner iv (c' :: xs) H i') ((c' :: xs).getD i' 0))
    {t : Nat} (ht : 0 < t) :
    fact (t - 1) * ((K - L * t) ^ (t - 1) * sumTo (K ^ K) (fun H => indB (permB K H) * meetM K inner iv n1 xs L t H)) ≤
      n1 ^ t * ((sumTo (L * t) (fun j => j) * F) ^ (t - 1) * sumTo (K ^ K) (fun H => indB (permB K H))) := by
  have e : sumTo (K ^ K) (fun H => indB (permB K H) * meetM K inner iv n1 xs L t H) =
      sumTo (n1 ^ t) (fun a => sumTo (K ^ K) (fun H => indB (permB K H) * indB (injT n1 t a &&
        (List.range t).all (fun j => chain1 K inner iv (rget n1 j a :: xs) H (L + 1) ==
          chain1 K inner iv (rget n1 0 a :: xs) H (L + 1))))) := by
    unfold meetM
    rw [sumTo_congr _ (fun H _ => sumTo_mul _ _ _)]
    exact sumTo_exch _ (n1 ^ t) (K ^ K)
  rw [e, sumTo_mul, sumTo_mul]
  refine Nat.le_trans (sumTo_mono _ (fun a _ => ?_)) (Nat.le_of_eq (sumTo_const _ (n1 ^ t)))
  cases hi : injT n1 t a
  · have z : ∀ H, indB (permB K H) * indB (false && (List.range t).all (fun j => chain1 K inner iv (rget n1 j a :: xs) H (L + 1) ==
        chain1 K inner iv (rget n1 0 a :: xs) H (L + 1))) = 0 := fun H => by rw [Bool.false_and]; exact Nat.mul_zero _
    rw [sumTo_congr _ (fun H _ => z H), sumTo_const, Nat.mul_zero, Nat.mul_zero, Nat.mul_zero]; exact Nat.zero_le _
  · have hdT : ∀ i j, i < t → j < t → i ≠ j → inner iv (rget n1 i a) ≠ inner iv (rget n1 j a) := fun i j hi' hj hij =>
      hd _ _ (rget_lt hn _ _) (rget_lt hn _ _) (injT_ne hn t a hi i j hi' hj hij)
    have hsep : ∀ H, ∀ i i' j j', i' < i → i ≤ L → j < t → j' < t →
        posS K inner iv t (fun j => rget n1 j a) xs H (i * t + j) ≠ posS K inner iv t (fun j => rget n1 j a) xs H (i' * t + j') :=
      fun H i i' j j' hii hiL hj hj' => by
        rw [posS_step K inner iv ht _ xs H i j hj, posS_step K inner iv ht _ xs H i' j' hj']
        exact hsepC H _ _ i i' (rget_lt hn _ _) (rget_lt hn _ _) hii hiL
    have hc := allMeet_countP hK inner hin κ hκ hF hpk iv ht (fun j => rget n1 j a) hdT xs L hsep
    refine Nat.le_trans (Nat.le_of_eq ?_) hc
    congr 2
    refine sumTo_congr _ (fun H _ => ?_)
    rw [Bool.true_and, indB_and']

/-- **The tuple load averaged**: with `Q = (t-1)! (K - L t)^(t-1)`,
    `Q s0 (s0-1) ⋯ (s0-t+1)` times the summed `loadT` is at most
    `Q s0 (s0-1) ⋯ (s0-t+1) (s0 - 1) + n1 n1^t ((0 + ⋯ + (L t - 1)) F)^(t-1)`
    per permutation table. -/
theorem loadT_countP {K Kc F : Nat} (hK : 0 < K) (inner : Nat → Nat → Nat) (hin : ∀ s x, inner s x < K) (κ : Nat → Nat)
    (hκ : ∀ u, κ u < Kc) (hF : ∀ v, sumTo K (fun u => indB (decide (κ u = v))) ≤ F)
    (hpk : ∀ x s s', inner s x = inner s' x → κ s = κ s') (iv : Nat) {n1 : Nat} (hn : 0 < n1)
    (hd : ∀ a b, a < n1 → b < n1 → a ≠ b → inner iv a ≠ inner iv b) (xs : List Nat) (L : Nat)
    (hsepC : ∀ H c c' i i', c < n1 → c' < n1 → i' < i → i ≤ L →
      inner (chain1 K inner iv (c :: xs) H i) ((c :: xs).getD i 0) ≠ inner (chain1 K inner iv (c' :: xs) H i') ((c' :: xs).getD i' 0))
    {t : Nat} (ht : 0 < t) (s0 : Nat) :
    fact (t - 1) * (K - L * t) ^ (t - 1) * ffac s0 t * sumTo (K ^ K) (fun H => indB (permB K H) * loadT K inner iv n1 xs L t s0 H) ≤
      (fact (t - 1) * (K - L * t) ^ (t - 1) * ffac s0 t * (s0 - 1) + n1 * (n1 ^ t * (sumTo (L * t) (fun j => j) * F) ^ (t - 1))) *
        sumTo (K ^ K) (fun H => indB (permB K H)) := by
  have hm0 := meetM_countP hK inner hin κ hκ hF hpk iv hn hd xs L hsepC ht
  have hm : fact (t - 1) * (K - L * t) ^ (t - 1) * sumTo (K ^ K) (fun H => indB (permB K H) * meetM K inner iv n1 xs L t H) ≤
      n1 ^ t * (sumTo (L * t) (fun j => j) * F) ^ (t - 1) * sumTo (K ^ K) (fun H => indB (permB K H)) := by
    rw [Nat.mul_assoc, Nat.mul_assoc (n1 ^ t)]; exact hm0
  clear hm0
  generalize hQ : fact (t - 1) * (K - L * t) ^ (t - 1) = Q at *
  generalize hPi : sumTo (K ^ K) (fun H => indB (permB K H)) = Pi0 at *
  -- Markov: the tables where meetM reaches ffac s0 t
  have mk : ffac s0 t * sumTo (K ^ K) (fun H => indB (permB K H && decide (ffac s0 t ≤ meetM K inner iv n1 xs L t H))) ≤
      sumTo (K ^ K) (fun H => indB (permB K H) * meetM K inner iv n1 xs L t H) := by
    rw [sumTo_mul]
    refine sumTo_mono _ (fun H _ => ?_)
    cases permB K H
    · simp [indB]
    · by_cases h : ffac s0 t ≤ meetM K inner iv n1 xs L t H
      · rw [decide_eq_true h]; simp only [Bool.true_and, show indB true = 1 from rfl, Nat.mul_one, Nat.one_mul]; exact h
      · rw [decide_eq_false h]; simp [indB]
  have e : ∀ H, indB (permB K H) * loadT K inner iv n1 xs L t s0 H = indB (permB K H) * (s0 - 1) +
      n1 * indB (permB K H && decide (ffac s0 t ≤ meetM K inner iv n1 xs L t H)) := fun H => by
    unfold loadT; rw [Nat.mul_add, Nat.mul_left_comm, indB_and']
  have e2 : sumTo (K ^ K) (fun H => indB (permB K H) * (s0 - 1)) = (s0 - 1) * Pi0 := by
    rw [← hPi, sumTo_mul]; exact sumTo_congr _ (fun H _ => Nat.mul_comm _ _)
  rw [sumTo_congr _ (fun H _ => e H), sumTo_add, e2, ← sumTo_mul]
  generalize hB : sumTo (K ^ K) (fun H => indB (permB K H && decide (ffac s0 t ≤ meetM K inner iv n1 xs L t H))) = Bd at *
  generalize hMM : sumTo (K ^ K) (fun H => indB (permB K H) * meetM K inner iv n1 xs L t H) = MM at *
  generalize hW : n1 ^ t * (sumTo (L * t) (fun j => j) * F) ^ (t - 1) = W at *
  generalize hf : ffac s0 t = f at *
  -- Q f ((s0-1) Pi0 + n1 Bd) ≤ (Q f (s0-1) + n1 W) Pi0, from f Bd ≤ MM and Q MM ≤ W Pi0
  have h1 : Q * (f * Bd) ≤ Q * MM := Nat.mul_le_mul_left _ mk
  have hm' : Q * MM ≤ W * Pi0 := hm
  calc Q * f * ((s0 - 1) * Pi0 + n1 * Bd) = Q * f * (s0 - 1) * Pi0 + n1 * (Q * (f * Bd)) := by
        rw [Nat.mul_add]; congr 1 <;> ac_rfl
    _ ≤ Q * f * (s0 - 1) * Pi0 + n1 * (W * Pi0) := Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.le_trans h1 hm')) _
    _ = (Q * f * (s0 - 1) + n1 * W) * Pi0 := by rw [Nat.add_mul, Nat.mul_assoc n1]

/-! ### Domain separation by tags, and every later transcript -/

/-- The later block list `xsOf X L i` carries the tags `1, 2, …, L`. -/
def tagOK (X L : Nat) (tb : Nat → Nat) (i : Nat) : Bool :=
  (List.range L).all (fun m => tb (rget X m i) == m + 1)

/-- **Tags separate the steps**: a position's tag is its block's (`hτ`), first
    commitments carry tag `0` and the later block `m` tag `m + 1`; then
    positions at different steps differ, at every table. -/
theorem sep_of_tags {K : Nat} (inner : Nat → Nat → Nat) (τ tb : Nat → Nat) (hτ : ∀ s x, τ (inner s x) = tb x)
    (iv n1 : Nat) (h0 : ∀ c, c < n1 → tb c = 0) (xs : List Nat) (L : Nat)
    (hxs : ∀ m, m < L → tb (xs.getD m 0) = m + 1) :
    ∀ H c c' i i', c < n1 → c' < n1 → i' < i → i ≤ L →
      inner (chain1 K inner iv (c :: xs) H i) ((c :: xs).getD i 0) ≠ inner (chain1 K inner iv (c' :: xs) H i') ((c' :: xs).getD i' 0) := by
  intro H c c' i i' _ hc' hii hiL e
  have := congrArg τ e
  rw [hτ, hτ] at this
  obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by omega⟩
  have hl : tb ((c :: xs).getD (m + 1) 0) = m + 1 := hxs m (by omega)
  cases i' with
  | zero =>
    have hr : tb ((c' :: xs).getD 0 0) = 0 := h0 c' hc'
    rw [hl, hr] at this; exact Nat.succ_ne_zero _ this
  | succ m' =>
    have hr : tb ((c' :: xs).getD (m' + 1) 0) = m' + 1 := hxs m' (by omega)
    rw [hl, hr] at this; omega

theorem tagOK_xsOf {X L : Nat} (tb : Nat → Nat) (i : Nat) (h : tagOK X L tb i = true) :
    ∀ m, m < L → tb ((xsOf X L i).getD m 0) = m + 1 := fun m hm => by
  rw [xsOf_getD X L i m hm]; exact beq_iff_eq.1 (List.all_eq_true.1 h m (List.mem_range.2 hm))

/-- The tuple load for every tagged later transcript. -/
def loadTA (K : Nat) (inner : Nat → Nat → Nat) (iv n1 : Nat) (tb : Nat → Nat) (X L t s0 H : Nat) : Nat :=
  (s0 - 1) + n1 * sumTo (X ^ L) (fun i => indB (tagOK X L tb i && decide (ffac s0 t ≤ meetM K inner iv n1 (xsOf X L i) L t H)))

theorem preimage_loadTA (K : Nat) (inner : Nat → Nat → Nat) (iv : Nat) {n1 : Nat} (hn : 0 < n1) (tb : Nat → Nat)
    {X : Nat} (hX : 0 < X) (L t s0 : Nat) (xs : List Nat) (hxs : ∀ m, m < L → xs.getD m 0 < X)
    (htag : ∀ m, m < L → tb (xs.getD m 0) = m + 1) (H v : Nat) :
    sumTo n1 (fun c => indB (decide (chain1 K inner iv (c :: xs) H (L + 1) = v))) ≤ loadTA K inner iv n1 tb X L t s0 H := by
  obtain ⟨i, hi, hag⟩ := xsOf_cover hX xs hxs
  have hch : ∀ c, chain1 K inner iv (c :: xs) H (L + 1) = chain1 K inner iv (c :: xsOf X L i) H (L + 1) :=
    fun c => chain1_congr K inner iv _ _ H (L + 1) (fun j hj => by
      cases j with
      | zero => rfl
      | succ j => exact hag j (Nat.lt_of_succ_lt_succ hj))
  have hok : tagOK X L tb i = true := List.all_eq_true.2 (fun m hm => by
    have hm' := List.mem_range.1 hm
    rw [← xsOf_getD X L i m hm', ← hag m hm', htag m hm']; exact beq_iff_eq.2 rfl)
  rw [sumTo_congr _ (fun c _ => by rw [hch c])]
  refine Nat.le_trans (preimage_loadT K inner iv hn (xsOf X L i) L t s0 H v) ?_
  unfold loadT loadTA
  refine Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.le_trans ?_ (le_sumTo (fun i => indB (tagOK X L tb i &&
    decide (ffac s0 t ≤ meetM K inner iv n1 (xsOf X L i) L t H))) _ hi))) _
  rw [hok, Bool.true_and]; exact Nat.le_refl _

/-- **Markov for meeting tuples**: per tagged later block list. -/
theorem meet_markov {K Kc F : Nat} (hK : 0 < K) (inner : Nat → Nat → Nat) (hin : ∀ s x, inner s x < K) (κ : Nat → Nat)
    (hκ : ∀ u, κ u < Kc) (hF : ∀ v, sumTo K (fun u => indB (decide (κ u = v))) ≤ F)
    (hpk : ∀ x s s', inner s x = inner s' x → κ s = κ s') (iv : Nat) {n1 : Nat} (hn : 0 < n1)
    (hd : ∀ a b, a < n1 → b < n1 → a ≠ b → inner iv a ≠ inner iv b) (xs : List Nat) (L : Nat)
    (hsepC : ∀ H c c' i i', c < n1 → c' < n1 → i' < i → i ≤ L →
      inner (chain1 K inner iv (c :: xs) H i) ((c :: xs).getD i 0) ≠ inner (chain1 K inner iv (c' :: xs) H i') ((c' :: xs).getD i' 0))
    {t : Nat} (ht : 0 < t) (s0 : Nat) :
    fact (t - 1) * (K - L * t) ^ (t - 1) * (ffac s0 t * sumTo (K ^ K) (fun H =>
        indB (permB K H && decide (ffac s0 t ≤ meetM K inner iv n1 xs L t H)))) ≤
      n1 ^ t * (sumTo (L * t) (fun j => j) * F) ^ (t - 1) * sumTo (K ^ K) (fun H => indB (permB K H)) := by
  have hm0 := meetM_countP hK inner hin κ hκ hF hpk iv hn hd xs L hsepC ht
  have mk : ffac s0 t * sumTo (K ^ K) (fun H => indB (permB K H && decide (ffac s0 t ≤ meetM K inner iv n1 xs L t H))) ≤
      sumTo (K ^ K) (fun H => indB (permB K H) * meetM K inner iv n1 xs L t H) := by
    rw [sumTo_mul]
    refine sumTo_mono _ (fun H _ => ?_)
    cases permB K H
    · simp [indB]
    · by_cases h : ffac s0 t ≤ meetM K inner iv n1 xs L t H
      · rw [decide_eq_true h]; simp only [Bool.true_and, show indB true = 1 from rfl, Nat.mul_one, Nat.one_mul]; exact h
      · rw [decide_eq_false h]; simp [indB]
  calc fact (t - 1) * (K - L * t) ^ (t - 1) * (ffac s0 t * sumTo (K ^ K) (fun H =>
        indB (permB K H && decide (ffac s0 t ≤ meetM K inner iv n1 xs L t H))))
      ≤ fact (t - 1) * (K - L * t) ^ (t - 1) * sumTo (K ^ K) (fun H => indB (permB K H) * meetM K inner iv n1 xs L t H) :=
        Nat.mul_le_mul_left _ mk
    _ = fact (t - 1) * ((K - L * t) ^ (t - 1) * sumTo (K ^ K) (fun H => indB (permB K H) * meetM K inner iv n1 xs L t H)) :=
        Nat.mul_assoc _ _ _
    _ ≤ _ := by rw [Nat.mul_assoc (n1 ^ t)]; exact hm0

/-- **The tagged tuple load averaged**: `Q = (t-1)! (K - L t)^(t-1)`, `f =
    s0 (s0-1) ⋯ (s0-t+1)`; `Q f` times the summed `loadTA` is at most
    `Q f (s0 - 1) + n1 X^L n1^t ((0 + ⋯ + (L t - 1)) F)^(t-1)` per
    permutation table. -/
theorem loadTA_countP {K Kc F : Nat} (hK : 0 < K) (inner : Nat → Nat → Nat) (hin : ∀ s x, inner s x < K) (κ : Nat → Nat)
    (hκ : ∀ u, κ u < Kc) (hF : ∀ v, sumTo K (fun u => indB (decide (κ u = v))) ≤ F)
    (hpk : ∀ x s s', inner s x = inner s' x → κ s = κ s') (iv : Nat) {n1 : Nat} (hn : 0 < n1)
    (hd : ∀ a b, a < n1 → b < n1 → a ≠ b → inner iv a ≠ inner iv b) (τ tb : Nat → Nat) (hτ : ∀ s x, τ (inner s x) = tb x)
    (h0 : ∀ c, c < n1 → tb c = 0) (X L : Nat) {t : Nat} (ht : 0 < t) (s0 : Nat) :
    fact (t - 1) * (K - L * t) ^ (t - 1) * ffac s0 t * sumTo (K ^ K) (fun H => indB (permB K H) * loadTA K inner iv n1 tb X L t s0 H) ≤
      (fact (t - 1) * (K - L * t) ^ (t - 1) * ffac s0 t * (s0 - 1) +
        n1 * (X ^ L * (n1 ^ t * (sumTo (L * t) (fun j => j) * F) ^ (t - 1)))) * sumTo (K ^ K) (fun H => indB (permB K H)) := by
  let bad := fun i H => indB (permB K H && (tagOK X L tb i && decide (ffac s0 t ≤ meetM K inner iv n1 (xsOf X L i) L t H)))
  have each : ∀ i, fact (t - 1) * (K - L * t) ^ (t - 1) * (ffac s0 t * sumTo (K ^ K) (fun H => bad i H)) ≤
      n1 ^ t * (sumTo (L * t) (fun j => j) * F) ^ (t - 1) * sumTo (K ^ K) (fun H => indB (permB K H)) := by
    intro i
    cases hok : tagOK X L tb i
    · have z : sumTo (K ^ K) (fun H => bad i H) = 0 :=
        Eq.trans (sumTo_congr _ (fun H _ => by show indB (permB K H && (tagOK X L tb i && _)) = 0; rw [hok]; simp [indB]))
          (Eq.trans (sumTo_const 0 _) (Nat.mul_zero _))
      rw [z, Nat.mul_zero, Nat.mul_zero]; exact Nat.zero_le _
    · have hs := sep_of_tags (K := K) inner τ tb hτ iv n1 h0 (xsOf X L i) L (tagOK_xsOf tb i hok)
      have hm := meet_markov hK inner hin κ hκ hF hpk iv hn hd (xsOf X L i) L hs ht s0
      refine Nat.le_trans (Nat.le_of_eq ?_) hm
      have z : sumTo (K ^ K) (fun H => bad i H) = sumTo (K ^ K) (fun H =>
          indB (permB K H && decide (ffac s0 t ≤ meetM K inner iv n1 (xsOf X L i) L t H))) :=
        sumTo_congr _ (fun H _ => by show indB (permB K H && (tagOK X L tb i && _)) = _; rw [hok, Bool.true_and])
      rw [z]
  have e : ∀ H, indB (permB K H) * loadTA K inner iv n1 tb X L t s0 H = indB (permB K H) * (s0 - 1) +
      n1 * sumTo (X ^ L) (fun i => bad i H) := fun H => by
    unfold loadTA
    rw [Nat.mul_add, Nat.mul_left_comm, sumTo_mul]
    congr 2
    exact sumTo_congr _ (fun i _ => indB_and' _ _)
  have e2 : sumTo (K ^ K) (fun H => indB (permB K H) * (s0 - 1)) = (s0 - 1) * sumTo (K ^ K) (fun H => indB (permB K H)) := by
    rw [sumTo_mul]; exact sumTo_congr _ (fun H _ => Nat.mul_comm _ _)
  rw [sumTo_congr _ (fun H _ => e H), sumTo_add, e2, ← sumTo_mul, sumTo_exch _ (X ^ L) (K ^ K)]
  generalize hPi : sumTo (K ^ K) (fun H => indB (permB K H)) = Pi0 at *
  generalize hQ : fact (t - 1) * (K - L * t) ^ (t - 1) = Q at *
  generalize hW : n1 ^ t * (sumTo (L * t) (fun j => j) * F) ^ (t - 1) = W at *
  generalize hf : ffac s0 t = f at *
  have hs : Q * (f * sumTo (X ^ L) (fun i => sumTo (K ^ K) (fun H => bad i H))) ≤ X ^ L * (W * Pi0) := by
    rw [sumTo_mul, sumTo_mul]
    refine Nat.le_trans (sumTo_mono _ (fun i _ => ?_)) (Nat.le_of_eq (sumTo_const _ (X ^ L)))
    exact each i
  calc Q * f * ((s0 - 1) * Pi0 + n1 * sumTo (X ^ L) (fun i => sumTo (K ^ K) (fun H => bad i H)))
      = Q * f * (s0 - 1) * Pi0 + n1 * (Q * (f * sumTo (X ^ L) (fun i => sumTo (K ^ K) (fun H => bad i H)))) := by
        rw [Nat.mul_add]; congr 1 <;> ac_rfl
    _ ≤ Q * f * (s0 - 1) * Pi0 + n1 * (X ^ L * (W * Pi0)) := Nat.add_le_add_left (Nat.mul_le_mul_left _ hs) _
    _ = _ := by rw [Nat.add_mul]; ac_rfl

/-- **`SudChallenger`'s spread hypotheses at every permutation table, `L + 1`
    absorptions**: the index `φ m w` the state after the first commitment
    `m % n1` and the later blocks `enc (m / n1) w`, each below `X` and
    tagged by its step; the table's `δs' = δs loadTA` meets `hsp1` and
    `hφsp` for every `d`, `rest`, `w` and `v` (`s0 ≥ 2`). -/
theorem loadTA_hsp {D W : Type} {K NS1 n1 δs X : Nat} (inner : Nat → Nat → Nat) (iv : Nat) (tb : Nat → Nat) (hX : 0 < X) (L t : Nat)
    (enc : Nat → W → List Nat) (henc : ∀ r w i, i < L → (enc r w).getD i 0 < X)
    (htag : ∀ r w i, i < L → tb ((enc r w).getD i 0) = i + 1)
    (Com1 : D → Nat → Nat) (hr1 : ∀ d σ, Com1 d σ < n1)
    (hsp1 : ∀ d v, sumTo NS1 (fun σ => indB (decide (Com1 d σ = v))) ≤ δs) {s0 : Nat} (hs0 : 2 ≤ s0) (H : Nat) :
    (∀ d v, sumTo NS1 (fun σ => indB (decide (Com1 d σ = v))) ≤ δs * loadTA K inner iv n1 tb X L t s0 H) ∧
      (∀ d rest w v, sumTo NS1 (fun σ1 => indB (decide
        ((fun m' w => chain1 K inner iv ((m' % n1) :: enc (m' / n1) w) H (L + 1)) (Com1 d σ1 + n1 * rest) w = v))) ≤
        δs * loadTA K inner iv n1 tb X L t s0 H) := by
  have h1 : 1 ≤ loadTA K inner iv n1 tb X L t s0 H := Nat.le_trans (Nat.le_sub_of_add_le hs0) (Nat.le_add_right _ _)
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
  exact Nat.mul_le_mul_left _ (preimage_loadTA K inner iv hn1 tb hX L t s0 (enc rest w) (henc rest w) (htag rest w) H v)

theorem loadTA_δs_countP {K Kc F : Nat} (hK : 0 < K) (inner : Nat → Nat → Nat) (hin : ∀ s x, inner s x < K) (κ : Nat → Nat)
    (hκ : ∀ u, κ u < Kc) (hF : ∀ v, sumTo K (fun u => indB (decide (κ u = v))) ≤ F)
    (hpk : ∀ x s s', inner s x = inner s' x → κ s = κ s') (iv : Nat) {n1 : Nat} (hn : 0 < n1)
    (hd : ∀ a b, a < n1 → b < n1 → a ≠ b → inner iv a ≠ inner iv b) (τ tb : Nat → Nat) (hτ : ∀ s x, τ (inner s x) = tb x)
    (h0 : ∀ c, c < n1 → tb c = 0) (X L : Nat) {t : Nat} (ht : 0 < t) (s0 δs : Nat) :
    fact (t - 1) * (K - L * t) ^ (t - 1) * ffac s0 t *
        sumTo (K ^ K) (fun H => indB (permB K H) * (δs * loadTA K inner iv n1 tb X L t s0 H)) ≤
      δs * ((fact (t - 1) * (K - L * t) ^ (t - 1) * ffac s0 t * (s0 - 1) +
        n1 * (X ^ L * (n1 ^ t * (sumTo (L * t) (fun j => j) * F) ^ (t - 1)))) * sumTo (K ^ K) (fun H => indB (permB K H))) := by
  have h := loadTA_countP hK inner hin κ hκ hF hpk iv hn hd τ tb hτ h0 X L ht s0
  rw [sumTo_congr _ (fun H _ => Nat.mul_left_comm _ _ _), ← sumTo_mul, Nat.mul_left_comm]
  exact Nat.mul_le_mul_left _ h

/-- The spread the permutation `H` gives proof `ix`: `δ0 ix loadTA`. -/
def δsT (K : Nat) (inner : Nat → Nat → Nat) (iv n1 : Nat) (tb : Nat → Nat) (X L t s0 : Nat) (δ0 : Nat → Nat) (H ix : Nat) : Nat :=
  δ0 ix * loadTA K inner iv n1 tb X L t s0 H

/-- **Tags at the full-width instance**: with the block overwriting the low
    digit `x % R1` and tags read off its range, `τ p = (p % R1) / Y`, the tag
    is the block's; first commitments below `Y` carry tag `0`, and a later
    block in `[(m+1) Y, (m+2) Y)` carries tag `m + 1`. -/
theorem tag_satPT {R1 R2 C Y n1 : Nat} (hR1 : 0 < R1) (hY : n1 ≤ Y) (hYR : Y ≤ R1) :
    (∀ s x, ((x % R1 + R1 * ((s / R1) % (R2 * C))) % R1) / Y = (x % R1) / Y) ∧
      (∀ c, c < n1 → (c % R1) / Y = 0) := by
  refine ⟨fun s x => by rw [Nat.add_mul_mod_self_left, Nat.mod_mod], fun c hc => ?_⟩
  rw [Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hc (Nat.le_trans hY hYR))]
  exact Nat.div_eq_of_lt (Nat.lt_of_lt_of_le hc hY)

section
open B Air Stmt Mach Sudoku SudokuText Compose CompM Wit

set_option maxRecDepth 100000 in
/-- **`sud_interleaveS` averaged over a uniform permutation, the index
    after the first commitment and `L` tagged later blocks** (`loadφA`): at
    each permutation table `P` with `δsT P = δ0 loadTA` (`loadTA_hsp`); the
    error the permutation-weighted sum of the tables' errors
    (`zkbT_avgW`). -/
theorem sud_interleaveLT {V Wv P1 P2 P3 W1 W2 W3 : Type} {kr kq : Nat} (φ1 : Nat → Nat → W1 → Nat) (nx1 : Nat → Nat → Nat → List Nat → Nat × Nat × W1) (G1 : Nat → Nat → Nat → List (List (List F)) → Nat → List Nat → P1) (φ2 : Nat → Nat → W2 → Nat) (nx2 : Nat → Nat → Nat → List Nat → Nat × Nat × W2) (G2 : Nat → Nat → Nat → List (List (List F)) → Nat → List Nat → P2) (φ3 : Nat → Nat → W3 → Nat) (nx3 : Nat → Nat → Nat → List Nat → Nat × Nat × W3) (G3 : Nat → Nat → Nat → List (List (List (List F))) × List (List (List F)) → Nat → List Nat → P3)
     (off : EF → String → EF) {puzzle : ∀ ix : Nat, List Nat} (hc : ∀ ix : Nat, CluesOK (cluesOf (puzzle ix))) {ρ : ∀ ix : Nat, Nat → Bool} {A : ∀ ix : Nat, List Cell} {k : ∀ ix : Nat, Nat} {row : ∀ ix : Nat, Nat → Air.Row} (hA : ∀ ix : Nat, AcceptsFrom (A ix) (stmtMachine (ρ ix) 729 (sudokuExpr (cluesOf (puzzle ix))) ACC REJ) (k ix) (row ix)) (hacc : ∀ ix : Nat, rd (A ix) ((row ix) ((k ix) - 1)).ctr ((row ix) ((k ix) - 1)).hd = some (.atom ACC)) (hlen : ∀ ix : Nat, (A ix).length = 2 ^ 16) (hk : ∀ ix : Nat, (k ix) ≤ 2 ^ 16) {tP : ∀ ix : Nat, Nat} (htp : ∀ ix : Nat, (tP ix) = progTp (stmtMachine (fun _ => false) 729 (sudokuExpr (cluesOf (puzzle ix))) ACC REJ).heap) (S16 S10 SP : ∀ ix : Nat, Nat → List F) (qv : ∀ ix : Nat, EF → EF → List EF → F → List F → List F → List EF) (wm wc ww wp : ∀ ix : Nat, Nat → List (EF → EF → List F)) {Lwm Lwc Lww Lwp : ∀ ix : Nat, Nat} (hlwm : ∀ ix : Nat, ∀ c, ((wm ix) c).length = (Lwm ix)) (hlwc : ∀ ix : Nat, ∀ c, ((wc ix) c).length = (Lwc ix)) (hlww : ∀ ix : Nat, ∀ c, ((ww ix) c).length = (Lww ix)) (hlwp : ∀ ix : Nat, ∀ c, ((wp ix) c).length = (Lwp ix)) {K2 K4 : Nat} (hK2 : 0 < K2) (hK4 : 0 < K4) (hS16 : ∀ ix : Nat, ∀ c4, ∀ x ∈ (S16 ix) c4, x ∉ cosetL 1 (bbGen 16) (2 ^ 16)) (hS10 : ∀ ix : Nat, ∀ c4, ∀ x ∈ (S10 ix) c4, x ∉ cosetL 1 (bbGen 10) (2 ^ 10)) (hSP : ∀ ix : Nat, ∀ c4, ∀ x ∈ (SP ix) c4, x ∉ cosetL 1 (bbGen ((tP ix) + 1)) (2 ^ ((tP ix) + 1))) (hsz16 : ∀ ix : Nat, ∀ c4, 2 * ((S16 ix) c4).length + 8 ≤ 2 ^ 16) (hsz : ∀ ix : Nat, ∀ c4, 2 * ((S10 ix) c4).length + 8 ≤ 2 ^ 10) (hszP : ∀ ix : Nat, ∀ c4, 2 * ((SP ix) c4).length + 8 ≤ 2 ^ ((tP ix) + 1)) {ncw : ∀ ix : Nat, Nat} (αd : ∀ ix : Nat, Nat → EF) {B4 : ∀ ix : Nat, Nat} (hB4 : ∀ ix : Nat, sumTo K4 (fun c4 => indB (!genB ((αd ix) c4))) ≤ (B4 ix)) (fri : ∀ ix : Nat, Nat → EF → EF → List (EF → EF) → V) (hncw : ∀ ix : Nat, 4 ≤ (ncw ix)) (NR2 : ∀ ix : Nat, Nat) (Rb : ∀ ix : Nat, Nat → EF → EF → Nat → List (EF → EF)) (Ro : ∀ ix : Nat, Nat → EF → EF → Nat → Wv) {n1 n2 n3 : Nat} {NS1 NS2 NS3 : ∀ ix : Nat, Nat} (Com1 : ∀ ix : Nat, List (List (List F)) → Nat → Nat) (hc1 : ∀ ix : Nat, ComHides (NS1 ix) (Com1 ix)) (hp1 : ∀ ix : Nat, ∀ c4 T1 T2 T3 T4 M, ComPfHides (NS1 ix) (Com1 ix) ((pfRdM (Q4 * Q4) K2 Q4 K4 n1 kr (φ1 ix) (nx1 ix) (G1 ix)) c4 T1 T2 T3 T4 M) (opF ((sudGroups (tP ix) ((S16 ix) c4) ((S10 ix) c4) ((SP ix) c4) EF.zero (qv ix)).map (·.base.S)) [0, 2, 4, 6])) (hr1 : ∀ ix : Nat, ∀ d σ, (Com1 ix) d σ < n1) (d1 : ∀ ix : Nat, List (List (List F))) (Com2 : ∀ ix : Nat, List (List (List F)) → Nat → Nat) (hc2 : ∀ ix : Nat, ComHides (NS2 ix) (Com2 ix)) (hp2 : ∀ ix : Nat, ∀ c4 T1 T2 T3 T4 M, ComPfHides (NS2 ix) (Com2 ix) ((pfRdM (Q4 * Q4) K2 Q4 K4 n1 kr (φ2 ix) (nx2 ix) (G2 ix)) c4 T1 T2 T3 T4 M) (opF ((sudGroups (tP ix) ((S16 ix) c4) ((S10 ix) c4) ((SP ix) c4) EF.zero (qv ix)).map (·.base.S)) [1, 3, 5, 7])) (hr2 : ∀ ix : Nat, ∀ d σ, (Com2 ix) d σ < n2) (d2 : ∀ ix : Nat, List (List (List F))) (Com3 : ∀ ix : Nat, List (List (List (List F))) × List (List (List F)) → Nat → Nat) (hc3 : ∀ ix : Nat, ComHides (NS3 ix) (Com3 ix)) (hp3 : ∀ ix : Nat, ∀ c4 T1 T2 T3 T4 M, ComPfHides (NS3 ix) (Com3 ix) ((pfRdM (Q4 * Q4) K2 Q4 K4 n1 kr (φ3 ix) (nx3 ix) (G3 ix)) c4 T1 T2 T3 T4 M) (fun d => (opQ (sudSsT ((S16 ix) c4) ((S10 ix) c4) ((SP ix) c4)) d.1, opCw (sudSsC (tP ix) ((S16 ix) c4) ((S10 ix) c4) ((SP ix) c4)) d.2))) (hr3 : ∀ ix : Nat, ∀ d σ, (Com3 ix) d σ < n3) (d3 : ∀ ix : Nat, List (List (List (List F))) × List (List (List F)))
    {Kp : Nat} (hKp : 0 < Kp) (inner : Nat → Nat → Nat) (hin : ∀ s x, inner s x < Kp) (κ : Nat → Nat) {Kc : Nat}
    (hκ : ∀ u, κ u < Kc) (hpk : ∀ x s s', inner s x = inner s' x → κ s = κ s') (iv : Nat)
    (hd : ∀ a b, a < n1 → b < n1 → a ≠ b → inner iv a ≠ inner iv b)
    (τ tb : Nat → Nat) (hτ : ∀ s x, τ (inner s x) = tb x) (h0 : ∀ c, c < n1 → tb c = 0)
    {X : Nat} (hX : 0 < X) (L : Nat) (enc : Nat → Option (List (List (List EF)) × List (List (List (List EF))) × List (List (List EF))) → List Nat) (henc : ∀ r w i, i < L → (enc r w).getD i 0 < X)
    (htag : ∀ r w i, i < L → tb ((enc r w).getD i 0) = i + 1) (δ0 : Nat → Nat)
    (hsp1 : ∀ ix d v, sumTo (NS1 ix) (fun σ => indB (decide (Com1 ix d σ = v))) ≤ δ0 ix) {t : Nat} (ht : 0 < t) {s0 : Nat} (hs0 : 2 ≤ s0)
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
            cond (isQ n) 0 (((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) n).NS * (((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) n).NR * (Q4 ^ 2 * δsT Kp inner iv n1 tb X L t s0 δ0 P n))))))) n))) := by
  intro n
  exact zkbT_avgW (fun P => indB (permB Kp P)) (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo (K4 ^ Kp) (fun H4 => sumTo ((Q4 * Q4) ^ n1) (fun H1 => sumTo (K2 ^ (n1 * n2)) (fun H2 => sumTo (Q4 ^ (n1 * (n2 * n3))) (fun H3 => f (H1, H2, H3, H4)))))) (smPowD (X := fun _ => Nat × Nat × Nat × (Nat → Tup)) (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc 0) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).sm 2) n) (scPowD (C := fun _ => Nat × Nat × Nat × Nat) (fun _ => (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo K4 (fun c4 => sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo Q4 (fun c3 => f (c1, c2, c3, c4))))))) n)
    (fun P => (rvPowD (mixRv (Q4 * Q4) K2 Q4 K4 kq isQ nxtQ
        (fun i => read4T (Q4 * Q4) K2 Q4 K4 ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).m1 ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).m2 ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).m3 ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).q ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).out)) n)) (fun P => (pgPowD (pgRd (Q4 * Q4) K2 Q4 K4 (fun i => !isQ i) (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).pts) (fun _ c => c)) n)) (fun P => (svPowDT (pgRd (Q4 * Q4) K2 Q4 K4 (fun i => !isQ i) (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).pts) (fun _ c => c))
        (mixSv (Q4 * Q4) K2 Q4 K4 kq isQ nxtQ (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).sv)) n))
    (fun P => (errPowD (fun _ => (K4 * (Q4 * Q4 * (K2 * Q4)))) (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).sm 2) (fun _ => (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo K4 (fun c4 => sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo Q4 (fun c3 => f (c1, c2, c3, c4))))))) (fun i => cond (isQ i) 0 ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).ε)
        (fun n => (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo K4 (fun c4 => sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo Q4 (fun c3 => f (c1, c2, c3, c4)))))) (fun _ => (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo (K4 ^ Kp) (fun H4 => sumTo ((Q4 * Q4) ^ n1) (fun H1 => sumTo (K2 ^ (n1 * n2)) (fun H2 => sumTo (Q4 ^ (n1 * (n2 * n3))) (fun H3 => f (H1, H2, H3, H4)))))) (fun _ => smPowD (X := fun _ => Nat × Nat × Nat × (Nat → Tup)) (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).sm 2) n
          (fun _ => rSum (fun i => cond (isQ i) kq (4 + 3 * kr)) n *
            cond (isQ n) 0 (((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) n).NS * (((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) n).NR * (Q4 ^ 2 * δsT Kp inner iv n1 tb X L t s0 δ0 P n))))))) n)) (fun P _ hw =>
    sud_interleaveS φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3 off hc hA hacc hlen hk htp S16 S10 SP qv wm wc ww wp hlwm hlwc hlww hlwp
      hK2 hK4 (loadφA Kp inner iv n1 L enc P) (fun _ _ _ => rget_lt hKp _ _) hS16 hS10 hSP hsz16 hsz hszP αd hB4 fri hncw NR2 Rb Ro
      Com1 hc1 hp1 hr1 d1 Com2 hc2 hp2 hr2 d2 Com3 hc3 hp3 hr3 d3 (δsT Kp inner iv n1 tb X L t s0 δ0 P)
      (fun ix => (loadTA_hsp inner iv tb hX L t enc henc htag (Com1 ix) (hr1 ix) (hsp1 ix) hs0 P).1)
      (fun ix => (loadTA_hsp inner iv tb hX L t enc henc htag (Com1 ix) (hr1 ix) (hsp1 ix) hs0 P).2) isQ nxtQ n)


set_option maxHeartbeats 1600000 in
set_option maxRecDepth 100000 in
/-- **`sud_interleaveLT` with a number for its error**: `Kq = (t-1)!
    (Kp - L t)^(t-1) s0 (s0-1) ⋯ (s0-t+1)` times the averaged real count is
    at most `Kq` times the averaged simulation plus `errPowD` at the errors
    `Kq W ε` and each spread `δ0 i (Kq (s0 - 1) + n1 X^L n1^t
    ((0 + ⋯ + (L t - 1)) F)^(t-1)) W`, `W` the number of permutation tables
    (`avg_err_bound`, `loadTA_δs_countP`). -/
theorem sud_interleaveLTN {V Wv P1 P2 P3 W1 W2 W3 : Type} {kr kq : Nat} (φ1 : Nat → Nat → W1 → Nat) (nx1 : Nat → Nat → Nat → List Nat → Nat × Nat × W1) (G1 : Nat → Nat → Nat → List (List (List F)) → Nat → List Nat → P1) (φ2 : Nat → Nat → W2 → Nat) (nx2 : Nat → Nat → Nat → List Nat → Nat × Nat × W2) (G2 : Nat → Nat → Nat → List (List (List F)) → Nat → List Nat → P2) (φ3 : Nat → Nat → W3 → Nat) (nx3 : Nat → Nat → Nat → List Nat → Nat × Nat × W3) (G3 : Nat → Nat → Nat → List (List (List (List F))) × List (List (List F)) → Nat → List Nat → P3)
     (off : EF → String → EF) {puzzle : ∀ ix : Nat, List Nat} (hc : ∀ ix : Nat, CluesOK (cluesOf (puzzle ix))) {ρ : ∀ ix : Nat, Nat → Bool} {A : ∀ ix : Nat, List Cell} {k : ∀ ix : Nat, Nat} {row : ∀ ix : Nat, Nat → Air.Row} (hA : ∀ ix : Nat, AcceptsFrom (A ix) (stmtMachine (ρ ix) 729 (sudokuExpr (cluesOf (puzzle ix))) ACC REJ) (k ix) (row ix)) (hacc : ∀ ix : Nat, rd (A ix) ((row ix) ((k ix) - 1)).ctr ((row ix) ((k ix) - 1)).hd = some (.atom ACC)) (hlen : ∀ ix : Nat, (A ix).length = 2 ^ 16) (hk : ∀ ix : Nat, (k ix) ≤ 2 ^ 16) {tP : ∀ ix : Nat, Nat} (htp : ∀ ix : Nat, (tP ix) = progTp (stmtMachine (fun _ => false) 729 (sudokuExpr (cluesOf (puzzle ix))) ACC REJ).heap) (S16 S10 SP : ∀ ix : Nat, Nat → List F) (qv : ∀ ix : Nat, EF → EF → List EF → F → List F → List F → List EF) (wm wc ww wp : ∀ ix : Nat, Nat → List (EF → EF → List F)) {Lwm Lwc Lww Lwp : ∀ ix : Nat, Nat} (hlwm : ∀ ix : Nat, ∀ c, ((wm ix) c).length = (Lwm ix)) (hlwc : ∀ ix : Nat, ∀ c, ((wc ix) c).length = (Lwc ix)) (hlww : ∀ ix : Nat, ∀ c, ((ww ix) c).length = (Lww ix)) (hlwp : ∀ ix : Nat, ∀ c, ((wp ix) c).length = (Lwp ix)) {K2 K4 : Nat} (hK2 : 0 < K2) (hK4 : 0 < K4) (hS16 : ∀ ix : Nat, ∀ c4, ∀ x ∈ (S16 ix) c4, x ∉ cosetL 1 (bbGen 16) (2 ^ 16)) (hS10 : ∀ ix : Nat, ∀ c4, ∀ x ∈ (S10 ix) c4, x ∉ cosetL 1 (bbGen 10) (2 ^ 10)) (hSP : ∀ ix : Nat, ∀ c4, ∀ x ∈ (SP ix) c4, x ∉ cosetL 1 (bbGen ((tP ix) + 1)) (2 ^ ((tP ix) + 1))) (hsz16 : ∀ ix : Nat, ∀ c4, 2 * ((S16 ix) c4).length + 8 ≤ 2 ^ 16) (hsz : ∀ ix : Nat, ∀ c4, 2 * ((S10 ix) c4).length + 8 ≤ 2 ^ 10) (hszP : ∀ ix : Nat, ∀ c4, 2 * ((SP ix) c4).length + 8 ≤ 2 ^ ((tP ix) + 1)) {ncw : ∀ ix : Nat, Nat} (αd : ∀ ix : Nat, Nat → EF) {B4 : ∀ ix : Nat, Nat} (hB4 : ∀ ix : Nat, sumTo K4 (fun c4 => indB (!genB ((αd ix) c4))) ≤ (B4 ix)) (fri : ∀ ix : Nat, Nat → EF → EF → List (EF → EF) → V) (hncw : ∀ ix : Nat, 4 ≤ (ncw ix)) (NR2 : ∀ ix : Nat, Nat) (Rb : ∀ ix : Nat, Nat → EF → EF → Nat → List (EF → EF)) (Ro : ∀ ix : Nat, Nat → EF → EF → Nat → Wv) {n1 n2 n3 : Nat} {NS1 NS2 NS3 : ∀ ix : Nat, Nat} (Com1 : ∀ ix : Nat, List (List (List F)) → Nat → Nat) (hc1 : ∀ ix : Nat, ComHides (NS1 ix) (Com1 ix)) (hp1 : ∀ ix : Nat, ∀ c4 T1 T2 T3 T4 M, ComPfHides (NS1 ix) (Com1 ix) ((pfRdM (Q4 * Q4) K2 Q4 K4 n1 kr (φ1 ix) (nx1 ix) (G1 ix)) c4 T1 T2 T3 T4 M) (opF ((sudGroups (tP ix) ((S16 ix) c4) ((S10 ix) c4) ((SP ix) c4) EF.zero (qv ix)).map (·.base.S)) [0, 2, 4, 6])) (hr1 : ∀ ix : Nat, ∀ d σ, (Com1 ix) d σ < n1) (d1 : ∀ ix : Nat, List (List (List F))) (Com2 : ∀ ix : Nat, List (List (List F)) → Nat → Nat) (hc2 : ∀ ix : Nat, ComHides (NS2 ix) (Com2 ix)) (hp2 : ∀ ix : Nat, ∀ c4 T1 T2 T3 T4 M, ComPfHides (NS2 ix) (Com2 ix) ((pfRdM (Q4 * Q4) K2 Q4 K4 n1 kr (φ2 ix) (nx2 ix) (G2 ix)) c4 T1 T2 T3 T4 M) (opF ((sudGroups (tP ix) ((S16 ix) c4) ((S10 ix) c4) ((SP ix) c4) EF.zero (qv ix)).map (·.base.S)) [1, 3, 5, 7])) (hr2 : ∀ ix : Nat, ∀ d σ, (Com2 ix) d σ < n2) (d2 : ∀ ix : Nat, List (List (List F))) (Com3 : ∀ ix : Nat, List (List (List (List F))) × List (List (List F)) → Nat → Nat) (hc3 : ∀ ix : Nat, ComHides (NS3 ix) (Com3 ix)) (hp3 : ∀ ix : Nat, ∀ c4 T1 T2 T3 T4 M, ComPfHides (NS3 ix) (Com3 ix) ((pfRdM (Q4 * Q4) K2 Q4 K4 n1 kr (φ3 ix) (nx3 ix) (G3 ix)) c4 T1 T2 T3 T4 M) (fun d => (opQ (sudSsT ((S16 ix) c4) ((S10 ix) c4) ((SP ix) c4)) d.1, opCw (sudSsC (tP ix) ((S16 ix) c4) ((S10 ix) c4) ((SP ix) c4)) d.2))) (hr3 : ∀ ix : Nat, ∀ d σ, (Com3 ix) d σ < n3) (d3 : ∀ ix : Nat, List (List (List (List F))) × List (List (List F)))
    {Kp : Nat} (hKp : 0 < Kp) (inner : Nat → Nat → Nat) (hin : ∀ s x, inner s x < Kp) (κ : Nat → Nat) {Kc : Nat}
    (hκ : ∀ u, κ u < Kc) (hpk : ∀ x s s', inner s x = inner s' x → κ s = κ s') (iv : Nat)
    (hd : ∀ a b, a < n1 → b < n1 → a ≠ b → inner iv a ≠ inner iv b)
    (τ tb : Nat → Nat) (hτ : ∀ s x, τ (inner s x) = tb x) (h0 : ∀ c, c < n1 → tb c = 0)
    {X : Nat} (hX : 0 < X) (L : Nat) (enc : Nat → Option (List (List (List EF)) × List (List (List (List EF))) × List (List (List EF))) → List Nat) (henc : ∀ r w i, i < L → (enc r w).getD i 0 < X)
    (htag : ∀ r w i, i < L → tb ((enc r w).getD i 0) = i + 1) (δ0 : Nat → Nat) (hn1 : 0 < n1) {F : Nat} (hF : ∀ v, sumTo Kp (fun u => indB (decide (κ u = v))) ≤ F)
    (hsp1 : ∀ ix d v, sumTo (NS1 ix) (fun σ => indB (decide (Com1 ix d σ = v))) ≤ δ0 ix) {t : Nat} (ht : 0 < t) {s0 : Nat} (hs0 : 2 ≤ s0)
    (isQ : Nat → Bool) (nxtQ : Nat → List Nat → Nat × Nat × Unit) :
    ∀ n (E : Nat × (Nat × Nat × Nat × Nat) → _ → Bool),
      (fact (t - 1) * (Kp - L * t) ^ (t - 1) * ffac s0 t) * ((KPowD (fun _ => (K4 * (Q4 * Q4 * (K2 * Q4)))) n) * (fun (f : Nat × (Nat × Nat × Nat × Nat) → Nat) => sumTo (Kp ^ Kp) (fun P => indB (permB Kp P) * (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo (K4 ^ Kp) (fun H4 => sumTo ((Q4 * Q4) ^ n1) (fun H1 => sumTo (K2 ^ (n1 * n2)) (fun H2 => sumTo (Q4 ^ (n1 * (n2 * n3))) (fun H3 => f (H1, H2, H3, H4)))))) (fun H => f (P, H)))) (fun H => (smPowD (X := fun _ => Nat × Nat × Nat × (Nat → Tup)) (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc 0) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).sm 2) n) (fun x => indB (E H ((fun PH x => (rvPowD (mixRv (Q4 * Q4) K2 Q4 K4 kq isQ nxtQ
        (fun i => read4T (Q4 * Q4) K2 Q4 K4 ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc PH.1) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).m1 ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc PH.1) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).m2 ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc PH.1) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).m3 ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc PH.1) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).q ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc PH.1) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).out)) n) PH.2 x) H x))))) ≤
        (fact (t - 1) * (Kp - L * t) ^ (t - 1) * ffac s0 t) * (fun (f : Nat × (Nat × Nat × Nat × Nat) → Nat) => sumTo (Kp ^ Kp) (fun P => indB (permB Kp P) * (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo (K4 ^ Kp) (fun H4 => sumTo ((Q4 * Q4) ^ n1) (fun H1 => sumTo (K2 ^ (n1 * n2)) (fun H2 => sumTo (Q4 ^ (n1 * (n2 * n3))) (fun H3 => f (H1, H2, H3, H4)))))) (fun H => f (P, H)))) (fun H => (scPowD (C := fun _ => Nat × Nat × Nat × Nat) (fun _ => (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo K4 (fun c4 => sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo Q4 (fun c3 => f (c1, c2, c3, c4))))))) n) (fun c => (smPowD (X := fun _ => Nat × Nat × Nat × (Nat → Tup)) (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc 0) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).sm 2) n) (fun x => indB (E ((fun PH c x => (PH.1, (pgPowD (pgRd (Q4 * Q4) K2 Q4 K4 (fun i => !isQ i) (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc PH.1) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).pts) (fun _ c => c)) n) PH.2 c x)) H c x) ((fun PH c x => (svPowDT (pgRd (Q4 * Q4) K2 Q4 K4 (fun i => !isQ i) (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc PH.1) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).pts) (fun _ c => c))
        (mixSv (Q4 * Q4) K2 Q4 K4 kq isQ nxtQ (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc PH.1) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).sv)) n) PH.2 c x) H c x))))) +
        errPowD (fun _ => (K4 * (Q4 * Q4 * (K2 * Q4)))) (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc 0) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).sm 2) (fun _ => (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo K4 (fun c4 => sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo Q4 (fun c3 => f (c1, c2, c3, c4))))))) (fun i => (fact (t - 1) * (Kp - L * t) ^ (t - 1) * ffac s0 t) * (sumTo (Kp ^ Kp) (fun P => indB (permB Kp P))) * (fun i => cond (isQ i) 0 ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc 0) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).ε) i) (fun i => (fun n x => (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo K4 (fun c4 => sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo Q4 (fun c3 => f (c1, c2, c3, c4)))))) (fun _ => (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo (K4 ^ Kp) (fun H4 => sumTo ((Q4 * Q4) ^ n1) (fun H1 => sumTo (K2 ^ (n1 * n2)) (fun H2 => sumTo (Q4 ^ (n1 * (n2 * n3))) (fun H3 => f (H1, H2, H3, H4)))))) (fun _ => smPowD (X := fun _ => Nat × Nat × Nat × (Nat → Tup)) (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc 0) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).sm 2) n
          (fun _ => rSum (fun i => cond (isQ i) kq (4 + 3 * kr)) n *
            cond (isQ n) 0 (((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc 0) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) n).NS * (((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc 0) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) n).NR * (Q4 ^ 2 * x))))))) i ((fun i => δ0 i * ((fact (t - 1) * (Kp - L * t) ^ (t - 1) * ffac s0 t * (s0 - 1) + n1 * (X ^ L * (n1 ^ t * (sumTo (L * t) (fun j => j) * F) ^ (t - 1)))) * (sumTo (Kp ^ Kp) (fun P => indB (permB Kp P))))) i)) n := by
  intro n E
  have h := sud_interleaveLT (kq := kq) φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3 off hc hA hacc hlen hk htp S16 S10 SP qv wm wc ww wp hlwm hlwc hlww hlwp hK2 hK4 hS16 hS10 hSP hsz16 hsz hszP αd hB4 fri hncw NR2 Rb Ro Com1 hc1 hp1 hr1 d1 Com2 hc2 hp2 hr2 d2 Com3 hc3 hp3 hr3 d3 hKp inner hin κ hκ hpk iv hd τ tb hτ h0 hX L enc henc htag δ0 hsp1 ht hs0 isQ nxtQ n
  have hb := (avg_err_bound (fun _ => (K4 * (Q4 * Q4 * (K2 * Q4)))) (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc 0) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).sm 2) (fun _ => (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo K4 (fun c4 => sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo Q4 (fun c3 => f (c1, c2, c3, c4))))))) (fun i => cond (isQ i) 0 ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc 0) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).ε) (Kp ^ Kp) (fun P => indB (permB Kp P))
      (fun P i => δsT Kp inner iv n1 tb X L t s0 δ0 P i) (fun n x => (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo K4 (fun c4 => sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo Q4 (fun c3 => f (c1, c2, c3, c4)))))) (fun _ => (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo (K4 ^ Kp) (fun H4 => sumTo ((Q4 * Q4) ^ n1) (fun H1 => sumTo (K2 ^ (n1 * n2)) (fun H2 => sumTo (Q4 ^ (n1 * (n2 * n3))) (fun H3 => f (H1, H2, H3, H4)))))) (fun _ => smPowD (X := fun _ => Nat × Nat × Nat × (Nat → Tup)) (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc 0) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).sm 2) n
          (fun _ => rSum (fun i => cond (isQ i) kq (4 + 3 * kr)) n *
            cond (isQ n) 0 (((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc 0) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) n).NS * (((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc 0) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) n).NR * (Q4 ^ 2 * x)))))))
      (fun i x => wrap_scale (lin_sum4 _ _ _ _) (lin_sum4 _ _ _ _) (lin_smPowD (fun _ => lin_sm _ _ _ _) i) _ _ _ _ _ x)
      (fact (t - 1) * (Kp - L * t) ^ (t - 1) * ffac s0 t) (fun i => δ0 i * ((fact (t - 1) * (Kp - L * t) ^ (t - 1) * ffac s0 t * (s0 - 1) + n1 * (X ^ L * (n1 ^ t * (sumTo (L * t) (fun j => j) * F) ^ (t - 1)))) * (sumTo (Kp ^ Kp) (fun P => indB (permB Kp P))))) (fun i => loadTA_δs_countP hKp inner hin κ hκ hF hpk iv hn1 hd τ tb hτ h0 X L ht s0 (δ0 i)) n)
  exact zkbT_err_le h _ _ hb E

end

end Circuit
