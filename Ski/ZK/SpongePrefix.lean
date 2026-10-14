import Ski.ZK.SpongeRoot

/-!
# Chains after a public prefix

`SpongeRoot` fixes the state `iv` before the first commitment, chosen
before the permutation.  Plonky3's batch-stark transcript absorbs a
domain separator and the instances' degree bits first, so the state the
first commitment meets is an answer of the permutation.  Here the joint
run starts with that prefix.

- **The run.** From a public `z`, the prefix's `m` public blocks `pre`,
  then `n1` chains from its last answer `ivP` (`posP`, `nxtP`,
  `runP_eq`, `nearN_runP`).
- **A label for the prefix.** The prefix's queries carry label `n1`; the
  chains `0, …, n1 - 1`.  When the chains all meet, the prefix's label
  may stay apart, so `n1` chains still need `n1 - 1` merges
  (`labR_finalR`).
- **What goes unpaid.** A chain query landing on a later prefix position
  merges with the prefix, paid by the prefix's previous answer, which
  shares its projection (`hpk2`).  Unpaid are a chain's first query
  repeating a prefix position (at most one chain per position, by `hd`),
  and the first later revisit of the prefix's first position or of a
  chain's first position (at most one each a step, by `hdx`): `m + 2 L`
  in all (`unpP`, `unpP_count`).  So chains that all meet make
  `n1 - 1 - (m + 2 L)` fresh near queries (`allMeet_nearP`).
- **The bounds.** `SpongeRoot`'s chain with `k = m + t (L+1)` queries and
  exponent `t - 1 - (m + 2 L)`: `allMeet_countPP`, `meetM_countPP`,
  `meet_markovP`, `loadTP`, `loadTP_countP`, `loadTP_hsp`, and the
  composite `sud_interleaveLP`, `sud_interleaveLPN`.  `hd` and `hdx`
  now hold from every state, as 0.8's absorption gives them
  (`inner08_hd`, `inner08_hdx`).

Limits: the first commitment fills the chains' first block (`SpongeAlign`
splits it); the fourth table `H4` stays independent of the permutation;
and every step after the first commitment absorbs a block, where 0.8 permutes an empty buffer, a squeeze leaving the rate, when a phase draws more than `RATE` elements (the bench's lookup phase draws `1 + 4 + 4 = 9` at `GRIND_LOOKUP = 5`).
-/

set_option autoImplicit false

namespace Circuit
open ZKF

/-- The prefix's `i`-th position: from `z`, the public blocks `pre`. -/
def posPre (K : Nat) (inner : Nat → Nat → Nat) (z : Nat) (pre : List Nat) (H i : Nat) : Nat :=
  inner (chain1 K inner z pre H i) (pre.getD i 0)

/-- The state after the prefix. -/
def ivP (K : Nat) (inner : Nat → Nat → Nat) (z : Nat) (pre : List Nat) (H : Nat) : Nat :=
  chain1 K inner z pre H pre.length

/-- Query `τ`'s position: the prefix's first, then the chains' from `ivP`. -/
def posP (K : Nat) (inner : Nat → Nat → Nat) (z : Nat) (pre : List Nat) (n1 : Nat) (cf : Nat → Nat) (xs : List Nat)
    (H τ : Nat) : Nat :=
  if τ < pre.length then posPre K inner z pre H τ else posS K inner (ivP K inner z pre H) n1 cf xs H (τ - pre.length)

/-- The joint run's next position from its answers, newest first. -/
def nxtP (inner : Nat → Nat → Nat) (z : Nat) (pre : List Nat) (n1 : Nat) (cf : Nat → Nat) (xs : List Nat)
    (l : List Nat) : Nat :=
  if l.length < pre.length then inner (if l.length = 0 then z else l.getD 0 0) (pre.getD l.length 0)
  else nxtS inner (if pre.length = 0 then z else l.getD (l.length - pre.length) 0) n1 cf xs (l.take (l.length - pre.length))

theorem rget_posPre (K : Nat) (inner : Nat → Nat → Nat) (z : Nat) (pre : List Nat) (H i : Nat) :
    rget K (posPre K inner z pre H i) H = chain1 K inner z pre H (i + 1) := rfl

/-- **The joint run is the prefix's queries, then the chains'.** -/
theorem runP_eq (K : Nat) (inner : Nat → Nat → Nat) (z : Nat) (pre : List Nat) {n1 : Nat} (hn1 : 0 < n1)
    (cf : Nat → Nat) (xs : List Nat) (H : Nat) :
    ∀ ℓ, runAdp K (nxtP inner z pre n1 cf xs) H ℓ =
      (List.range ℓ).reverse.map (fun τ => (posP K inner z pre n1 cf xs H τ, rget K (posP K inner z pre n1 cf xs H τ) H))
  | 0 => rfl
  | ℓ + 1 => by
    have ih := runP_eq K inner z pre hn1 cf xs H ℓ
    show (nxtP inner z pre n1 cf xs ((runAdp K (nxtP inner z pre n1 cf xs) H ℓ).map Prod.snd), _) ::
      runAdp K (nxtP inner z pre n1 cf xs) H ℓ = _
    rw [List.range_succ, List.reverse_append, List.map_append, ih]
    let ans := ((List.range ℓ).reverse.map (fun τ => (posP K inner z pre n1 cf xs H τ,
        rget K (posP K inner z pre n1 cf xs H τ) H))).map Prod.snd
    have hlen : ans.length = ℓ := by simp [ans]
    have hget : ∀ i, i < ℓ → ans.getD i 0 = rget K (posP K inner z pre n1 cf xs H (ℓ - 1 - i)) H := fun i hi => by
      show (((List.range ℓ).reverse.map _).map Prod.snd).getD i 0 = _
      rw [List.map_map, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_reverse (by
        rw [List.length_range]; exact hi), List.getElem?_range (by rw [List.length_range]; omega)]
      simp only [Option.map_some, Option.getD_some, Function.comp, List.length_range]
    have hp : nxtP inner z pre n1 cf xs ans = posP K inner z pre n1 cf xs H ℓ := by
      unfold nxtP
      rw [hlen]
      by_cases hl : ℓ < pre.length
      · rw [if_pos hl]
        unfold posP; rw [if_pos hl]
        unfold posPre
        congr 1
        cases ℓ with
        | zero => rfl
        | succ ℓ' =>
          rw [if_neg (Nat.succ_ne_zero _), hget 0 (Nat.succ_pos _)]
          have : ℓ' + 1 - 1 - 0 = ℓ' := by omega
          rw [this]
          unfold posP; rw [if_pos (by omega)]
          rfl
      · rw [if_neg hl]
        unfold posP; rw [if_neg hl]
        have hge : pre.length ≤ ℓ := Nat.le_of_not_lt hl
        -- the state after the prefix, read off the answers
        have hiv : (if pre.length = 0 then z else ans.getD (ℓ - pre.length) 0) = ivP K inner z pre H := by
          by_cases h0 : pre.length = 0
          · rw [if_pos h0]; unfold ivP; rw [h0]; rfl
          · rw [if_neg h0, hget _ (by omega)]
            have : ℓ - 1 - (ℓ - pre.length) = pre.length - 1 := by omega
            rw [this]
            unfold posP; rw [if_pos (by omega)]
            show chain1 K inner z pre H (pre.length - 1 + 1) = _
            rw [Nat.sub_add_cancel (Nat.pos_of_ne_zero h0)]; rfl
        rw [hiv]
        -- the chains' answers: the first `ℓ - m` of the list
        have htake : ans.take (ℓ - pre.length) = ((runAdp K (nxtS inner (ivP K inner z pre H) n1 cf xs) H
            (ℓ - pre.length)).map Prod.snd) := by
          rw [runS_eq K inner _ hn1 cf xs H]
          apply List.ext_getElem
          · simp [ans] <;> omega
          · intro i h1 h2
            have hi : i < ℓ - pre.length := by simpa using h2
            rw [List.getElem_take]
            have e1 := hget i (by omega)
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hlen]; omega)] at e1
            simp only [Option.getD_some] at e1
            rw [e1]
            simp only [List.getElem_map, List.getElem_reverse, List.getElem_range, List.length_range]
            unfold posP; rw [if_neg (by omega)]
            rw [show ℓ - 1 - i - pre.length = ℓ - pre.length - 1 - i by omega]
        rw [htake]
        -- the chains' next position, by `runS_eq` one step on
        have hs := runS_eq K inner (ivP K inner z pre H) hn1 cf xs H (ℓ - pre.length + 1)
        have hh : (runAdp K (nxtS inner (ivP K inner z pre H) n1 cf xs) H (ℓ - pre.length + 1)).head? =
            some (nxtS inner (ivP K inner z pre H) n1 cf xs ((runAdp K (nxtS inner (ivP K inner z pre H) n1 cf xs) H
              (ℓ - pre.length)).map Prod.snd), rget K (nxtS inner (ivP K inner z pre H) n1 cf xs ((runAdp K
                (nxtS inner (ivP K inner z pre H) n1 cf xs) H (ℓ - pre.length)).map Prod.snd)) H) := rfl
        rw [hs, List.range_succ, List.reverse_append] at hh
        simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append, List.map_cons,
          List.head?_cons, Option.some.injEq, Prod.mk.injEq] at hh
        exact hh.1.symm
    rw [hp]; rfl

/-- **The fresh near queries of the prefixed joint run are `nearN`'s.** -/
theorem nearN_runP {K : Nat} (hK : 0 < K) (inner : Nat → Nat → Nat) (κ : Nat → Nat) (z : Nat) (pre : List Nat) {n1 : Nat} (hn1 : 0 < n1)
    (cf : Nat → Nat) (xs : List Nat) (H : Nat) :
    ∀ T, nearN K (fun a b => decide (κ a = κ b)) (runAdp K (nxtP inner z pre n1 cf xs) H T) =
      sumTo T (fun τ => indB (nearInc (posP K inner z pre n1 cf xs H) (fun τ => κ (rget K (posP K inner z pre n1 cf xs H τ) H)) τ))
  | 0 => rfl
  | T + 1 => by
    have ih := nearN_runP hK inner κ z pre hn1 cf xs H T
    have hr : runAdp K (nxtP inner z pre n1 cf xs) H (T + 1) =
        (posP K inner z pre n1 cf xs H T, rget K (posP K inner z pre n1 cf xs H T) H) :: runAdp K (nxtP inner z pre n1 cf xs) H T := by
      rw [runP_eq K inner z pre hn1 cf xs H, runP_eq K inner z pre hn1 cf xs H, List.range_succ, List.reverse_append]; rfl
    rw [hr]
    show nearN K _ (runAdp K (nxtP inner z pre n1 cf xs) H T) + _ = sumTo T _ + _
    rw [ih]
    congr 2
    have hmem : ∀ q, q ∈ (runAdp K (nxtP inner z pre n1 cf xs) H T).map Prod.fst ↔ ∃ τ, τ < T ∧ posP K inner z pre n1 cf xs H τ = q := by
      intro q
      rw [runP_eq K inner z pre hn1 cf xs H, List.map_map, List.mem_map]
      exact ⟨fun ⟨τ, hτ, e⟩ => ⟨τ, List.mem_range.1 (List.mem_reverse.1 hτ), e⟩,
        fun ⟨τ, hτ, e⟩ => ⟨τ, List.mem_reverse.2 (List.mem_range.2 hτ), e⟩⟩
    have hsnd : ∀ u, u ∈ (runAdp K (nxtP inner z pre n1 cf xs) H T).map Prod.snd ↔
        ∃ τ, τ < T ∧ rget K (posP K inner z pre n1 cf xs H τ) H = u := by
      intro u
      rw [runP_eq K inner z pre hn1 cf xs H, List.map_map, List.mem_map]
      exact ⟨fun ⟨τ, hτ, e⟩ => ⟨τ, List.mem_range.1 (List.mem_reverse.1 hτ), e⟩,
        fun ⟨τ, hτ, e⟩ => ⟨τ, List.mem_reverse.2 (List.mem_range.2 hτ), e⟩⟩
    have e1 : decide (posP K inner z pre n1 cf xs H T ∈ (runAdp K (nxtP inner z pre n1 cf xs) H T).map Prod.fst) =
        oldB (posP K inner z pre n1 cf xs H) T := by
      cases h : oldB (posP K inner z pre n1 cf xs H) T
      · refine decide_eq_false (fun hm => ?_)
        obtain ⟨τ, hτ, e⟩ := (hmem _).1 hm
        rw [oldB_spec _ hτ e] at h; exact Bool.noConfusion h
      · obtain ⟨hf, ef⟩ := firstOld_spec _ h
        exact decide_eq_true ((hmem _).2 ⟨_, hf, ef⟩)
    have e2 : decide (rget K (posP K inner z pre n1 cf xs H T) H ∈ nearR K (fun a b => decide (κ a = κ b))
          ((runAdp K (nxtP inner z pre n1 cf xs) H T).map Prod.snd)) =
        (List.range T).any (fun τ' => κ (rget K (posP K inner z pre n1 cf xs H τ') H) == κ (rget K (posP K inner z pre n1 cf xs H T) H)) := by
      cases h : (List.range T).any (fun τ' => κ (rget K (posP K inner z pre n1 cf xs H τ') H) == κ (rget K (posP K inner z pre n1 cf xs H T) H))
      · refine decide_eq_false (fun hm => ?_)
        unfold nearR at hm
        obtain ⟨_, hany⟩ := List.mem_filter.1 hm
        obtain ⟨u, hu, hk⟩ := List.any_eq_true.1 hany
        obtain ⟨τ, hτ, e⟩ := (hsnd u).1 hu
        have := List.any_eq_false.1 h τ (List.mem_range.2 hτ)
        exact this (by rw [e]; exact beq_iff_eq.2 (of_decide_eq_true hk))
      · obtain ⟨τ, hτ, hk⟩ := List.any_eq_true.1 h
        refine decide_eq_true ?_
        unfold nearR
        refine List.mem_filter.2 ⟨List.mem_range.2 (rget_lt hK _ _), List.any_eq_true.2 ⟨_, (hsnd _).2 ⟨τ, List.mem_range.1 hτ, rfl⟩, ?_⟩⟩
        exact decide_eq_true (beq_iff_eq.1 hk)
    unfold nearInc
    rw [e1, e2]


theorem posP_pre (K : Nat) (inner : Nat → Nat → Nat) (z : Nat) (pre : List Nat) (n1 : Nat) (cf : Nat → Nat) (xs : List Nat)
    (H : Nat) {i : Nat} (hi : i < pre.length) :
    posP K inner z pre n1 cf xs H i = inner (chain1 K inner z pre H i) (pre.getD i 0) := by
  unfold posP; rw [if_pos hi]; rfl

theorem posP_chain (K : Nat) (inner : Nat → Nat → Nat) (z : Nat) (pre : List Nat) (n1 : Nat) (cf : Nat → Nat) (xs : List Nat)
    (H τ : Nat) (hτ : pre.length ≤ τ) :
    posP K inner z pre n1 cf xs H τ = posS K inner (ivP K inner z pre H) n1 cf xs H (τ - pre.length) := by
  unfold posP; rw [if_neg (Nat.not_lt_of_le hτ)]

/-- A prefix query after the first reads the one before. -/
theorem posP_prev_pre (K : Nat) (inner : Nat → Nat → Nat) (z : Nat) (pre : List Nat) (n1 : Nat) (cf : Nat → Nat)
    (xs : List Nat) (H : Nat) {i : Nat} (h1 : 1 ≤ i) (hi : i < pre.length) :
    posP K inner z pre n1 cf xs H i = inner (rget K (posP K inner z pre n1 cf xs H (i - 1)) H) (pre.getD i 0) := by
  rw [posP_pre K inner z pre n1 cf xs H hi, posP_pre K inner z pre n1 cf xs H (by omega)]
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  rfl

/-- The state after the prefix is its last answer. -/
theorem ivP_last (K : Nat) (inner : Nat → Nat → Nat) (z : Nat) (pre : List Nat) (n1 : Nat) (cf : Nat → Nat)
    (xs : List Nat) (H : Nat) (hm : 0 < pre.length) :
    ivP K inner z pre H = rget K (posP K inner z pre n1 cf xs H (pre.length - 1)) H := by
  rw [posP_pre K inner z pre n1 cf xs H (by omega)]
  unfold ivP
  conv => lhs; rw [← Nat.sub_add_cancel hm]
  rfl

/-- A chain's first query. -/
theorem posP_first (K : Nat) (inner : Nat → Nat → Nat) (z : Nat) (pre : List Nat) {n1 : Nat} (hn1 : 0 < n1)
    (cf : Nat → Nat) (xs : List Nat) (H c : Nat) (hc : c < n1) :
    posP K inner z pre n1 cf xs H (pre.length + c) = inner (ivP K inner z pre H) (cf c) := by
  rw [posP_chain K inner z pre n1 cf xs H _ (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
  have := posS_step K inner (ivP K inner z pre H) hn1 cf xs H 0 c hc
  rw [Nat.zero_mul, Nat.zero_add] at this; exact this

/-- A chain's later query reads its previous one. -/
theorem posP_prev (K : Nat) (inner : Nat → Nat → Nat) (z : Nat) (pre : List Nat) {n1 : Nat} (hn1 : 0 < n1)
    (cf : Nat → Nat) (xs : List Nat) (H T : Nat) (hT : pre.length + n1 ≤ T) :
    posP K inner z pre n1 cf xs H T = inner (rget K (posP K inner z pre n1 cf xs H (T - n1)) H)
      (xs.getD ((T - pre.length) / n1 - 1) 0) := by
  rw [posP_chain K inner z pre n1 cf xs H _ (by omega), posP_chain K inner z pre n1 cf xs H _ (by omega)]
  generalize hu : T - pre.length = u
  have hu' : T - n1 - pre.length = u - n1 := by omega
  rw [hu']
  have hT' : n1 ≤ u := by omega
  have hj := Nat.mod_lt u hn1
  have hq : 1 ≤ u / n1 := (Nat.le_div_iff_mul_le hn1).2 (by rw [Nat.one_mul]; exact hT')
  have hdm : u = u / n1 * n1 + u % n1 := by rw [Nat.mul_comm]; exact (Nat.div_add_mod u n1).symm
  have e1 : u = (u / n1 - 1 + 1) * n1 + u % n1 := by rw [Nat.sub_add_cancel hq]; exact hdm
  have e2 : u - n1 = (u / n1 - 1) * n1 + u % n1 := by
    have hge : n1 ≤ u / n1 * n1 := by
      calc n1 = 1 * n1 := (Nat.one_mul _).symm
        _ ≤ u / n1 * n1 := Nat.mul_le_mul_right _ hq
    rw [Nat.sub_mul, Nat.one_mul]; omega
  rw [e2]; conv => lhs; rw [e1]
  exact posS_next K inner _ hn1 cf xs H _ _ hj

/-- **`labR_finalU` with a root label**: `t` chains and one more label `t`
    (the prefix's); if every chain makes a query at one position `p`
    before `Tend`, then `t ≤` the fresh near queries `+ 1 +` the unpaid
    merges, the root's label left out. -/
theorem labR_finalR (t : Nat) (pos ch kap : Nat → Nat) (unp : Nat → Bool) {Kc : Nat} (hch : ∀ τ, ch τ < t + 1)
    (hkap : ∀ τ, kap τ < Kc) (hkp : ∀ τ τ', pos τ = pos τ' → kap τ = kap τ')
    (Tend p : Nat) (hprev : ∀ T τ0, T < Tend → τ0 < T → pos τ0 = pos T → labR pos ch T (ch T) ≠ labR pos ch T (ch τ0) →
      unp T = false → ∃ τ1 τ2, τ1 < T ∧ τ2 < T ∧ labR pos ch T (ch τ1) = labR pos ch T (ch T) ∧
        labR pos ch T (ch τ2) = labR pos ch T (ch τ0) ∧ kap τ1 = kap τ2)
    (hall : ∀ j, j < t → ∃ τ, τ < Tend ∧ ch τ = j ∧ pos τ = p) :
    t ≤ sumTo Tend (fun τ => indB (nearInc pos kap τ)) + 1 + sumTo Tend (fun τ => indB (unp τ)) := by
  have hinv := labR_invU (t + 1) pos ch kap unp hch hkap hkp Tend hprev Tend (Nat.le_refl _)
  -- the labels present: the chains' common one, and the root's
  let lab := labR pos ch Tend
  have hc : dcount (t + 1) lab (fun _ => true) ≤ 2 := by
    have pt : ∀ v, v < t + 1 → indB (present (t + 1) lab (fun _ => true) v) ≤
        indB (present t lab (fun _ => true) v) + indB (decide (v = lab t)) := fun v _ => by
      cases h : present (t + 1) lab (fun _ => true) v
      · exact Nat.zero_le _
      · obtain ⟨j, hj, e⟩ := List.any_eq_true.1 h
        rw [Bool.true_and, beq_iff_eq] at e
        rcases Nat.lt_or_ge j t with hjt | hjt
        · have : present t lab (fun _ => true) v = true :=
            List.any_eq_true.2 ⟨j, List.mem_range.2 hjt, by rw [Bool.true_and]; exact beq_iff_eq.2 e⟩
          rw [this]; exact Nat.le_add_right _ _
        · have hj' : j = t := by have := List.mem_range.1 hj; omega
          rw [hj'] at e
          rw [decide_eq_true e.symm]; exact Nat.le_add_left _ _
    have h1' : sumTo (t + 1) (fun v => indB (present t lab (fun _ => true) v)) ≤ 1 := by
      refine sum_le_one (t + 1) (fun v v' _ _ h1 h2 => ?_)
      obtain ⟨j, hj, e⟩ := List.any_eq_true.1 h1
      obtain ⟨j', hj', e'⟩ := List.any_eq_true.1 h2
      rw [Bool.true_and, beq_iff_eq] at e e'
      obtain ⟨τ, hτ, c, pτ⟩ := hall j (List.mem_range.1 hj)
      obtain ⟨τ', hτ', c', pτ'⟩ := hall j' (List.mem_range.1 hj')
      rw [← e, ← e', ← c, ← c']
      exact labR_coh pos ch Tend τ τ' hτ hτ' (pτ.trans pτ'.symm)
    have h2 : sumTo (t + 1) (fun v => indB (decide (v = lab t))) ≤ 1 := (sumTo_indEq _ _).1
    have hmono := sumTo_mono (t + 1) pt
    rw [sumTo_add] at hmono
    unfold dcount
    omega
  have hc' : dcount (t + 1) (labR pos ch Tend) (fun _ => true) ≤ 2 := hc
  omega

/-- The label of query `τ`: the prefix's `n1`, chain `(τ - m) % n1` after. -/
def chP (m n1 τ : Nat) : Nat := if τ < m then n1 else (τ - m) % n1

/-- A chain's first query repeating an earlier position. -/
def unpA (K : Nat) (inner : Nat → Nat → Nat) (z : Nat) (pre : List Nat) (n1 : Nat) (cf : Nat → Nat) (xs : List Nat)
    (H T : Nat) : Bool :=
  decide (pre.length ≤ T) && decide (T < pre.length + n1) && oldB (posP K inner z pre n1 cf xs H) T

/-- A later query's first revisit of the prefix's first position. -/
def unpB (K : Nat) (inner : Nat → Nat → Nat) (z : Nat) (pre : List Nat) (n1 : Nat) (cf : Nat → Nat) (xs : List Nat)
    (H T : Nat) : Bool :=
  decide (pre.length + n1 ≤ T) && decide (0 < pre.length) &&
    (posP K inner z pre n1 cf xs H 0 == posP K inner z pre n1 cf xs H T) &&
    !((List.range T).any (fun τ => decide (pre.length + n1 ≤ τ) &&
      posP K inner z pre n1 cf xs H τ == posP K inner z pre n1 cf xs H T))

/-- The unpaid merges of the prefixed run: `unpA`, `unpB`, and a later
    query's first revisit of a chain's first position (`unpS` past the
    prefix). -/
def unpP (K : Nat) (inner : Nat → Nat → Nat) (z : Nat) (pre : List Nat) (n1 : Nat) (cf : Nat → Nat) (xs : List Nat)
    (H T : Nat) : Bool :=
  unpA K inner z pre n1 cf xs H T || unpB K inner z pre n1 cf xs H T ||
    (decide (pre.length ≤ T) && unpS K inner (ivP K inner z pre H) n1 cf xs H (T - pre.length))

/-- An indicator below a sum when it implies one of the summands. -/
theorem indB_le_sumTo_of {b : Bool} {q : Nat → Bool} {m : Nat} (h : b = true → ∃ i, i < m ∧ q i = true) :
    indB b ≤ sumTo m (fun i => indB (q i)) := by
  cases hb : b
  · exact Nat.zero_le _
  · obtain ⟨i, hi, hq⟩ := h hb
    refine Nat.le_trans (Nat.le_of_eq ?_) (le_sumTo (fun i => indB (q i)) m hi)
    rw [hq]

/-- **Unpaid merges of the prefixed run number at most `m + 2 L`.** -/
theorem unpP_count {K : Nat} (inner : Nat → Nat → Nat) (z : Nat) (pre : List Nat) {n1 : Nat} (hn1 : 0 < n1)
    (cf : Nat → Nat) (hd : ∀ iv a b, a < n1 → b < n1 → a ≠ b → inner iv (cf a) ≠ inner iv (cf b))
    (hdx : ∀ iv s s' x a b, a < n1 → b < n1 → inner s x = inner iv (cf a) → inner s' x = inner iv (cf b) → a = b)
    (xs : List Nat) (H L : Nat) :
    sumTo (pre.length + n1 * (L + 1)) (fun T => indB (unpP K inner z pre n1 cf xs H T)) ≤ pre.length + 2 * L := by
  let m := pre.length
  let pos := posP K inner z pre n1 cf xs H
  have hor : ∀ T, indB (unpP K inner z pre n1 cf xs H T) ≤ indB (unpA K inner z pre n1 cf xs H T) +
      indB (unpB K inner z pre n1 cf xs H T) +
      indB (decide (m ≤ T) && unpS K inner (ivP K inner z pre H) n1 cf xs H (T - m)) := fun T => by
    unfold unpP
    refine Nat.le_trans (indB_or_le _ _) (Nat.add_le_add_right (indB_or_le _ _) _)
  refine Nat.le_trans (sumTo_mono _ (fun T _ => hor T)) ?_
  rw [sumTo_add, sumTo_add]
  -- the chains' first queries repeat prefix positions, each at most once
  have hA : sumTo (m + n1 * (L + 1)) (fun T => indB (unpA K inner z pre n1 cf xs H T)) ≤ m := by
    have pt : ∀ T, indB (unpA K inner z pre n1 cf xs H T) ≤
        sumTo m (fun i => indB (decide (m ≤ T) && decide (T < m + n1) && (pos i == pos T))) := fun T => by
      refine indB_le_sumTo_of (fun h => ?_)
      unfold unpA at h
      rw [Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at h
      obtain ⟨⟨h1, h2⟩, ho⟩ := h
      obtain ⟨hf, ef⟩ := firstOld_spec _ ho
      refine ⟨firstOld pos T, ?_, ?_⟩
      · -- an earlier chain's first position is never this one
        refine Nat.lt_of_not_le (fun hge => ?_)
        obtain ⟨c, rfl⟩ : ∃ c, T = m + c := ⟨T - m, by omega⟩
        have hge' : m ≤ firstOld (posP K inner z pre n1 cf xs H) (m + c) := hge
        obtain ⟨c', hc'⟩ : ∃ c', firstOld (posP K inner z pre n1 cf xs H) (m + c) = m + c' :=
          ⟨firstOld (posP K inner z pre n1 cf xs H) (m + c) - m, by omega⟩
        have hcc : c' < c := by rw [hc'] at hf; omega
        have e := ef
        rw [hc'] at e
        change posP K inner z pre n1 cf xs H (pre.length + c') = posP K inner z pre n1 cf xs H (pre.length + c) at e
        rw [posP_first K inner z pre hn1 cf xs H c' (by omega), posP_first K inner z pre hn1 cf xs H c (by omega)] at e
        exact hd _ c' c (by omega) (by omega) (Nat.ne_of_lt hcc) e
      · rw [Bool.and_eq_true, Bool.and_eq_true]
        exact ⟨⟨decide_eq_true h1, decide_eq_true h2⟩, beq_iff_eq.2 ef⟩
    refine Nat.le_trans (sumTo_mono _ (fun T _ => pt T)) ?_
    rw [sumTo_exch]
    refine Nat.le_trans (sumTo_mono _ (fun i _ => sum_le_one (m + n1 * (L + 1)) (fun T T' _ _ h1 h2 => ?_)))
      (Nat.le_of_eq (Eq.trans (sumTo_const 1 m) (Nat.mul_one m)))
    rw [Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq, beq_iff_eq] at h1 h2
    obtain ⟨⟨a1, a2⟩, e1⟩ := h1
    obtain ⟨⟨b1, b2⟩, e2⟩ := h2
    obtain ⟨c, rfl⟩ : ∃ c, T = m + c := ⟨T - m, by omega⟩
    obtain ⟨c', rfl⟩ : ∃ c', T' = m + c' := ⟨T' - m, by omega⟩
    have e := e1.symm.trans e2
    change posP K inner z pre n1 cf xs H (pre.length + c) = posP K inner z pre n1 cf xs H (pre.length + c') at e
    rw [posP_first K inner z pre hn1 cf xs H c (by omega), posP_first K inner z pre hn1 cf xs H c' (by omega)] at e
    have := Decidable.byContradiction (fun hne : c ≠ c' => hd _ c c' (by omega) (by omega) hne e)
    rw [this]
  -- first revisits of the prefix's first position: one a step
  have hB : sumTo (m + n1 * (L + 1)) (fun T => indB (unpB K inner z pre n1 cf xs H T)) ≤ L := by
    rw [sumTo_app _ m, sumTo_split n1 _ (L + 1)]
    have z0 : sumTo m (fun T => indB (unpB K inner z pre n1 cf xs H T)) = 0 :=
      Eq.trans (sumTo_congr _ (fun T hT => by
        show indB (unpB K inner z pre n1 cf xs H T) = 0
        unfold unpB; rw [decide_eq_false (by omega)]; rfl)) (Eq.trans (sumTo_const 0 m) (Nat.mul_zero m))
    rw [z0, Nat.zero_add]
    refine sumTo_le_tail _ ?_ (fun q => ?_) L
    · refine Eq.trans (sumTo_congr _ (fun r hr => ?_)) (Eq.trans (sumTo_const 0 n1) (Nat.mul_zero n1))
      show indB (unpB K inner z pre n1 cf xs H (m + (r + n1 * 0))) = 0
      unfold unpB; rw [decide_eq_false (by omega)]; rfl
    · refine sum_le_one n1 (fun r r' hr hr' u u' => ?_)
      unfold unpB at u u'
      simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq, beq_iff_eq] at u u'
      obtain ⟨⟨⟨hq, _⟩, e⟩, hfirst⟩ := u
      obtain ⟨⟨⟨hq', _⟩, e'⟩, hfirst'⟩ := u'
      have hp : pos (m + (r + n1 * q)) = pos (m + (r' + n1 * q)) := e.symm.trans e'
      rcases Nat.lt_trichotomy r r' with h | h | h
      · exfalso
        refine List.any_eq_false.1 hfirst' (m + (r + n1 * q)) (List.mem_range.2 (by omega)) ?_
        rw [Bool.and_eq_true]; exact ⟨decide_eq_true hq, beq_iff_eq.2 hp⟩
      · exact h
      · exfalso
        refine List.any_eq_false.1 hfirst (m + (r' + n1 * q)) (List.mem_range.2 (by omega)) ?_
        rw [Bool.and_eq_true]; exact ⟨decide_eq_true hq', beq_iff_eq.2 hp.symm⟩
  -- first revisits of chains' first positions: `unpS_count` past the prefix
  have hC : sumTo (m + n1 * (L + 1)) (fun T => indB (decide (m ≤ T) &&
      unpS K inner (ivP K inner z pre H) n1 cf xs H (T - m))) ≤ L := by
    rw [sumTo_app _ m]
    have z0 : sumTo m (fun T => indB (decide (m ≤ T) && unpS K inner (ivP K inner z pre H) n1 cf xs H (T - m))) = 0 :=
      Eq.trans (sumTo_congr _ (fun T hT => by rw [decide_eq_false (by omega)]; rfl))
        (Eq.trans (sumTo_const 0 m) (Nat.mul_zero m))
    rw [z0, Nat.zero_add]
    refine Nat.le_trans (Nat.le_of_eq (sumTo_congr _ (fun u _ => ?_)))
      (unpS_count (K := K) inner (ivP K inner z pre H) hn1 cf (hdx (ivP K inner z pre H)) xs H L)
    show indB (decide (m ≤ m + u) && unpS K inner (ivP K inner z pre H) n1 cf xs H (m + u - m)) = _
    rw [decide_eq_true (Nat.le_add_right m u), Bool.true_and, Nat.add_sub_cancel_left]
  have h2 : pre.length + 2 * L = m + L + L := by show m + 2 * L = m + L + L; omega
  rw [h2]
  exact Nat.add_le_add (Nat.add_le_add hA hB) hC

/-- **Chains after a public prefix that all meet saw near-collisions**:
    the prefix's `m` queries from `z`, then `n1` chains from its last
    answer, distinct first positions from any state (`hd`), each block
    sending at most one first commitment's position (`hdx`).  The prefix
    carries a label of its own; a revisit of a prefix position after the
    first is paid by the prefix's previous answer, and the unpaid merges
    number at most `m + 2 L` (`unpP_count`). -/
theorem allMeet_nearP {K Kc : Nat} (inner : Nat → Nat → Nat) (hin : ∀ s x, inner s x < K) (κ : Nat → Nat)
    (hκ : ∀ u, κ u < Kc) (hpk2 : ∀ s s' x x', inner s x = inner s' x' → κ s = κ s') (z : Nat) (pre : List Nat)
    {n1 : Nat} (hn1 : 0 < n1) (cf : Nat → Nat)
    (hd : ∀ iv a b, a < n1 → b < n1 → a ≠ b → inner iv (cf a) ≠ inner iv (cf b))
    (hdx : ∀ iv s s' x a b, a < n1 → b < n1 → inner s x = inner iv (cf a) → inner s' x = inner iv (cf b) → a = b)
    (xs : List Nat) {H : Nat} (hP : permB K H = true) (L : Nat)
    {v : Nat} (hall : ∀ j, j < n1 → chain1 K inner (ivP K inner z pre H) (cf j :: xs) H (L + 1) = v) :
    n1 ≤ 1 + (pre.length + 2 * L) +
      nearN K (fun a b => decide (κ a = κ b)) (runAdp K (nxtP inner z pre n1 cf xs) H (pre.length + n1 * (L + 1))) := by
  have hK : 0 < K := Nat.lt_of_le_of_lt (Nat.zero_le _) (hin 0 0)
  let m := pre.length
  let pos := posP K inner z pre n1 cf xs H
  let kap := fun τ => κ (rget K (pos τ) H)
  let ch := chP m n1
  have chC : ∀ τ, m ≤ τ → ch τ = (τ - m) % n1 := fun τ h => by
    show (if τ < m then n1 else (τ - m) % n1) = _; rw [if_neg (Nat.not_lt_of_le h)]
  have chR : ∀ τ, τ < m → ch τ = n1 := fun τ h => by
    show (if τ < m then n1 else (τ - m) % n1) = _; rw [if_pos h]
  have chm : ∀ τ, m + n1 ≤ τ → ch (τ - n1) = ch τ := fun τ h => by
    rw [chC _ (by omega), chC _ (by omega)]
    have : τ - n1 - m + n1 = τ - m := by omega
    conv => rhs; rw [← this]
    rw [Nat.add_mod_right]
  have prev : ∀ T, m + n1 ≤ T → pos T = inner (rget K (pos (T - n1)) H) (xs.getD ((T - m) / n1 - 1) 0) :=
    fun T h => posP_prev K inner z pre hn1 cf xs H T h
  -- `T`'s predecessor shares its projection with `τ`'s when their positions agree
  have kpay : ∀ T τ, m + n1 ≤ T → m + n1 ≤ τ → pos τ = pos T → kap (T - n1) = kap (τ - n1) := fun T τ hT hτ e => by
    show κ (rget K (pos (T - n1)) H) = κ (rget K (pos (τ - n1)) H)
    rw [prev T hT, prev τ hτ] at e
    exact (hpk2 _ _ _ _ e).symm
  have hpos : ∀ τ, pos τ < K := fun τ => by
    show posP K inner z pre n1 cf xs H τ < K
    unfold posP; split
    · exact hin _ _
    · exact hin _ _
  have hfin := labR_finalR n1 pos ch kap (unpP K inner z pre n1 cf xs H)
    (fun τ => by
      show (if τ < m then n1 else (τ - m) % n1) < n1 + 1
      split
      · exact Nat.lt_succ_self _
      · exact Nat.lt_succ_of_lt (Nat.mod_lt _ hn1))
    (fun τ => hκ _)
    (fun τ τ' e => by show κ (rget K (pos τ) H) = κ (rget K (pos τ') H); rw [e])
    (m + n1 * (L + 1)) (pos (m + L * n1))
    (fun T τ0 hT hτ0 e hab hu => by
      have hu' : unpA K inner z pre n1 cf xs H T = false ∧ unpB K inner z pre n1 cf xs H T = false ∧
          (decide (pre.length ≤ T) && unpS K inner (ivP K inner z pre H) n1 cf xs H (T - pre.length)) = false := by
        unfold unpP at hu
        simp only [Bool.or_eq_false_iff] at hu
        exact ⟨hu.1.1, hu.1.2, hu.2⟩
      obtain ⟨hA, hB, hC⟩ := hu'
      rcases Nat.lt_or_ge T m with hTm | hTm
      · exfalso; exact hab (by rw [chR T hTm, chR τ0 (by omega)])
      rcases Nat.lt_or_ge T (m + n1) with hT1 | hT1
      · exfalso
        unfold unpA at hA
        rw [decide_eq_true hTm, decide_eq_true hT1, Bool.true_and, Bool.true_and,
          oldB_spec _ hτ0 e] at hA
        exact Bool.noConfusion hA
      -- `T` a later query: its predecessor is `T - n1`
      have c1 : labR pos ch T (ch (T - n1)) = labR pos ch T (ch T) := by rw [chm T hT1]
      -- an earlier later query at `T`'s position, when `T`'s first revisit is excluded
      have earlier : ∀ (hex : (List.range T).any (fun τ => decide (m + n1 ≤ τ) && pos τ == pos T) = true),
          ∃ τ1 τ2, τ1 < T ∧ τ2 < T ∧ labR pos ch T (ch τ1) = labR pos ch T (ch T) ∧
            labR pos ch T (ch τ2) = labR pos ch T (ch τ0) ∧ kap τ1 = kap τ2 := fun hex => by
        obtain ⟨τ', hτ'm, hτ'⟩ := List.any_eq_true.1 hex
        rw [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hτ'
        obtain ⟨h2, e2⟩ := hτ'
        have hτ'T := List.mem_range.1 hτ'm
        refine ⟨T - n1, τ' - n1, by omega, by omega, c1, ?_, kpay T τ' hT1 h2 e2⟩
        rw [chm τ' h2]
        exact labR_coh pos ch T τ' τ0 hτ'T hτ0 (e2.trans e.symm)
      rcases Nat.lt_or_ge τ0 m with h0 | h0
      · -- a prefix position
        rcases Nat.eq_zero_or_pos τ0 with hz | hz
        · -- the prefix's first: an earlier later query revisited it
          subst hz
          unfold unpB at hB
          rw [decide_eq_true hT1, decide_eq_true (show 0 < pre.length by omega), Bool.true_and, Bool.true_and,
            show (posP K inner z pre n1 cf xs H 0 == posP K inner z pre n1 cf xs H T) = true from beq_iff_eq.2 e,
            Bool.true_and, Bool.not_eq_false'] at hB
          exact earlier hB
        · -- a later prefix position: paid by the prefix's previous answer
          refine ⟨T - n1, τ0 - 1, by omega, by omega, c1, by rw [chR _ (by omega), chR τ0 h0], ?_⟩
          show κ (rget K (pos (T - n1)) H) = κ (rget K (pos (τ0 - 1)) H)
          have ee := e
          change posP K inner z pre n1 cf xs H τ0 = pos T at ee
          rw [posP_prev_pre K inner z pre n1 cf xs H hz h0, prev T hT1] at ee
          exact (hpk2 _ _ _ _ ee).symm
      rcases Nat.lt_or_ge τ0 (m + n1) with h1 | h1
      · -- a chain's first position: an earlier later query revisited it
        rw [decide_eq_true hTm, Bool.true_and] at hC
        unfold unpS at hC
        have hu1 : decide (n1 ≤ T - pre.length) = true := decide_eq_true (by omega)
        have hfp : (List.range n1).any (fun c => posS K inner (ivP K inner z pre H) n1 cf xs H c ==
            posS K inner (ivP K inner z pre H) n1 cf xs H (T - pre.length)) = true := by
          refine List.any_eq_true.2 ⟨τ0 - m, List.mem_range.2 (by omega), beq_iff_eq.2 ?_⟩
          have e' := e
          change posP K inner z pre n1 cf xs H τ0 = posP K inner z pre n1 cf xs H T at e'
          rw [posP_chain K inner z pre n1 cf xs H _ (by omega), posP_chain K inner z pre n1 cf xs H _ (by omega)] at e'
          exact e'
        rw [hu1, hfp, Bool.true_and, Bool.true_and, Bool.not_eq_false'] at hC
        obtain ⟨u', hu'm, hu'⟩ := List.any_eq_true.1 hC
        rw [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hu'
        refine earlier (List.any_eq_true.2 ⟨m + u', List.mem_range.2 (by have := List.mem_range.1 hu'm; omega), ?_⟩)
        rw [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
        refine ⟨by omega, ?_⟩
        change posP K inner z pre n1 cf xs H (pre.length + u') = posP K inner z pre n1 cf xs H T
        rw [posP_chain K inner z pre n1 cf xs H _ (by omega), posP_chain K inner z pre n1 cf xs H T (by omega),
          Nat.add_sub_cancel_left]
        exact hu'.2
      · -- a later chain position: paid by both predecessors
        exact ⟨T - n1, τ0 - n1, by omega, by omega, c1, by rw [chm τ0 h1], kpay T τ0 hT1 h1 e⟩)
    (fun j hj => ⟨m + (L * n1 + j), by
      calc m + (L * n1 + j) < m + (L * n1 + n1) := by omega
        _ = m + n1 * (L + 1) := by rw [Nat.mul_comm n1, Nat.succ_mul],
      by rw [chC _ (Nat.le_add_right _ _), Nat.add_sub_cancel_left, Nat.add_comm, Nat.add_mul_mod_self_right,
        Nat.mod_eq_of_lt hj], by
      refine permB_inj hP (hpos _) (hpos _) ?_
      show rget K (posP K inner z pre n1 cf xs H (pre.length + (L * n1 + j))) H =
        rget K (posP K inner z pre n1 cf xs H (pre.length + L * n1)) H
      rw [posP_chain K inner z pre n1 cf xs H _ (Nat.le_add_right _ _), posP_chain K inner z pre n1 cf xs H _
        (Nat.le_add_right _ _), Nat.add_sub_cancel_left, Nat.add_sub_cancel_left, rget_posS, rget_posS]
      have a1 : (L * n1 + j) % n1 = j := by rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]
      have a2 : (L * n1 + j) / n1 = L := by rw [Nat.add_comm, Nat.add_mul_div_right _ _ hn1, Nat.div_eq_of_lt hj, Nat.zero_add]
      have b1 : (L * n1) % n1 = 0 := Nat.mul_mod_left _ _
      have b2 : (L * n1) / n1 = L := Nat.mul_div_cancel _ hn1
      rw [a1, a2, b1, b2, hall j hj, hall 0 hn1]⟩)
  have hU : sumTo (m + n1 * (L + 1)) (fun T => indB (unpP K inner z pre n1 cf xs H T)) ≤ m + 2 * L :=
    unpP_count (K := K) inner z pre hn1 cf hd hdx xs H L
  rw [nearN_runP hK inner κ z pre hn1 cf xs H]
  show n1 ≤ 1 + (pre.length + 2 * L) + sumTo (m + n1 * (L + 1)) (fun τ => indB (nearInc pos kap τ))
  omega

/-- **Chains after a prefix that all meet are rare**: `n1` chains after
    the `m`-block prefix all reach one state after `L + 1` absorptions on
    at most `((0 + ⋯ + (k - 1)) F)^e / (e! (K - k)^e)` of the permutation
    tables, `k = m + n1 (L+1)` queries, `e = n1 - 1 - (m + 2 L)`
    (`allMeet_nearP`, `nearN_tail`). -/
theorem allMeet_countPP {K Kc F : Nat} (hK : 0 < K) (inner : Nat → Nat → Nat) (hin : ∀ s x, inner s x < K) (κ : Nat → Nat)
    (hκ : ∀ u, κ u < Kc) (hF : ∀ v, sumTo K (fun u => indB (decide (κ u = v))) ≤ F)
    (hpk2 : ∀ s s' x x', inner s x = inner s' x' → κ s = κ s') (z : Nat) (pre : List Nat) {n1 : Nat} (hn1 : 0 < n1)
    (cf : Nat → Nat) (hd : ∀ iv a b, a < n1 → b < n1 → a ≠ b → inner iv (cf a) ≠ inner iv (cf b)) (xs : List Nat) (L : Nat)
    (hdx : ∀ iv s s' x a b, a < n1 → b < n1 → inner s x = inner iv (cf a) → inner s' x = inner iv (cf b) → a = b) :
    fact (n1 - 1 - (pre.length + 2 * L)) * ((K - (pre.length + n1 * (L + 1))) ^ (n1 - 1 - (pre.length + 2 * L)) * sumTo (K ^ K) (fun H => indB (permB K H &&
        (List.range n1).all (fun j => chain1 K inner (ivP K inner z pre H) (cf j :: xs) H (L + 1) == chain1 K inner (ivP K inner z pre H) (cf 0 :: xs) H (L + 1))))) ≤
      (sumTo ((pre.length + n1 * (L + 1))) (fun j => j) * F) ^ (n1 - 1 - (pre.length + 2 * L)) * sumTo (K ^ K) (fun H => indB (permB K H)) := by
  have hnx : ∀ l, nxtP inner z pre n1 cf xs l < K := fun l => by unfold nxtP nxtS; split <;> (try split) <;> exact hin _ _
  refine Nat.le_trans (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (sumTo_mono _ (fun H _ => ?_))))
    (nearN_tail hK (fun a b => decide (κ a = κ b)) (rel_symm κ) (fib_rel κ hF) (nxtP inner z pre n1 cf xs) hnx ((pre.length + n1 * (L + 1))) (n1 - 1 - (pre.length + 2 * L)))
  cases hP : permB K H
  · exact Nat.zero_le _
  cases ha : (List.range n1).all (fun j => chain1 K inner (ivP K inner z pre H) (cf j :: xs) H (L + 1) == chain1 K inner (ivP K inner z pre H) (cf 0 :: xs) H (L + 1))
  · exact Nat.zero_le _
  · have hall : ∀ j, j < n1 → chain1 K inner (ivP K inner z pre H) (cf j :: xs) H (L + 1) = chain1 K inner (ivP K inner z pre H) (cf 0 :: xs) H (L + 1) :=
      fun j hj => beq_iff_eq.1 (List.all_eq_true.1 ha j (List.mem_range.2 hj))
    have hm := allMeet_nearP inner hin κ hκ hpk2 z pre hn1 cf hd hdx xs hP L hall
    have : n1 - 1 - (pre.length + 2 * L) ≤ nearN K (fun a b => decide (κ a = κ b)) (runAdp K (nxtP inner z pre n1 cf xs) H ((pre.length + n1 * (L + 1)))) := by omega
    rw [decide_eq_true this]; exact Nat.le_refl _

/-- **Meeting tuples after a prefix, averaged**: `e! (K - k)^e` times the
    summed `meetM` from the prefix's state is at most `n1^t ((0 + ⋯ +
    (k - 1)) F)^e` per permutation table, `k = m + t (L+1)`,
    `e = t - 1 - (m + 2 L)`. -/
theorem meetM_countPP {K Kc F : Nat} (hK : 0 < K) (inner : Nat → Nat → Nat) (hin : ∀ s x, inner s x < K) (κ : Nat → Nat)
    (hκ : ∀ u, κ u < Kc) (hF : ∀ v, sumTo K (fun u => indB (decide (κ u = v))) ≤ F)
    (hpk2 : ∀ s s' x x', inner s x = inner s' x' → κ s = κ s') (z : Nat) (pre : List Nat) {n1 : Nat} (hn : 0 < n1)
    (hd : ∀ iv a b, a < n1 → b < n1 → a ≠ b → inner iv a ≠ inner iv b) (xs : List Nat) (L : Nat)
    (hdxC : ∀ iv s s' x c c', c < n1 → c' < n1 → inner s x = inner iv c → inner s' x = inner iv c' → c = c')
    {t : Nat} (ht : 0 < t) :
    fact (t - 1 - (pre.length + 2 * L)) * ((K - (pre.length + t * (L + 1))) ^ (t - 1 - (pre.length + 2 * L)) * sumTo (K ^ K) (fun H => indB (permB K H) * meetM K inner (ivP K inner z pre H) n1 xs L t H)) ≤
      n1 ^ t * ((sumTo ((pre.length + t * (L + 1))) (fun j => j) * F) ^ (t - 1 - (pre.length + 2 * L)) * sumTo (K ^ K) (fun H => indB (permB K H))) := by
  have e : sumTo (K ^ K) (fun H => indB (permB K H) * meetM K inner (ivP K inner z pre H) n1 xs L t H) =
      sumTo (n1 ^ t) (fun a => sumTo (K ^ K) (fun H => indB (permB K H) * indB (injT n1 t a &&
        (List.range t).all (fun j => chain1 K inner (ivP K inner z pre H) (rget n1 j a :: xs) H (L + 1) ==
          chain1 K inner (ivP K inner z pre H) (rget n1 0 a :: xs) H (L + 1))))) := by
    unfold meetM
    rw [sumTo_congr _ (fun H _ => sumTo_mul _ _ _)]
    exact sumTo_exch _ (n1 ^ t) (K ^ K)
  rw [e, sumTo_mul, sumTo_mul]
  refine Nat.le_trans (sumTo_mono _ (fun a _ => ?_)) (Nat.le_of_eq (sumTo_const _ (n1 ^ t)))
  cases hi : injT n1 t a
  · have z : ∀ H, indB (permB K H) * indB (false && (List.range t).all (fun j => chain1 K inner (ivP K inner z pre H) (rget n1 j a :: xs) H (L + 1) ==
        chain1 K inner (ivP K inner z pre H) (rget n1 0 a :: xs) H (L + 1))) = 0 := fun H => by rw [Bool.false_and]; exact Nat.mul_zero _
    rw [sumTo_congr _ (fun H _ => z H), sumTo_const, Nat.mul_zero, Nat.mul_zero, Nat.mul_zero]; exact Nat.zero_le _
  · have hdT : ∀ iv i j, i < t → j < t → i ≠ j → inner iv (rget n1 i a) ≠ inner iv (rget n1 j a) := fun iv i j hi' hj hij =>
      hd iv _ _ (rget_lt hn _ _) (rget_lt hn _ _) (injT_ne hn t a hi i j hi' hj hij)
    have hdxT : ∀ iv s s' x i j, i < t → j < t → inner s x = inner iv (rget n1 i a) → inner s' x = inner iv (rget n1 j a) →
        i = j := fun iv s s' x i j hi' hj e1 e2 =>
      Decidable.byContradiction (fun hij => injT_ne hn t a hi i j hi' hj hij
        (hdxC iv s s' x _ _ (rget_lt hn _ _) (rget_lt hn _ _) e1 e2))
    have hc := allMeet_countPP hK inner hin κ hκ hF hpk2 z pre ht (fun j => rget n1 j a) hdT xs L hdxT
    refine Nat.le_trans (Nat.le_of_eq ?_) hc
    congr 2
    refine sumTo_congr _ (fun H _ => ?_)
    rw [Bool.true_and, indB_and']


/-- The tuple load for every later transcript. -/
def loadTP (K : Nat) (inner : Nat → Nat → Nat) (z : Nat) (pre : List Nat) (n1 : Nat) (X L t s0 H : Nat) : Nat :=
  (s0 - 1) + n1 * sumTo (X ^ L) (fun i => indB (decide (ffac s0 t ≤ meetM K inner (ivP K inner z pre H) n1 (xsOf X L i) L t H)))

theorem preimage_loadTP (K : Nat) (inner : Nat → Nat → Nat) (z : Nat) (pre : List Nat) {n1 : Nat} (hn : 0 < n1)
    {X : Nat} (hX : 0 < X) (L t s0 : Nat) (xs : List Nat) (hxs : ∀ m, m < L → xs.getD m 0 < X)
    (H v : Nat) :
    sumTo n1 (fun c => indB (decide (chain1 K inner (ivP K inner z pre H) (c :: xs) H (L + 1) = v))) ≤ loadTP K inner z pre n1 X L t s0 H := by
  obtain ⟨i, hi, hag⟩ := xsOf_cover hX xs hxs
  have hch : ∀ c, chain1 K inner (ivP K inner z pre H) (c :: xs) H (L + 1) = chain1 K inner (ivP K inner z pre H) (c :: xsOf X L i) H (L + 1) :=
    fun c => chain1_congr K inner (ivP K inner z pre H) _ _ H (L + 1) (fun j hj => by
      cases j with
      | zero => rfl
      | succ j => exact hag j (Nat.lt_of_succ_lt_succ hj))
  rw [sumTo_congr _ (fun c _ => by rw [hch c])]
  refine Nat.le_trans (preimage_loadT K inner (ivP K inner z pre H) hn (xsOf X L i) L t s0 H v) ?_
  unfold loadT loadTP
  exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (le_sumTo (fun i => indB
    (decide (ffac s0 t ≤ meetM K inner (ivP K inner z pre H) n1 (xsOf X L i) L t H))) _ hi)) _

/-- **Markov for meeting tuples**: per later block list. -/
theorem meet_markovP {K Kc F : Nat} (hK : 0 < K) (inner : Nat → Nat → Nat) (hin : ∀ s x, inner s x < K) (κ : Nat → Nat)
    (hκ : ∀ u, κ u < Kc) (hF : ∀ v, sumTo K (fun u => indB (decide (κ u = v))) ≤ F)
    (hpk2 : ∀ s s' x x', inner s x = inner s' x' → κ s = κ s') (z : Nat) (pre : List Nat) {n1 : Nat} (hn : 0 < n1)
    (hd : ∀ iv a b, a < n1 → b < n1 → a ≠ b → inner iv a ≠ inner iv b) (xs : List Nat) (L : Nat)
    (hdxC : ∀ iv s s' x c c', c < n1 → c' < n1 → inner s x = inner iv c → inner s' x = inner iv c' → c = c')
    {t : Nat} (ht : 0 < t) (s0 : Nat) :
    fact (t - 1 - (pre.length + 2 * L)) * (K - (pre.length + t * (L + 1))) ^ (t - 1 - (pre.length + 2 * L)) * (ffac s0 t * sumTo (K ^ K) (fun H =>
        indB (permB K H && decide (ffac s0 t ≤ meetM K inner (ivP K inner z pre H) n1 xs L t H)))) ≤
      n1 ^ t * (sumTo ((pre.length + t * (L + 1))) (fun j => j) * F) ^ (t - 1 - (pre.length + 2 * L)) * sumTo (K ^ K) (fun H => indB (permB K H)) := by
  have hm0 := meetM_countPP hK inner hin κ hκ hF hpk2 z pre hn hd xs L hdxC ht
  have mk : ffac s0 t * sumTo (K ^ K) (fun H => indB (permB K H && decide (ffac s0 t ≤ meetM K inner (ivP K inner z pre H) n1 xs L t H))) ≤
      sumTo (K ^ K) (fun H => indB (permB K H) * meetM K inner (ivP K inner z pre H) n1 xs L t H) := by
    rw [sumTo_mul]
    refine sumTo_mono _ (fun H _ => ?_)
    cases permB K H
    · simp [indB]
    · by_cases h : ffac s0 t ≤ meetM K inner (ivP K inner z pre H) n1 xs L t H
      · rw [decide_eq_true h]; simp only [Bool.true_and, show indB true = 1 from rfl, Nat.mul_one, Nat.one_mul]; exact h
      · rw [decide_eq_false h]; simp [indB]
  calc fact (t - 1 - (pre.length + 2 * L)) * (K - (pre.length + t * (L + 1))) ^ (t - 1 - (pre.length + 2 * L)) * (ffac s0 t * sumTo (K ^ K) (fun H =>
        indB (permB K H && decide (ffac s0 t ≤ meetM K inner (ivP K inner z pre H) n1 xs L t H))))
      ≤ fact (t - 1 - (pre.length + 2 * L)) * (K - (pre.length + t * (L + 1))) ^ (t - 1 - (pre.length + 2 * L)) * sumTo (K ^ K) (fun H => indB (permB K H) * meetM K inner (ivP K inner z pre H) n1 xs L t H) :=
        Nat.mul_le_mul_left _ mk
    _ = fact (t - 1 - (pre.length + 2 * L)) * ((K - (pre.length + t * (L + 1))) ^ (t - 1 - (pre.length + 2 * L)) * sumTo (K ^ K) (fun H => indB (permB K H) * meetM K inner (ivP K inner z pre H) n1 xs L t H)) :=
        Nat.mul_assoc _ _ _
    _ ≤ _ := by rw [Nat.mul_assoc (n1 ^ t)]; exact hm0

/-- **The tuple load after a prefix, averaged**: `k = m + t (L+1)`,
    `e = t - 1 - (m + 2 L)`, `Q = e! (K - k)^e`, `f = s0 (s0-1) ⋯ (s0-t+1)`;
    `Q f` times the summed `loadTP` is at most
    `Q f (s0 - 1) + n1 X^L n1^t ((0 + ⋯ + (k - 1)) F)^e` per permutation
    table. -/
theorem loadTP_countP {K Kc F : Nat} (hK : 0 < K) (inner : Nat → Nat → Nat) (hin : ∀ s x, inner s x < K) (κ : Nat → Nat)
    (hκ : ∀ u, κ u < Kc) (hF : ∀ v, sumTo K (fun u => indB (decide (κ u = v))) ≤ F)
    (hpk2 : ∀ s s' x x', inner s x = inner s' x' → κ s = κ s') (z : Nat) (pre : List Nat) {n1 : Nat} (hn : 0 < n1)
    (hd : ∀ iv a b, a < n1 → b < n1 → a ≠ b → inner iv a ≠ inner iv b)
    (hdxC : ∀ iv s s' x c c', c < n1 → c' < n1 → inner s x = inner iv c → inner s' x = inner iv c' → c = c') (X L : Nat) {t : Nat} (ht : 0 < t) (s0 : Nat) :
    fact (t - 1 - (pre.length + 2 * L)) * (K - (pre.length + t * (L + 1))) ^ (t - 1 - (pre.length + 2 * L)) * ffac s0 t * sumTo (K ^ K) (fun H => indB (permB K H) * loadTP K inner z pre n1 X L t s0 H) ≤
      (fact (t - 1 - (pre.length + 2 * L)) * (K - (pre.length + t * (L + 1))) ^ (t - 1 - (pre.length + 2 * L)) * ffac s0 t * (s0 - 1) +
        n1 * (X ^ L * (n1 ^ t * (sumTo ((pre.length + t * (L + 1))) (fun j => j) * F) ^ (t - 1 - (pre.length + 2 * L))))) * sumTo (K ^ K) (fun H => indB (permB K H)) := by
  let bad := fun i H => indB (permB K H && decide (ffac s0 t ≤ meetM K inner (ivP K inner z pre H) n1 (xsOf X L i) L t H))
  have each : ∀ i, fact (t - 1 - (pre.length + 2 * L)) * (K - (pre.length + t * (L + 1))) ^ (t - 1 - (pre.length + 2 * L)) * (ffac s0 t * sumTo (K ^ K) (fun H => bad i H)) ≤
      n1 ^ t * (sumTo ((pre.length + t * (L + 1))) (fun j => j) * F) ^ (t - 1 - (pre.length + 2 * L)) * sumTo (K ^ K) (fun H => indB (permB K H)) :=
    fun i => meet_markovP hK inner hin κ hκ hF hpk2 z pre hn hd (xsOf X L i) L hdxC ht s0
  have e : ∀ H, indB (permB K H) * loadTP K inner z pre n1 X L t s0 H = indB (permB K H) * (s0 - 1) +
      n1 * sumTo (X ^ L) (fun i => bad i H) := fun H => by
    unfold loadTP
    rw [Nat.mul_add, Nat.mul_left_comm, sumTo_mul]
    congr 2
    exact sumTo_congr _ (fun i _ => indB_and' _ _)
  have e2 : sumTo (K ^ K) (fun H => indB (permB K H) * (s0 - 1)) = (s0 - 1) * sumTo (K ^ K) (fun H => indB (permB K H)) := by
    rw [sumTo_mul]; exact sumTo_congr _ (fun H _ => Nat.mul_comm _ _)
  rw [sumTo_congr _ (fun H _ => e H), sumTo_add, e2, ← sumTo_mul, sumTo_exch _ (X ^ L) (K ^ K)]
  generalize hPi : sumTo (K ^ K) (fun H => indB (permB K H)) = Pi0 at *
  generalize hQ : fact (t - 1 - (pre.length + 2 * L)) * (K - (pre.length + t * (L + 1))) ^ (t - 1 - (pre.length + 2 * L)) = Q at *
  generalize hW : n1 ^ t * (sumTo ((pre.length + t * (L + 1))) (fun j => j) * F) ^ (t - 1 - (pre.length + 2 * L)) = W at *
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
    absorptions after a prefix**: the index `φ m w` the state after the
    prefix, the first commitment `m % n1` and the later blocks
    `enc (m / n1) w`, each below `X`; the table's `δs' = δs loadTP` meets `hsp1` and
    `hφsp` for every `d`, `rest`, `w` and `v` (`s0 ≥ 2`). -/
theorem loadTP_hsp {D W : Type} {K NS1 n1 δs X : Nat} (inner : Nat → Nat → Nat) (z : Nat) (pre : List Nat) (hX : 0 < X) (L t : Nat)
    (enc : Nat → W → List Nat) (henc : ∀ r w i, i < L → (enc r w).getD i 0 < X)
    (Com1 : D → Nat → Nat) (hr1 : ∀ d σ, Com1 d σ < n1)
    (hsp1 : ∀ d v, sumTo NS1 (fun σ => indB (decide (Com1 d σ = v))) ≤ δs) {s0 : Nat} (hs0 : 2 ≤ s0) (H : Nat) :
    (∀ d v, sumTo NS1 (fun σ => indB (decide (Com1 d σ = v))) ≤ δs * loadTP K inner z pre n1 X L t s0 H) ∧
      (∀ d rest w v, sumTo NS1 (fun σ1 => indB (decide
        ((fun m' w => chain1 K inner (ivP K inner z pre H) ((m' % n1) :: enc (m' / n1) w) H (L + 1)) (Com1 d σ1 + n1 * rest) w = v))) ≤
        δs * loadTP K inner z pre n1 X L t s0 H) := by
  have h1 : 1 ≤ loadTP K inner z pre n1 X L t s0 H := Nat.le_trans (Nat.le_sub_of_add_le hs0) (Nat.le_add_right _ _)
  refine ⟨fun d v => Nat.le_trans (hsp1 d v) (Nat.le_trans (Nat.le_of_eq (Nat.mul_one δs).symm)
    (Nat.mul_le_mul_left _ h1)), fun d rest w v => ?_⟩
  have hn1 : 0 < n1 := Nat.lt_of_le_of_lt (Nat.zero_le _) (hr1 d 0)
  have em : ∀ σ1, (Com1 d σ1 + n1 * rest) % n1 = Com1 d σ1 ∧ (Com1 d σ1 + n1 * rest) / n1 = rest := fun σ1 =>
    ⟨by rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (hr1 d σ1)],
     by rw [Nat.add_mul_div_left _ _ hn1, Nat.div_eq_of_lt (hr1 d σ1), Nat.zero_add]⟩
  let φ := fun c => chain1 K inner (ivP K inner z pre H) (c :: enc rest w) H (L + 1)
  have e : ∀ σ1, (fun m' w => chain1 K inner (ivP K inner z pre H) ((m' % n1) :: enc (m' / n1) w) H (L + 1)) (Com1 d σ1 + n1 * rest) w =
      φ (Com1 d σ1) := fun σ1 => by
    show chain1 K inner (ivP K inner z pre H) (((Com1 d σ1 + n1 * rest) % n1) :: enc ((Com1 d σ1 + n1 * rest) / n1) w) H (L + 1) = _
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
  exact Nat.mul_le_mul_left _ (preimage_loadTP K inner z pre hn1 hX L t s0 (enc rest w) (henc rest w) H v)

theorem loadTP_δs_countP {K Kc F : Nat} (hK : 0 < K) (inner : Nat → Nat → Nat) (hin : ∀ s x, inner s x < K) (κ : Nat → Nat)
    (hκ : ∀ u, κ u < Kc) (hF : ∀ v, sumTo K (fun u => indB (decide (κ u = v))) ≤ F)
    (hpk2 : ∀ s s' x x', inner s x = inner s' x' → κ s = κ s') (z : Nat) (pre : List Nat) {n1 : Nat} (hn : 0 < n1)
    (hd : ∀ iv a b, a < n1 → b < n1 → a ≠ b → inner iv a ≠ inner iv b)
    (hdxC : ∀ iv s s' x c c', c < n1 → c' < n1 → inner s x = inner iv c → inner s' x = inner iv c' → c = c') (X L : Nat) {t : Nat} (ht : 0 < t) (s0 δs : Nat) :
    fact (t - 1 - (pre.length + 2 * L)) * (K - (pre.length + t * (L + 1))) ^ (t - 1 - (pre.length + 2 * L)) * ffac s0 t *
        sumTo (K ^ K) (fun H => indB (permB K H) * (δs * loadTP K inner z pre n1 X L t s0 H)) ≤
      δs * ((fact (t - 1 - (pre.length + 2 * L)) * (K - (pre.length + t * (L + 1))) ^ (t - 1 - (pre.length + 2 * L)) * ffac s0 t * (s0 - 1) +
        n1 * (X ^ L * (n1 ^ t * (sumTo ((pre.length + t * (L + 1))) (fun j => j) * F) ^ (t - 1 - (pre.length + 2 * L))))) * sumTo (K ^ K) (fun H => indB (permB K H))) := by
  have h := loadTP_countP hK inner hin κ hκ hF hpk2 z pre hn hd hdxC X L ht s0
  rw [sumTo_congr _ (fun H _ => Nat.mul_left_comm _ _ _), ← sumTo_mul, Nat.mul_left_comm]
  exact Nat.mul_le_mul_left _ h

/-- The spread the permutation `H` gives proof `ix`: `δ0 ix loadTP`. -/
def δsPf (K : Nat) (inner : Nat → Nat → Nat) (z : Nat) (pre : List Nat) (n1 : Nat) (X L t s0 : Nat) (δ0 : Nat → Nat) (H ix : Nat) : Nat :=
  δ0 ix * loadTP K inner z pre n1 X L t s0 H


section
open B Air Stmt Mach Sudoku SudokuText Compose CompM Wit

set_option maxRecDepth 100000 in
/-- **`sud_interleaveS` averaged over a uniform permutation, the index
    after a public prefix, the first commitment and any `L` later blocks**
    (`loadφA` from `ivP`): at each permutation table `P` with
    `δsPf P = δ0 loadTP` (`loadTP_hsp`); the error the permutation-weighted
    sum of the tables' errors (`zkbT_avgW`). -/
theorem sud_interleaveLP {V Wv P1 P2 P3 W1 W2 W3 : Type} {kr kq : Nat} (φ1 : Nat → Nat → W1 → Nat) (nx1 : Nat → Nat → Nat → List Nat → Nat × Nat × W1) (G1 : Nat → Nat → Nat → List (List (List F)) → Nat → List Nat → P1) (φ2 : Nat → Nat → W2 → Nat) (nx2 : Nat → Nat → Nat → List Nat → Nat × Nat × W2) (G2 : Nat → Nat → Nat → List (List (List F)) → Nat → List Nat → P2) (φ3 : Nat → Nat → W3 → Nat) (nx3 : Nat → Nat → Nat → List Nat → Nat × Nat × W3) (G3 : Nat → Nat → Nat → List (List (List (List F))) × List (List (List F)) → Nat → List Nat → P3)
     (off : EF → String → EF) {puzzle : ∀ ix : Nat, List Nat} (hc : ∀ ix : Nat, CluesOK (cluesOf (puzzle ix))) {ρ : ∀ ix : Nat, Nat → Bool} {A : ∀ ix : Nat, List Cell} {k : ∀ ix : Nat, Nat} {row : ∀ ix : Nat, Nat → Air.Row} (hA : ∀ ix : Nat, AcceptsFrom (A ix) (stmtMachine (ρ ix) 729 (sudokuExpr (cluesOf (puzzle ix))) ACC REJ) (k ix) (row ix)) (hacc : ∀ ix : Nat, rd (A ix) ((row ix) ((k ix) - 1)).ctr ((row ix) ((k ix) - 1)).hd = some (.atom ACC)) (hlen : ∀ ix : Nat, (A ix).length = 2 ^ 16) (hk : ∀ ix : Nat, (k ix) ≤ 2 ^ 16) {tP : ∀ ix : Nat, Nat} (htp : ∀ ix : Nat, (tP ix) = progTp (stmtMachine (fun _ => false) 729 (sudokuExpr (cluesOf (puzzle ix))) ACC REJ).heap) (S16 S10 SP : ∀ ix : Nat, Nat → List F) (qv : ∀ ix : Nat, EF → EF → List EF → F → List F → List F → List EF) (wm wc ww wp : ∀ ix : Nat, Nat → List (EF → EF → List F)) {Lwm Lwc Lww Lwp : ∀ ix : Nat, Nat} (hlwm : ∀ ix : Nat, ∀ c, ((wm ix) c).length = (Lwm ix)) (hlwc : ∀ ix : Nat, ∀ c, ((wc ix) c).length = (Lwc ix)) (hlww : ∀ ix : Nat, ∀ c, ((ww ix) c).length = (Lww ix)) (hlwp : ∀ ix : Nat, ∀ c, ((wp ix) c).length = (Lwp ix)) {K2 K4 : Nat} (hK2 : 0 < K2) (hK4 : 0 < K4) (hS16 : ∀ ix : Nat, ∀ c4, ∀ x ∈ (S16 ix) c4, x ∉ cosetL 1 (bbGen 16) (2 ^ 16)) (hS10 : ∀ ix : Nat, ∀ c4, ∀ x ∈ (S10 ix) c4, x ∉ cosetL 1 (bbGen 10) (2 ^ 10)) (hSP : ∀ ix : Nat, ∀ c4, ∀ x ∈ (SP ix) c4, x ∉ cosetL 1 (bbGen ((tP ix) + 1)) (2 ^ ((tP ix) + 1))) (hsz16 : ∀ ix : Nat, ∀ c4, 2 * ((S16 ix) c4).length + 8 ≤ 2 ^ 16) (hsz : ∀ ix : Nat, ∀ c4, 2 * ((S10 ix) c4).length + 8 ≤ 2 ^ 10) (hszP : ∀ ix : Nat, ∀ c4, 2 * ((SP ix) c4).length + 8 ≤ 2 ^ ((tP ix) + 1)) {ncw : ∀ ix : Nat, Nat} (αd : ∀ ix : Nat, Nat → EF) {B4 : ∀ ix : Nat, Nat} (hB4 : ∀ ix : Nat, sumTo K4 (fun c4 => indB (!genB ((αd ix) c4))) ≤ (B4 ix)) (fri : ∀ ix : Nat, Nat → EF → EF → List (EF → EF) → V) (hncw : ∀ ix : Nat, 4 ≤ (ncw ix)) (NR2 : ∀ ix : Nat, Nat) (Rb : ∀ ix : Nat, Nat → EF → EF → Nat → List (EF → EF)) (Ro : ∀ ix : Nat, Nat → EF → EF → Nat → Wv) {n1 n2 n3 : Nat} {NS1 NS2 NS3 : ∀ ix : Nat, Nat} (Com1 : ∀ ix : Nat, List (List (List F)) → Nat → Nat) (hc1 : ∀ ix : Nat, ComHides (NS1 ix) (Com1 ix)) (hp1 : ∀ ix : Nat, ∀ c4 T1 T2 T3 T4 M, ComPfHides (NS1 ix) (Com1 ix) ((pfRdM (Q4 * Q4) K2 Q4 K4 n1 kr (φ1 ix) (nx1 ix) (G1 ix)) c4 T1 T2 T3 T4 M) (opF ((sudGroups (tP ix) ((S16 ix) c4) ((S10 ix) c4) ((SP ix) c4) EF.zero (qv ix)).map (·.base.S)) [0, 2, 4, 6])) (hr1 : ∀ ix : Nat, ∀ d σ, (Com1 ix) d σ < n1) (d1 : ∀ ix : Nat, List (List (List F))) (Com2 : ∀ ix : Nat, List (List (List F)) → Nat → Nat) (hc2 : ∀ ix : Nat, ComHides (NS2 ix) (Com2 ix)) (hp2 : ∀ ix : Nat, ∀ c4 T1 T2 T3 T4 M, ComPfHides (NS2 ix) (Com2 ix) ((pfRdM (Q4 * Q4) K2 Q4 K4 n1 kr (φ2 ix) (nx2 ix) (G2 ix)) c4 T1 T2 T3 T4 M) (opF ((sudGroups (tP ix) ((S16 ix) c4) ((S10 ix) c4) ((SP ix) c4) EF.zero (qv ix)).map (·.base.S)) [1, 3, 5, 7])) (hr2 : ∀ ix : Nat, ∀ d σ, (Com2 ix) d σ < n2) (d2 : ∀ ix : Nat, List (List (List F))) (Com3 : ∀ ix : Nat, List (List (List (List F))) × List (List (List F)) → Nat → Nat) (hc3 : ∀ ix : Nat, ComHides (NS3 ix) (Com3 ix)) (hp3 : ∀ ix : Nat, ∀ c4 T1 T2 T3 T4 M, ComPfHides (NS3 ix) (Com3 ix) ((pfRdM (Q4 * Q4) K2 Q4 K4 n1 kr (φ3 ix) (nx3 ix) (G3 ix)) c4 T1 T2 T3 T4 M) (fun d => (opQ (sudSsT ((S16 ix) c4) ((S10 ix) c4) ((SP ix) c4)) d.1, opCw (sudSsC (tP ix) ((S16 ix) c4) ((S10 ix) c4) ((SP ix) c4)) d.2))) (hr3 : ∀ ix : Nat, ∀ d σ, (Com3 ix) d σ < n3) (d3 : ∀ ix : Nat, List (List (List (List F))) × List (List (List F)))
    {Kp : Nat} (hKp : 0 < Kp) (inner : Nat → Nat → Nat) (hin : ∀ s x, inner s x < Kp) (κ : Nat → Nat) {Kc : Nat}
    (hκ : ∀ u, κ u < Kc) (hpk2 : ∀ s s' x x', inner s x = inner s' x' → κ s = κ s') (z : Nat) (pre : List Nat)
    (hd : ∀ iv a b, a < n1 → b < n1 → a ≠ b → inner iv a ≠ inner iv b)
    (hdxC : ∀ iv s s' x c c', c < n1 → c' < n1 → inner s x = inner iv c → inner s' x = inner iv c' → c = c')
    {X : Nat} (hX : 0 < X) (L : Nat) (enc : Nat → Option (List (List (List EF)) × List (List (List (List EF))) × List (List (List EF))) → List Nat) (henc : ∀ r w i, i < L → (enc r w).getD i 0 < X)
    (δ0 : Nat → Nat)
    (hsp1 : ∀ ix d v, sumTo (NS1 ix) (fun σ => indB (decide (Com1 ix d σ = v))) ≤ δ0 ix) {t : Nat} (ht : 0 < t) {s0 : Nat} (hs0 : 2 ≤ s0)
    (isQ : Nat → Bool) (nxtQ : Nat → List Nat → Nat × Nat × Unit) :
    ∀ n, ZKBT (fun (f : Nat × (Nat × Nat × Nat × Nat) → Nat) => sumTo (Kp ^ Kp) (fun P => indB (permB Kp P) *
        (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo (K4 ^ Kp) (fun H4 => sumTo ((Q4 * Q4) ^ n1) (fun H1 => sumTo (K2 ^ (n1 * n2)) (fun H2 => sumTo (Q4 ^ (n1 * (n2 * n3))) (fun H3 => f (H1, H2, H3, H4)))))) (fun H => f (P, H))))
      (KPowD (fun _ => (K4 * (Q4 * Q4 * (K2 * Q4)))) n)
      (smPowD (X := fun _ => Nat × Nat × Nat × (Nat → Tup)) (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner (ivP Kp inner z pre 0) n1 L enc 0) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).sm 2) n)
      (scPowD (C := fun _ => Nat × Nat × Nat × Nat) (fun _ => (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo K4 (fun c4 => sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo Q4 (fun c3 => f (c1, c2, c3, c4))))))) n)
      (fun PH x => (rvPowD (mixRv (Q4 * Q4) K2 Q4 K4 kq isQ nxtQ
        (fun i => read4T (Q4 * Q4) K2 Q4 K4 ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner (ivP Kp inner z pre PH.1) n1 L enc PH.1) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).m1 ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner (ivP Kp inner z pre PH.1) n1 L enc PH.1) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).m2 ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner (ivP Kp inner z pre PH.1) n1 L enc PH.1) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).m3 ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner (ivP Kp inner z pre PH.1) n1 L enc PH.1) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).q ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner (ivP Kp inner z pre PH.1) n1 L enc PH.1) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).out)) n) PH.2 x)
      (fun PH c x => (PH.1, (pgPowD (pgRd (Q4 * Q4) K2 Q4 K4 (fun i => !isQ i) (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner (ivP Kp inner z pre PH.1) n1 L enc PH.1) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).pts) (fun _ c => c)) n) PH.2 c x))
      (fun PH c x => (svPowDT (pgRd (Q4 * Q4) K2 Q4 K4 (fun i => !isQ i) (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner (ivP Kp inner z pre PH.1) n1 L enc PH.1) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).pts) (fun _ c => c))
        (mixSv (Q4 * Q4) K2 Q4 K4 kq isQ nxtQ (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner (ivP Kp inner z pre PH.1) n1 L enc PH.1) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).sv)) n) PH.2 c x)
      (sumTo (Kp ^ Kp) (fun P => indB (permB Kp P) * (errPowD (fun _ => (K4 * (Q4 * Q4 * (K2 * Q4)))) (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner (ivP Kp inner z pre P) n1 L enc P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).sm 2) (fun _ => (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo K4 (fun c4 => sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo Q4 (fun c3 => f (c1, c2, c3, c4))))))) (fun i => cond (isQ i) 0 ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner (ivP Kp inner z pre P) n1 L enc P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).ε)
        (fun n => (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo K4 (fun c4 => sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo Q4 (fun c3 => f (c1, c2, c3, c4)))))) (fun _ => (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo (K4 ^ Kp) (fun H4 => sumTo ((Q4 * Q4) ^ n1) (fun H1 => sumTo (K2 ^ (n1 * n2)) (fun H2 => sumTo (Q4 ^ (n1 * (n2 * n3))) (fun H3 => f (H1, H2, H3, H4)))))) (fun _ => smPowD (X := fun _ => Nat × Nat × Nat × (Nat → Tup)) (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner (ivP Kp inner z pre P) n1 L enc P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).sm 2) n
          (fun _ => rSum (fun i => cond (isQ i) kq (4 + 3 * kr)) n *
            cond (isQ n) 0 (((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner (ivP Kp inner z pre P) n1 L enc P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) n).NS * (((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner (ivP Kp inner z pre P) n1 L enc P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) n).NR * (Q4 ^ 2 * δsPf Kp inner z pre n1 X L t s0 δ0 P n))))))) n))) := by
  intro n
  exact zkbT_avgW (fun P => indB (permB Kp P)) (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo (K4 ^ Kp) (fun H4 => sumTo ((Q4 * Q4) ^ n1) (fun H1 => sumTo (K2 ^ (n1 * n2)) (fun H2 => sumTo (Q4 ^ (n1 * (n2 * n3))) (fun H3 => f (H1, H2, H3, H4)))))) (smPowD (X := fun _ => Nat × Nat × Nat × (Nat → Tup)) (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner (ivP Kp inner z pre 0) n1 L enc 0) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).sm 2) n) (scPowD (C := fun _ => Nat × Nat × Nat × Nat) (fun _ => (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo K4 (fun c4 => sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo Q4 (fun c3 => f (c1, c2, c3, c4))))))) n)
    (fun P => (rvPowD (mixRv (Q4 * Q4) K2 Q4 K4 kq isQ nxtQ
        (fun i => read4T (Q4 * Q4) K2 Q4 K4 ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner (ivP Kp inner z pre P) n1 L enc P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).m1 ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner (ivP Kp inner z pre P) n1 L enc P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).m2 ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner (ivP Kp inner z pre P) n1 L enc P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).m3 ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner (ivP Kp inner z pre P) n1 L enc P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).q ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner (ivP Kp inner z pre P) n1 L enc P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).out)) n)) (fun P => (pgPowD (pgRd (Q4 * Q4) K2 Q4 K4 (fun i => !isQ i) (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner (ivP Kp inner z pre P) n1 L enc P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).pts) (fun _ c => c)) n)) (fun P => (svPowDT (pgRd (Q4 * Q4) K2 Q4 K4 (fun i => !isQ i) (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner (ivP Kp inner z pre P) n1 L enc P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).pts) (fun _ c => c))
        (mixSv (Q4 * Q4) K2 Q4 K4 kq isQ nxtQ (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner (ivP Kp inner z pre P) n1 L enc P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).sv)) n))
    (fun P => (errPowD (fun _ => (K4 * (Q4 * Q4 * (K2 * Q4)))) (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner (ivP Kp inner z pre P) n1 L enc P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).sm 2) (fun _ => (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo K4 (fun c4 => sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo Q4 (fun c3 => f (c1, c2, c3, c4))))))) (fun i => cond (isQ i) 0 ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner (ivP Kp inner z pre P) n1 L enc P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).ε)
        (fun n => (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo K4 (fun c4 => sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo Q4 (fun c3 => f (c1, c2, c3, c4)))))) (fun _ => (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo (K4 ^ Kp) (fun H4 => sumTo ((Q4 * Q4) ^ n1) (fun H1 => sumTo (K2 ^ (n1 * n2)) (fun H2 => sumTo (Q4 ^ (n1 * (n2 * n3))) (fun H3 => f (H1, H2, H3, H4)))))) (fun _ => smPowD (X := fun _ => Nat × Nat × Nat × (Nat → Tup)) (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner (ivP Kp inner z pre P) n1 L enc P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).sm 2) n
          (fun _ => rSum (fun i => cond (isQ i) kq (4 + 3 * kr)) n *
            cond (isQ n) 0 (((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner (ivP Kp inner z pre P) n1 L enc P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) n).NS * (((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner (ivP Kp inner z pre P) n1 L enc P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) n).NR * (Q4 ^ 2 * δsPf Kp inner z pre n1 X L t s0 δ0 P n))))))) n)) (fun P _ hw =>
    sud_interleaveS φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3 off hc hA hacc hlen hk htp S16 S10 SP qv wm wc ww wp hlwm hlwc hlww hlwp
      hK2 hK4 (loadφA Kp inner (ivP Kp inner z pre P) n1 L enc P) (fun _ _ _ => rget_lt hKp _ _) hS16 hS10 hSP hsz16 hsz hszP αd hB4 fri hncw NR2 Rb Ro
      Com1 hc1 hp1 hr1 d1 Com2 hc2 hp2 hr2 d2 Com3 hc3 hp3 hr3 d3 (δsPf Kp inner z pre n1 X L t s0 δ0 P)
      (fun ix => (loadTP_hsp inner z pre hX L t enc henc (Com1 ix) (hr1 ix) (hsp1 ix) hs0 P).1)
      (fun ix => (loadTP_hsp inner z pre hX L t enc henc (Com1 ix) (hr1 ix) (hsp1 ix) hs0 P).2) isQ nxtQ n)


-- The statement unfolds `sudDD`'s fields at every `ix`; elaborating it exceeds the default heartbeats.
set_option maxHeartbeats 6000000 in
set_option maxRecDepth 100000 in
/-- **`sud_interleaveLP` with a number for its error**: `k = m + t (L+1)`,
    `e = t - 1 - (m + 2 L)`, `Kq = e! (Kp - k)^e s0 (s0-1) ⋯ (s0-t+1)` times the
    averaged real count is at most `Kq` times the averaged simulation plus
    `errPowD` at the errors `Kq W ε` and each spread `δ0 i (Kq (s0 - 1) +
    n1 X^L n1^t ((0 + ⋯ + (k - 1)) F)^e) W`, `W` the number of permutation
    tables (`avg_err_bound`, `loadTP_δs_countP`). -/
theorem sud_interleaveLPN {V Wv P1 P2 P3 W1 W2 W3 : Type} {kr kq : Nat} (φ1 : Nat → Nat → W1 → Nat) (nx1 : Nat → Nat → Nat → List Nat → Nat × Nat × W1) (G1 : Nat → Nat → Nat → List (List (List F)) → Nat → List Nat → P1) (φ2 : Nat → Nat → W2 → Nat) (nx2 : Nat → Nat → Nat → List Nat → Nat × Nat × W2) (G2 : Nat → Nat → Nat → List (List (List F)) → Nat → List Nat → P2) (φ3 : Nat → Nat → W3 → Nat) (nx3 : Nat → Nat → Nat → List Nat → Nat × Nat × W3) (G3 : Nat → Nat → Nat → List (List (List (List F))) × List (List (List F)) → Nat → List Nat → P3)
     (off : EF → String → EF) {puzzle : ∀ ix : Nat, List Nat} (hc : ∀ ix : Nat, CluesOK (cluesOf (puzzle ix))) {ρ : ∀ ix : Nat, Nat → Bool} {A : ∀ ix : Nat, List Cell} {k : ∀ ix : Nat, Nat} {row : ∀ ix : Nat, Nat → Air.Row} (hA : ∀ ix : Nat, AcceptsFrom (A ix) (stmtMachine (ρ ix) 729 (sudokuExpr (cluesOf (puzzle ix))) ACC REJ) (k ix) (row ix)) (hacc : ∀ ix : Nat, rd (A ix) ((row ix) ((k ix) - 1)).ctr ((row ix) ((k ix) - 1)).hd = some (.atom ACC)) (hlen : ∀ ix : Nat, (A ix).length = 2 ^ 16) (hk : ∀ ix : Nat, (k ix) ≤ 2 ^ 16) {tP : ∀ ix : Nat, Nat} (htp : ∀ ix : Nat, (tP ix) = progTp (stmtMachine (fun _ => false) 729 (sudokuExpr (cluesOf (puzzle ix))) ACC REJ).heap) (S16 S10 SP : ∀ ix : Nat, Nat → List F) (qv : ∀ ix : Nat, EF → EF → List EF → F → List F → List F → List EF) (wm wc ww wp : ∀ ix : Nat, Nat → List (EF → EF → List F)) {Lwm Lwc Lww Lwp : ∀ ix : Nat, Nat} (hlwm : ∀ ix : Nat, ∀ c, ((wm ix) c).length = (Lwm ix)) (hlwc : ∀ ix : Nat, ∀ c, ((wc ix) c).length = (Lwc ix)) (hlww : ∀ ix : Nat, ∀ c, ((ww ix) c).length = (Lww ix)) (hlwp : ∀ ix : Nat, ∀ c, ((wp ix) c).length = (Lwp ix)) {K2 K4 : Nat} (hK2 : 0 < K2) (hK4 : 0 < K4) (hS16 : ∀ ix : Nat, ∀ c4, ∀ x ∈ (S16 ix) c4, x ∉ cosetL 1 (bbGen 16) (2 ^ 16)) (hS10 : ∀ ix : Nat, ∀ c4, ∀ x ∈ (S10 ix) c4, x ∉ cosetL 1 (bbGen 10) (2 ^ 10)) (hSP : ∀ ix : Nat, ∀ c4, ∀ x ∈ (SP ix) c4, x ∉ cosetL 1 (bbGen ((tP ix) + 1)) (2 ^ ((tP ix) + 1))) (hsz16 : ∀ ix : Nat, ∀ c4, 2 * ((S16 ix) c4).length + 8 ≤ 2 ^ 16) (hsz : ∀ ix : Nat, ∀ c4, 2 * ((S10 ix) c4).length + 8 ≤ 2 ^ 10) (hszP : ∀ ix : Nat, ∀ c4, 2 * ((SP ix) c4).length + 8 ≤ 2 ^ ((tP ix) + 1)) {ncw : ∀ ix : Nat, Nat} (αd : ∀ ix : Nat, Nat → EF) {B4 : ∀ ix : Nat, Nat} (hB4 : ∀ ix : Nat, sumTo K4 (fun c4 => indB (!genB ((αd ix) c4))) ≤ (B4 ix)) (fri : ∀ ix : Nat, Nat → EF → EF → List (EF → EF) → V) (hncw : ∀ ix : Nat, 4 ≤ (ncw ix)) (NR2 : ∀ ix : Nat, Nat) (Rb : ∀ ix : Nat, Nat → EF → EF → Nat → List (EF → EF)) (Ro : ∀ ix : Nat, Nat → EF → EF → Nat → Wv) {n1 n2 n3 : Nat} {NS1 NS2 NS3 : ∀ ix : Nat, Nat} (Com1 : ∀ ix : Nat, List (List (List F)) → Nat → Nat) (hc1 : ∀ ix : Nat, ComHides (NS1 ix) (Com1 ix)) (hp1 : ∀ ix : Nat, ∀ c4 T1 T2 T3 T4 M, ComPfHides (NS1 ix) (Com1 ix) ((pfRdM (Q4 * Q4) K2 Q4 K4 n1 kr (φ1 ix) (nx1 ix) (G1 ix)) c4 T1 T2 T3 T4 M) (opF ((sudGroups (tP ix) ((S16 ix) c4) ((S10 ix) c4) ((SP ix) c4) EF.zero (qv ix)).map (·.base.S)) [0, 2, 4, 6])) (hr1 : ∀ ix : Nat, ∀ d σ, (Com1 ix) d σ < n1) (d1 : ∀ ix : Nat, List (List (List F))) (Com2 : ∀ ix : Nat, List (List (List F)) → Nat → Nat) (hc2 : ∀ ix : Nat, ComHides (NS2 ix) (Com2 ix)) (hp2 : ∀ ix : Nat, ∀ c4 T1 T2 T3 T4 M, ComPfHides (NS2 ix) (Com2 ix) ((pfRdM (Q4 * Q4) K2 Q4 K4 n1 kr (φ2 ix) (nx2 ix) (G2 ix)) c4 T1 T2 T3 T4 M) (opF ((sudGroups (tP ix) ((S16 ix) c4) ((S10 ix) c4) ((SP ix) c4) EF.zero (qv ix)).map (·.base.S)) [1, 3, 5, 7])) (hr2 : ∀ ix : Nat, ∀ d σ, (Com2 ix) d σ < n2) (d2 : ∀ ix : Nat, List (List (List F))) (Com3 : ∀ ix : Nat, List (List (List (List F))) × List (List (List F)) → Nat → Nat) (hc3 : ∀ ix : Nat, ComHides (NS3 ix) (Com3 ix)) (hp3 : ∀ ix : Nat, ∀ c4 T1 T2 T3 T4 M, ComPfHides (NS3 ix) (Com3 ix) ((pfRdM (Q4 * Q4) K2 Q4 K4 n1 kr (φ3 ix) (nx3 ix) (G3 ix)) c4 T1 T2 T3 T4 M) (fun d => (opQ (sudSsT ((S16 ix) c4) ((S10 ix) c4) ((SP ix) c4)) d.1, opCw (sudSsC (tP ix) ((S16 ix) c4) ((S10 ix) c4) ((SP ix) c4)) d.2))) (hr3 : ∀ ix : Nat, ∀ d σ, (Com3 ix) d σ < n3) (d3 : ∀ ix : Nat, List (List (List (List F))) × List (List (List F)))
    {Kp : Nat} (hKp : 0 < Kp) (inner : Nat → Nat → Nat) (hin : ∀ s x, inner s x < Kp) (κ : Nat → Nat) {Kc : Nat}
    (hκ : ∀ u, κ u < Kc) (hpk2 : ∀ s s' x x', inner s x = inner s' x' → κ s = κ s') (z : Nat) (pre : List Nat)
    (hd : ∀ iv a b, a < n1 → b < n1 → a ≠ b → inner iv a ≠ inner iv b)
    (hdxC : ∀ iv s s' x c c', c < n1 → c' < n1 → inner s x = inner iv c → inner s' x = inner iv c' → c = c')
    {X : Nat} (hX : 0 < X) (L : Nat) (enc : Nat → Option (List (List (List EF)) × List (List (List (List EF))) × List (List (List EF))) → List Nat) (henc : ∀ r w i, i < L → (enc r w).getD i 0 < X)
    (δ0 : Nat → Nat) (hn1 : 0 < n1) {F : Nat} (hF : ∀ v, sumTo Kp (fun u => indB (decide (κ u = v))) ≤ F)
    (hsp1 : ∀ ix d v, sumTo (NS1 ix) (fun σ => indB (decide (Com1 ix d σ = v))) ≤ δ0 ix) {t : Nat} (ht : 0 < t) {s0 : Nat} (hs0 : 2 ≤ s0)
    (isQ : Nat → Bool) (nxtQ : Nat → List Nat → Nat × Nat × Unit) :
    ∀ n (E : Nat × (Nat × Nat × Nat × Nat) → _ → Bool),
      (fact (t - 1 - (pre.length + 2 * L)) * (Kp - (pre.length + t * (L + 1))) ^ (t - 1 - (pre.length + 2 * L)) * ffac s0 t) * ((KPowD (fun _ => (K4 * (Q4 * Q4 * (K2 * Q4)))) n) * (fun (f : Nat × (Nat × Nat × Nat × Nat) → Nat) => sumTo (Kp ^ Kp) (fun P => indB (permB Kp P) * (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo (K4 ^ Kp) (fun H4 => sumTo ((Q4 * Q4) ^ n1) (fun H1 => sumTo (K2 ^ (n1 * n2)) (fun H2 => sumTo (Q4 ^ (n1 * (n2 * n3))) (fun H3 => f (H1, H2, H3, H4)))))) (fun H => f (P, H)))) (fun H => (smPowD (X := fun _ => Nat × Nat × Nat × (Nat → Tup)) (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner (ivP Kp inner z pre 0) n1 L enc 0) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).sm 2) n) (fun x => indB (E H ((fun PH x => (rvPowD (mixRv (Q4 * Q4) K2 Q4 K4 kq isQ nxtQ
        (fun i => read4T (Q4 * Q4) K2 Q4 K4 ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner (ivP Kp inner z pre PH.1) n1 L enc PH.1) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).m1 ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner (ivP Kp inner z pre PH.1) n1 L enc PH.1) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).m2 ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner (ivP Kp inner z pre PH.1) n1 L enc PH.1) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).m3 ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner (ivP Kp inner z pre PH.1) n1 L enc PH.1) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).q ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner (ivP Kp inner z pre PH.1) n1 L enc PH.1) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).out)) n) PH.2 x) H x))))) ≤
        (fact (t - 1 - (pre.length + 2 * L)) * (Kp - (pre.length + t * (L + 1))) ^ (t - 1 - (pre.length + 2 * L)) * ffac s0 t) * (fun (f : Nat × (Nat × Nat × Nat × Nat) → Nat) => sumTo (Kp ^ Kp) (fun P => indB (permB Kp P) * (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo (K4 ^ Kp) (fun H4 => sumTo ((Q4 * Q4) ^ n1) (fun H1 => sumTo (K2 ^ (n1 * n2)) (fun H2 => sumTo (Q4 ^ (n1 * (n2 * n3))) (fun H3 => f (H1, H2, H3, H4)))))) (fun H => f (P, H)))) (fun H => (scPowD (C := fun _ => Nat × Nat × Nat × Nat) (fun _ => (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo K4 (fun c4 => sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo Q4 (fun c3 => f (c1, c2, c3, c4))))))) n) (fun c => (smPowD (X := fun _ => Nat × Nat × Nat × (Nat → Tup)) (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner (ivP Kp inner z pre 0) n1 L enc 0) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).sm 2) n) (fun x => indB (E ((fun PH c x => (PH.1, (pgPowD (pgRd (Q4 * Q4) K2 Q4 K4 (fun i => !isQ i) (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner (ivP Kp inner z pre PH.1) n1 L enc PH.1) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).pts) (fun _ c => c)) n) PH.2 c x)) H c x) ((fun PH c x => (svPowDT (pgRd (Q4 * Q4) K2 Q4 K4 (fun i => !isQ i) (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner (ivP Kp inner z pre PH.1) n1 L enc PH.1) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).pts) (fun _ c => c))
        (mixSv (Q4 * Q4) K2 Q4 K4 kq isQ nxtQ (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner (ivP Kp inner z pre PH.1) n1 L enc PH.1) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).sv)) n) PH.2 c x) H c x))))) +
        errPowD (fun _ => (K4 * (Q4 * Q4 * (K2 * Q4)))) (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner (ivP Kp inner z pre 0) n1 L enc 0) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).sm 2) (fun _ => (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo K4 (fun c4 => sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo Q4 (fun c3 => f (c1, c2, c3, c4))))))) (fun i => (fact (t - 1 - (pre.length + 2 * L)) * (Kp - (pre.length + t * (L + 1))) ^ (t - 1 - (pre.length + 2 * L)) * ffac s0 t) * (sumTo (Kp ^ Kp) (fun P => indB (permB Kp P))) * (fun i => cond (isQ i) 0 ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner (ivP Kp inner z pre 0) n1 L enc 0) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).ε) i) (fun i => (fun n x => (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo K4 (fun c4 => sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo Q4 (fun c3 => f (c1, c2, c3, c4)))))) (fun _ => (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo (K4 ^ Kp) (fun H4 => sumTo ((Q4 * Q4) ^ n1) (fun H1 => sumTo (K2 ^ (n1 * n2)) (fun H2 => sumTo (Q4 ^ (n1 * (n2 * n3))) (fun H3 => f (H1, H2, H3, H4)))))) (fun _ => smPowD (X := fun _ => Nat × Nat × Nat × (Nat → Tup)) (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner (ivP Kp inner z pre 0) n1 L enc 0) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).sm 2) n
          (fun _ => rSum (fun i => cond (isQ i) kq (4 + 3 * kr)) n *
            cond (isQ n) 0 (((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner (ivP Kp inner z pre 0) n1 L enc 0) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) n).NS * (((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner (ivP Kp inner z pre 0) n1 L enc 0) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) n).NR * (Q4 ^ 2 * x))))))) i ((fun i => δ0 i * ((fact (t - 1 - (pre.length + 2 * L)) * (Kp - (pre.length + t * (L + 1))) ^ (t - 1 - (pre.length + 2 * L)) * ffac s0 t * (s0 - 1) + n1 * (X ^ L * (n1 ^ t * (sumTo ((pre.length + t * (L + 1))) (fun j => j) * F) ^ (t - 1 - (pre.length + 2 * L))))) * (sumTo (Kp ^ Kp) (fun P => indB (permB Kp P))))) i)) n := by
  intro n E
  have h := sud_interleaveLP (kq := kq) φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3 off hc hA hacc hlen hk htp S16 S10 SP qv wm wc ww wp hlwm hlwc hlww hlwp hK2 hK4 hS16 hS10 hSP hsz16 hsz hszP αd hB4 fri hncw NR2 Rb Ro Com1 hc1 hp1 hr1 d1 Com2 hc2 hp2 hr2 d2 Com3 hc3 hp3 hr3 d3 hKp inner hin κ hκ hpk2 z pre hd hdxC hX L enc henc δ0 hsp1 ht hs0 isQ nxtQ n
  have hb := (avg_err_bound (fun _ => (K4 * (Q4 * Q4 * (K2 * Q4)))) (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner (ivP Kp inner z pre 0) n1 L enc 0) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).sm 2) (fun _ => (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo K4 (fun c4 => sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo Q4 (fun c3 => f (c1, c2, c3, c4))))))) (fun i => cond (isQ i) 0 ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner (ivP Kp inner z pre 0) n1 L enc 0) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).ε) (Kp ^ Kp) (fun P => indB (permB Kp P))
      (fun P i => δsPf Kp inner z pre n1 X L t s0 δ0 P i) (fun n x => (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo K4 (fun c4 => sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo Q4 (fun c3 => f (c1, c2, c3, c4)))))) (fun _ => (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo (K4 ^ Kp) (fun H4 => sumTo ((Q4 * Q4) ^ n1) (fun H1 => sumTo (K2 ^ (n1 * n2)) (fun H2 => sumTo (Q4 ^ (n1 * (n2 * n3))) (fun H3 => f (H1, H2, H3, H4)))))) (fun _ => smPowD (X := fun _ => Nat × Nat × Nat × (Nat → Tup)) (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner (ivP Kp inner z pre 0) n1 L enc 0) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).sm 2) n
          (fun _ => rSum (fun i => cond (isQ i) kq (4 + 3 * kr)) n *
            cond (isQ n) 0 (((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner (ivP Kp inner z pre 0) n1 L enc 0) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) n).NS * (((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner (ivP Kp inner z pre 0) n1 L enc 0) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) n).NR * (Q4 ^ 2 * x)))))))
      (fun i x => wrap_scale (lin_sum4 _ _ _ _) (lin_sum4 _ _ _ _) (lin_smPowD (fun _ => lin_sm _ _ _ _) i) _ _ _ _ _ x)
      (fact (t - 1 - (pre.length + 2 * L)) * (Kp - (pre.length + t * (L + 1))) ^ (t - 1 - (pre.length + 2 * L)) * ffac s0 t) (fun i => δ0 i * ((fact (t - 1 - (pre.length + 2 * L)) * (Kp - (pre.length + t * (L + 1))) ^ (t - 1 - (pre.length + 2 * L)) * ffac s0 t * (s0 - 1) + n1 * (X ^ L * (n1 ^ t * (sumTo ((pre.length + t * (L + 1))) (fun j => j) * F) ^ (t - 1 - (pre.length + 2 * L))))) * (sumTo (Kp ^ Kp) (fun P => indB (permB Kp P))))) (fun i => loadTP_δs_countP hKp inner hin κ hκ hF hpk2 z pre hn1 hd hdxC X L ht s0 (δ0 i)) n)
  exact zkbT_err_le h _ _ hb E

end

end Circuit
