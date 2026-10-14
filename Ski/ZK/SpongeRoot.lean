import Ski.ZK.SpongeAbsorb

/-!
# Chains that meet, first positions revisited

`SpongeUnion` asks that no later query revisit a first position (`hcf`),
which its tags `h0`, `hnz` supply and Plonky3 0.8 does not: at an 8-element
digest a later block is absorbed as a first commitment.  Here the
revisits are allowed.

- **Unpaid merges.** `labR_inv` pays every merge of two chains' labels by
  a projection both labels visited.  A revisit of a first position has no
  query before it in the revisited chain, so `labR_invU` lets a flagged
  query merge unpaid, counting it on the right, and asks the paying
  visitors to share only labels (`labR_finalU`).
- **At most `L` go unpaid.** A block sends at most one first commitment's
  position (`hdx`); so at each later step at most one first position is
  revisited for the first time, and later revisits of it are paid by the
  earlier revisitor's predecessor, which shares its projection (`hpk2`)
  and, by then, the revisited chain's label (`unpS`, `unpS_count`).
  Chains that all meet therefore make `n1 - 1 - L` fresh near queries
  (`allMeet_near3`).
- **The bounds.** `SpongeUnion`'s chain with the exponent `t - 1 - L` in
  place of `t - 1` and no tags: `allMeet_countP3`, `meetM_countP3`,
  `meet_markov3`, the load `loadTR` over every later block list
  (`preimage_loadTR`, `loadTR_countP`, `loadTR_hsp`), and the composite
  `sud_interleaveLR` with a number for its error (`sud_interleaveLRN`).
- **0.8's absorption.** `inner08` sends each block to at most one first
  commitment's position (`inner08_hdx`), and meets `hpk2`, `hF` and `hd`
  with the capacity's first element dropped (`SpongeAbsorb`).

Size.  At BabyBear width 16, rate 8, with `F / K = 1 / p ^ 7`, `n1 = p ^ 8`
and blocks below `X = 9 p ^ 8`, optimizing `t` and `s0` makes `E[loadTR]`
about `2^44`, `2^47`, `2^51`, `2^61` for `L = 1, 3, 10, 100`, against
`n1 ≈ 2^247` first commitments; the composites say nothing unless
`Kp > t (L + 1)` and `s0 ≥ t`.

Limits.  The state `iv` before the first commitment is fixed before the
permutation, where batch-stark absorbs a domain separator first; the
first commitment fills one block; the fourth table `H4` stays
independent of the permutation, which Plonky3 squeezes the challenge
from; and every step after the first commitment absorbs a block, where 0.8 permutes an empty buffer, a squeeze leaving the rate, when a phase draws more than `RATE` elements (the bench's lookup phase draws `1 + 4 + 4 = 9` at `GRIND_LOOKUP = 5`).
-/

set_option autoImplicit false

namespace Circuit
open ZKF

/-- **The invariant with unpaid merges**: `labR_inv` where a merge at a
    query flagged `unp` need not be paid by a shared projection, each
    such query counted on the right; the paying projection's visitors
    need share only labels with the merged chains. -/
theorem labR_invU (t : Nat) (pos ch kap : Nat → Nat) (unp : Nat → Bool) {Kc : Nat} (hch : ∀ τ, ch τ < t) (hkap : ∀ τ, kap τ < Kc)
    (hkp : ∀ τ τ', pos τ = pos τ' → kap τ = kap τ')
    (Tend : Nat) (hprev : ∀ T τ0, T < Tend → τ0 < T → pos τ0 = pos T → labR pos ch T (ch T) ≠ labR pos ch T (ch τ0) →
      unp T = false → ∃ τ1 τ2, τ1 < T ∧ τ2 < T ∧ labR pos ch T (ch τ1) = labR pos ch T (ch T) ∧
        labR pos ch T (ch τ2) = labR pos ch T (ch τ0) ∧ kap τ1 = kap τ2) :
    ∀ T, T ≤ Tend → t + sumTo Kc (fun v0 => dcount t (labR pos ch T) (visB ch kap T v0) - 1) ≤
      sumTo T (fun τ => indB (nearInc pos kap τ)) + dcount t (labR pos ch T) (fun _ => true) + sumTo T (fun τ => indB (unp τ))
  | 0, _ => by
    have hv : ∀ v0, visB ch kap 0 v0 = fun _ => false := fun v0 => rfl
    show t + sumTo Kc (fun v0 => dcount t (fun j => j) (visB ch kap 0 v0) - 1) ≤ 0 + dcount t (fun j => j) (fun _ => true) + 0
    rw [dcount_id, Nat.zero_add, Nat.add_zero]
    refine Nat.le_of_eq (Eq.trans (congrArg (t + ·) (Eq.trans (sumTo_congr _ (fun v0 _ => by
      rw [hv v0, dcount_none])) (Eq.trans (sumTo_const 0 Kc) (Nat.mul_zero Kc)))) (Nat.add_zero t))
  | T + 1, hT => by
    have ih := labR_invU t pos ch kap unp hch hkap hkp Tend hprev T (Nat.le_of_succ_le hT)
    have hun : sumTo (T + 1) (fun τ => indB (unp τ)) = sumTo T (fun τ => indB (unp τ)) + indB (unp T) := rfl
    rw [hun]
    have hnear : sumTo (T + 1) (fun τ => indB (nearInc pos kap τ)) =
        sumTo T (fun τ => indB (nearInc pos kap τ)) + indB (nearInc pos kap T) := rfl
    rw [hnear]
    have hlt : ∀ j, j < t → labR pos ch T j < t := fun j hj => labR_lt t pos ch hch T j hj
    cases ho : oldB pos T
    · -- a fresh query: labels unchanged, one visit added
      have hL : labR pos ch (T + 1) = labR pos ch T := by
        funext j; show (if oldB pos T = true then _ else _) = _; rw [ho]; rfl
      rw [hL]
      have pt : ∀ v0, dcount t (labR pos ch T) (visB ch kap (T + 1) v0) - 1 ≤
          (dcount t (labR pos ch T) (visB ch kap T v0) - 1) + indB (decide (v0 = kap T)) * indB (nearInc pos kap T) := by
        intro v0
        by_cases hv : v0 = kap T
        · subst hv
          have e := visB_add ch kap T
          have hadd := dcount_add t (labR pos ch T) (visB ch kap T (kap T)) (hch T) (hlt _ (hch T))
          rw [show visB ch kap (T + 1) (kap T) = fun j => visB ch kap T (kap T) j || j == ch T from e]
          rw [decide_eq_true rfl, show indB true = 1 from rfl, Nat.one_mul]
          cases hex : (List.range T).any (fun τ' => kap τ' == kap T)
          · -- no earlier visitor of this projection
            have hnone : visB ch kap T (kap T) = fun _ => false := by
              funext j
              refine List.any_eq_false.2 (fun τ hτ hb => ?_)
              rw [Bool.and_eq_true] at hb
              have := List.any_eq_false.1 hex τ hτ
              exact this hb.2
            rw [hnone, dcount_none] at hadd ⊢
            have := indB_le (!present t (labR pos ch T) (fun _ => false) (labR pos ch T (ch T)))
            omega
          · have hn : nearInc pos kap T = true := by unfold nearInc; rw [ho, hex]; rfl
            rw [hn, show indB true = 1 from rfl]
            have := indB_le (!present t (labR pos ch T) (visB ch kap T (kap T)) (labR pos ch T (ch T)))
            omega
        · rw [decide_eq_false hv, show indB false = 0 from rfl, Nat.zero_mul, Nat.add_zero]
          rw [show visB ch kap (T + 1) v0 = fun j => visB ch kap T v0 j from visB_other ch kap T v0 (fun e => hv e.symm)]
          exact Nat.le_refl _
      have hs := sumTo_mono Kc (fun v0 _ => pt v0)
      rw [sumTo_add, sumTo_point _ Kc (hkap T)] at hs
      omega
    · -- a repeated query
      obtain ⟨hf, ef⟩ := firstOld_spec pos ho
      have hn : nearInc pos kap T = false := by unfold nearInc; rw [ho]; rfl
      rw [hn, show indB false = 0 from rfl, Nat.add_zero]
      let τ0 := firstOld pos T
      let a := labR pos ch T (ch T)
      let b := labR pos ch T (ch τ0)
      have hL : labR pos ch (T + 1) = mergeL (labR pos ch T) a b := by
        funext j; show (if oldB pos T = true then _ else _) = _; rw [ho]; rfl
      have hk0 : kap τ0 = kap T := hkp _ _ ef
      have vis0 : visB ch kap T (kap T) (ch τ0) = true := by rw [← hk0]; exact visB_of ch kap hf
      by_cases hab : a = b
      · -- same label: nothing merges
        have hL' : labR pos ch (T + 1) = labR pos ch T := by rw [hL, ← hab, mergeL_self]
        rw [hL']
        have pt : ∀ v0, dcount t (labR pos ch T) (visB ch kap (T + 1) v0) = dcount t (labR pos ch T) (visB ch kap T v0) := by
          intro v0
          by_cases hv : v0 = kap T
          · subst hv
            rw [show visB ch kap (T + 1) (kap T) = fun j => visB ch kap T (kap T) j || j == ch T from visB_add ch kap T]
            refine dcount_add_eq t _ _ ?_
            have := present_of t (labR pos ch T) (visB ch kap T (kap T)) (hch τ0) vis0
            show present t (labR pos ch T) (visB ch kap T (kap T)) a = true
            rw [hab]; exact this
          · rw [show visB ch kap (T + 1) v0 = fun j => visB ch kap T v0 j from visB_other ch kap T v0 (fun e => hv e.symm)]
        rw [sumTo_congr _ (fun v0 _ => by rw [pt v0])]
        exact Nat.le_trans ih (Nat.add_le_add_left (Nat.le_add_right _ _) _)
      · -- two labels merge, paid by a projection whose visitors carried both
        have ha : a < t := hlt _ (hch T)
        have hb : b < t := hlt _ (hch τ0)
        rw [hL]
        have hLmT : (mergeL (labR pos ch T) a b) (ch T) = a := by show (if labR pos ch T (ch T) = b then a else labR pos ch T (ch T)) = a; rw [if_neg hab]
        have hLm0 : (mergeL (labR pos ch T) a b) (ch τ0) = a := by show (if labR pos ch T (ch τ0) = b then a else labR pos ch T (ch τ0)) = a; rw [if_pos rfl]
        have d_eq : ∀ v0, dcount t (mergeL (labR pos ch T) a b) (visB ch kap (T + 1) v0) = dcount t (mergeL (labR pos ch T) a b) (visB ch kap T v0) := by
          intro v0
          by_cases hv : v0 = kap T
          · subst hv
            rw [show visB ch kap (T + 1) (kap T) = fun j => visB ch kap T (kap T) j || j == ch T from visB_add ch kap T]
            refine dcount_add_eq t _ _ ?_
            rw [hLmT]
            have := present_of t (mergeL (labR pos ch T) a b) _ (hch τ0) vis0
            rw [hLm0] at this; exact this
          · rw [show visB ch kap (T + 1) v0 = fun j => visB ch kap T v0 j from visB_other ch kap T v0 (fun e => hv e.symm)]
        cases hu : unp T
        case true =>
          -- an unpaid merge: the surplus does not grow, one label goes
          have pt2 : ∀ v0, dcount t (mergeL (labR pos ch T) a b) (visB ch kap (T + 1) v0) - 1 ≤
              dcount t (labR pos ch T) (visB ch kap T v0) - 1 := fun v0 => by
            rw [d_eq v0]; exact Nat.sub_le_sub_right (dcount_merge_le t _ _ hab ha hb) 1
          have hs := sumTo_mono Kc (fun v0 _ => pt2 v0)
          have hc := dcount_merge_ge t (labR pos ch T) (fun _ => true) hab ha hb
          rw [show indB true = 1 from rfl]
          omega
        obtain ⟨τ1, τ2, h1, h2, c1, c2, k12⟩ := hprev T τ0 (Nat.lt_of_succ_le hT) hf ef hab hu
        let cs := kap τ1
        have pa : present t (labR pos ch T) (visB ch kap T cs) a = true := by
          have := present_of t (labR pos ch T) (visB ch kap T cs) (hch τ1) (visB_of ch kap h1)
          rw [c1] at this; exact this
        have pb : present t (labR pos ch T) (visB ch kap T cs) b = true := by
          have v2 : visB ch kap T cs (ch τ2) = true := by show visB ch kap T (kap τ1) (ch τ2) = true; rw [k12]; exact visB_of ch kap h2
          have := present_of t (labR pos ch T) (visB ch kap T cs) (hch τ2) v2
          rw [c2] at this; exact this
        have both := dcount_merge_both t (labR pos ch T) (visB ch kap T cs) hab ha hb pa pb
        have dpos : 1 ≤ dcount t (mergeL (labR pos ch T) a b) (visB ch kap T cs) := by
          have pr : present t (mergeL (labR pos ch T) a b) (visB ch kap T cs) a = true := by
            have := present_of t (mergeL (labR pos ch T) a b) (visB ch kap T cs) (hch τ1) (visB_of ch kap h1)
            have hLm1 : (mergeL (labR pos ch T) a b) (ch τ1) = a := by
              show (if labR pos ch T (ch τ1) = b then a else labR pos ch T (ch τ1)) = a
              rw [c1]; split <;> rfl
            rw [hLm1] at this; exact this
          refine Nat.le_trans (Nat.le_of_eq ?_) (le_sumTo (fun v => indB (present t (mergeL (labR pos ch T) a b) (visB ch kap T cs) v)) t ha)
          rw [pr]; rfl
        have pt : ∀ v0, (dcount t (mergeL (labR pos ch T) a b) (visB ch kap (T + 1) v0) - 1) + indB (decide (v0 = cs)) ≤
            dcount t (labR pos ch T) (visB ch kap T v0) - 1 := by
          intro v0
          rw [d_eq v0]
          by_cases hv : v0 = cs
          · rw [hv, decide_eq_true rfl, show indB true = 1 from rfl]
            have b2 := both
            omega
          · rw [decide_eq_false hv, show indB false = 0 from rfl, Nat.add_zero]
            exact Nat.sub_le_sub_right (dcount_merge_le t _ _ hab ha hb) 1
        have hs := sumTo_mono Kc (fun v0 _ => pt v0)
        rw [sumTo_add] at hs
        have hpt : sumTo Kc (fun v0 => indB (decide (v0 = cs))) = 1 := by
          have := sumTo_point 1 Kc (hkap τ1)
          rw [← this]; exact sumTo_congr _ (fun v0 _ => (Nat.mul_one _).symm)
        rw [hpt] at hs
        have hc := dcount_merge_ge t (labR pos ch T) (fun _ => true) hab ha hb
        omega


/-- **`labR_final` with unpaid merges**: chains whose last queries share a
    position saw near queries or unpaid merges, `t - 1` in all. -/
theorem labR_finalU (t : Nat) (pos ch kap : Nat → Nat) (unp : Nat → Bool) {Kc : Nat} (hch : ∀ τ, ch τ < t)
    (hkap : ∀ τ, kap τ < Kc) (hkp : ∀ τ τ', pos τ = pos τ' → kap τ = kap τ')
    (Tend p : Nat) (hprev : ∀ T τ0, T < Tend → τ0 < T → pos τ0 = pos T → labR pos ch T (ch T) ≠ labR pos ch T (ch τ0) →
      unp T = false → ∃ τ1 τ2, τ1 < T ∧ τ2 < T ∧ labR pos ch T (ch τ1) = labR pos ch T (ch T) ∧
        labR pos ch T (ch τ2) = labR pos ch T (ch τ0) ∧ kap τ1 = kap τ2)
    (hall : ∀ j, j < t → ∃ τ, τ < Tend ∧ ch τ = j ∧ pos τ = p) :
    t ≤ sumTo Tend (fun τ => indB (nearInc pos kap τ)) + 1 + sumTo Tend (fun τ => indB (unp τ)) := by
  have hinv := labR_invU t pos ch kap unp hch hkap hkp Tend hprev Tend (Nat.le_refl _)
  have hc : dcount t (labR pos ch Tend) (fun _ => true) ≤ 1 := by
    refine sum_le_one t (fun v v' _ _ h1 h2 => ?_)
    obtain ⟨j, hj, e⟩ := List.any_eq_true.1 h1
    obtain ⟨j', hj', e'⟩ := List.any_eq_true.1 h2
    rw [Bool.true_and, beq_iff_eq] at e e'
    obtain ⟨τ, hτ, c, pτ⟩ := hall j (List.mem_range.1 hj)
    obtain ⟨τ', hτ', c', pτ'⟩ := hall j' (List.mem_range.1 hj')
    rw [← e, ← e', ← c, ← c']
    exact labR_coh pos ch Tend τ τ' hτ hτ' (pτ.trans pτ'.symm)
  omega

/-- A sum over `L + 1` terms, the first `0` and each at most `1`. -/
theorem sumTo_le_tail (g : Nat → Nat) (h0 : g 0 = 0) (h1 : ∀ q, g q ≤ 1) : ∀ L, sumTo (L + 1) g ≤ L
  | 0 => by show 0 + g 0 ≤ 0; rw [h0]; exact Nat.le_refl 0
  | L + 1 => by
    show sumTo (L + 1) g + g (L + 1) ≤ L + 1
    exact Nat.add_le_add (sumTo_le_tail g h0 h1 L) (h1 _)

/-- The first later revisit of a first position: query `T` of the joint
    run, at step `1` or later, at a first position no earlier later query
    reached. -/
def unpS (K : Nat) (inner : Nat → Nat → Nat) (iv n1 : Nat) (cf : Nat → Nat) (xs : List Nat) (H T : Nat) : Bool :=
  decide (n1 ≤ T) && (List.range n1).any (fun c => posS K inner iv n1 cf xs H c == posS K inner iv n1 cf xs H T) &&
    !((List.range T).any (fun τ => decide (n1 ≤ τ) && posS K inner iv n1 cf xs H τ == posS K inner iv n1 cf xs H T))

/-- **Unpaid merges number at most `L`**: at each step `q ≥ 1` the block
    `xs[q-1]` sends at most one first commitment's position (`hdx`), and
    each first position has one first later revisit. -/
theorem unpS_count {K : Nat} (inner : Nat → Nat → Nat) (iv : Nat) {n1 : Nat} (hn1 : 0 < n1) (cf : Nat → Nat)
    (hdx : ∀ s s' x a b, a < n1 → b < n1 → inner s x = inner iv (cf a) → inner s' x = inner iv (cf b) → a = b)
    (xs : List Nat) (H L : Nat) :
    sumTo (n1 * (L + 1)) (fun T => indB (unpS K inner iv n1 cf xs H T)) ≤ L := by
  let pos := posS K inner iv n1 cf xs H
  have step0 : ∀ c, c < n1 → pos c = inner iv (cf c) := fun c hc => by
    have := posS_step K inner iv hn1 cf xs H 0 c hc
    rw [Nat.zero_mul, Nat.zero_add] at this; exact this
  rw [sumTo_split n1 _ (L + 1)]
  refine sumTo_le_tail _ ?_ (fun q => ?_) L
  · refine Eq.trans (sumTo_congr _ (fun r hr => ?_)) (Eq.trans (sumTo_const 0 n1) (Nat.mul_zero n1))
    show indB (unpS K inner iv n1 cf xs H (r + n1 * 0)) = 0
    have : unpS K inner iv n1 cf xs H (r + n1 * 0) = false := by
      unfold unpS; rw [Nat.mul_zero, Nat.add_zero, decide_eq_false (Nat.not_le_of_lt hr)]; rfl
    rw [this]; rfl
  · refine sum_le_one n1 (fun r r' hr hr' u u' => ?_)
    -- both are first later revisits at step `q`, so of one first position
    unfold unpS at u u'
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at u u'
    obtain ⟨⟨hq, hc⟩, hfirst⟩ := u
    obtain ⟨⟨hq', hc'⟩, hfirst'⟩ := u'
    obtain ⟨c, hcm, ec⟩ := List.any_eq_true.1 hc
    obtain ⟨c', hcm', ec'⟩ := List.any_eq_true.1 hc'
    have ec := beq_iff_eq.1 ec
    have ec' := beq_iff_eq.1 ec'
    have hc1 := List.mem_range.1 hcm
    have hc1' := List.mem_range.1 hcm'
    have q1 : 1 ≤ q := by
      rcases Nat.eq_zero_or_pos q with h | h
      · subst h; rw [Nat.mul_zero, Nat.add_zero] at hq; exact absurd hr (Nat.not_lt_of_le hq)
      · exact h
    have pq : ∀ j, j < n1 → pos (j + n1 * q) = inner (chain1 K inner iv (cf j :: xs) H q) (xs.getD (q - 1) 0) := by
      intro j hj
      have := posS_step K inner iv hn1 cf xs H q j hj
      rw [Nat.mul_comm, Nat.add_comm]
      refine this.trans ?_
      congr 1
      conv => lhs; rw [← Nat.sub_add_cancel q1]
      rfl
    have e1 : inner (chain1 K inner iv (cf r :: xs) H q) (xs.getD (q - 1) 0) = inner iv (cf c) := by
      rw [← pq r hr, ← step0 c hc1]; exact ec.symm
    have e2 : inner (chain1 K inner iv (cf r' :: xs) H q) (xs.getD (q - 1) 0) = inner iv (cf c') := by
      rw [← pq r' hr', ← step0 c' hc1']; exact ec'.symm
    have hcc := hdx _ _ _ c c' hc1 hc1' e1 e2
    subst hcc
    have hp : pos (r + n1 * q) = pos (r' + n1 * q) := ec.symm.trans ec'
    rcases Nat.lt_trichotomy r r' with h | h | h
    · exfalso
      refine List.any_eq_false.1 hfirst' (r + n1 * q) (List.mem_range.2 (Nat.add_lt_add_right h _)) ?_
      rw [Bool.and_eq_true]; exact ⟨decide_eq_true hq, beq_iff_eq.2 hp⟩
    · exact h
    · exfalso
      refine List.any_eq_false.1 hfirst (r' + n1 * q) (List.mem_range.2 (Nat.add_lt_add_right h _)) ?_
      rw [Bool.and_eq_true]; exact ⟨decide_eq_true hq', beq_iff_eq.2 hp.symm⟩

/-- **Chains that all meet saw near-collisions, first positions
    revisited**: `allMeet_near2` without `hcf`.  A later query may land on
    a first position when its block sends some state there; each block
    sends at most one first commitment's position (`hdx`).  The first such
    revisit of each first position goes unpaid, at most `L` in all
    (`unpS_count`); a later revisit is paid by the earlier revisitor's
    predecessor, whose projection it shares (`hpk2`). -/
theorem allMeet_near3 {K Kc : Nat} (inner : Nat → Nat → Nat) (hin : ∀ s x, inner s x < K) (κ : Nat → Nat)
    (hκ : ∀ u, κ u < Kc) (hpk2 : ∀ s s' x x', inner s x = inner s' x' → κ s = κ s') (iv : Nat) {n1 : Nat}
    (hn1 : 0 < n1) (cf : Nat → Nat) (hd : ∀ a b, a < n1 → b < n1 → a ≠ b → inner iv (cf a) ≠ inner iv (cf b))
    (hdx : ∀ s s' x a b, a < n1 → b < n1 → inner s x = inner iv (cf a) → inner s' x = inner iv (cf b) → a = b)
    (xs : List Nat) {H : Nat} (hP : permB K H = true) (L : Nat)
    {v : Nat} (hall : ∀ j, j < n1 → chain1 K inner iv (cf j :: xs) H (L + 1) = v) :
    n1 ≤ 1 + L + nearN K (fun a b => decide (κ a = κ b)) (runAdp K (nxtS inner iv n1 cf xs) H (n1 * (L + 1))) := by
  have hK : 0 < K := Nat.lt_of_le_of_lt (Nat.zero_le _) (hin 0 0)
  let pos := posS K inner iv n1 cf xs H
  let kap := fun τ => κ (rget K (pos τ) H)
  let ch := fun τ => τ % n1
  have step0 : ∀ j, j < n1 → pos j = inner iv (cf j) := fun j hj => by
    have := posS_step K inner iv hn1 cf xs H 0 j hj
    rw [Nat.zero_mul, Nat.zero_add] at this; exact this
  have prevpos : ∀ T, n1 ≤ T → pos T = inner (rget K (pos (T - n1)) H) (xs.getD (T / n1 - 1) 0) := fun T hT => by
    have hj := Nat.mod_lt T hn1
    have hq : 1 ≤ T / n1 := (Nat.le_div_iff_mul_le hn1).2 (by rw [Nat.one_mul]; exact hT)
    have hdm : T = T / n1 * n1 + T % n1 := by rw [Nat.mul_comm]; exact (Nat.div_add_mod T n1).symm
    have e1 : T = (T / n1 - 1 + 1) * n1 + T % n1 := by rw [Nat.sub_add_cancel hq]; exact hdm
    have e2 : T - n1 = (T / n1 - 1) * n1 + T % n1 := by
      have hge : n1 ≤ T / n1 * n1 := by
        calc n1 = 1 * n1 := (Nat.one_mul _).symm
          _ ≤ T / n1 * n1 := Nat.mul_le_mul_right _ hq
      rw [Nat.sub_mul, Nat.one_mul]; omega
    show posS K inner iv n1 cf xs H T = inner (rget K (posS K inner iv n1 cf xs H (T - n1)) H) _
    rw [e2]; conv => lhs; rw [e1]
    exact posS_next K inner iv hn1 cf xs H _ _ hj
  have chm : ∀ τ, n1 ≤ τ → ch (τ - n1) = ch τ := fun τ h => by
    show (τ - n1) % n1 = τ % n1
    conv => rhs; rw [← Nat.sub_add_cancel h]
    rw [Nat.add_mod_right]
  have hfin := labR_finalU n1 pos ch kap (unpS K inner iv n1 cf xs H) (fun τ => Nat.mod_lt τ hn1) (fun τ => hκ _)
    (fun τ τ' e => by show κ (rget K (pos τ) H) = κ (rget K (pos τ') H); rw [e])
    (n1 * (L + 1)) (pos (L * n1))
    (fun T τ0 hT hτ0 e _ hu => by
      rcases Nat.lt_or_ge τ0 n1 with h0 | h0
      · rcases Nat.lt_or_ge T n1 with h1 | h1
        · exfalso
          rw [step0 τ0 h0, step0 T h1] at e
          exact hd τ0 T h0 h1 (Nat.ne_of_lt hτ0) e
        · -- a revisit of a first position, not the first: an earlier revisitor pays
          have hany : (List.range T).any (fun τ => decide (n1 ≤ τ) && pos τ == pos T) = true := by
            unfold unpS at hu
            have hfp : (List.range n1).any (fun c => posS K inner iv n1 cf xs H c == posS K inner iv n1 cf xs H T) = true :=
              List.any_eq_true.2 ⟨τ0, List.mem_range.2 h0, beq_iff_eq.2 e⟩
            rw [decide_eq_true h1, hfp, Bool.true_and, Bool.true_and, Bool.not_eq_false'] at hu
            exact hu
          obtain ⟨τ', hτ'm, hτ'⟩ := List.any_eq_true.1 hany
          rw [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hτ'
          obtain ⟨h2, e2⟩ := hτ'
          have hτ'T := List.mem_range.1 hτ'm
          refine ⟨T - n1, τ' - n1, by omega, by omega, ?_, ?_, ?_⟩
          · show labR pos ch T (ch (T - n1)) = labR pos ch T (ch T); rw [chm T h1]
          · show labR pos ch T (ch (τ' - n1)) = labR pos ch T (ch τ0)
            rw [chm τ' h2]
            exact labR_coh pos ch T τ' τ0 hτ'T hτ0 (e2.trans e.symm)
          · show κ (rget K (pos (T - n1)) H) = κ (rget K (pos (τ' - n1)) H)
            have ee := e2
            rw [prevpos T h1, prevpos τ' h2] at ee
            exact (hpk2 _ _ _ _ ee).symm
      · have h1 : n1 ≤ T := Nat.le_trans h0 (Nat.le_of_lt hτ0)
        refine ⟨T - n1, τ0 - n1, by omega, by omega, ?_, ?_, ?_⟩
        · show labR pos ch T (ch (T - n1)) = labR pos ch T (ch T); rw [chm T h1]
        · show labR pos ch T (ch (τ0 - n1)) = labR pos ch T (ch τ0); rw [chm τ0 h0]
        · show κ (rget K (pos (T - n1)) H) = κ (rget K (pos (τ0 - n1)) H)
          rw [prevpos T h1, prevpos τ0 h0] at e
          exact (hpk2 _ _ _ _ e).symm)
    (fun j hj => ⟨L * n1 + j, by
      calc L * n1 + j < L * n1 + n1 := Nat.add_lt_add_left hj _
        _ = n1 * (L + 1) := by rw [Nat.mul_comm n1, Nat.succ_mul],
      by show (L * n1 + j) % n1 = j; rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj], by
      refine permB_inj hP (hin _ _) (hin _ _) ?_
      show rget K (posS K inner iv n1 cf xs H (L * n1 + j)) H = rget K (posS K inner iv n1 cf xs H (L * n1)) H
      rw [rget_posS, rget_posS]
      have a1 : (L * n1 + j) % n1 = j := by rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]
      have a2 : (L * n1 + j) / n1 = L := by rw [Nat.add_comm, Nat.add_mul_div_right _ _ hn1, Nat.div_eq_of_lt hj, Nat.zero_add]
      have b1 : (L * n1) % n1 = 0 := Nat.mul_mod_left _ _
      have b2 : (L * n1) / n1 = L := Nat.mul_div_cancel _ hn1
      rw [a1, a2, b1, b2, hall j hj, hall 0 hn1]⟩)
  have hU := unpS_count (K := K) inner iv hn1 cf hdx xs H L
  rw [nearN_runS hK inner κ iv hn1 cf xs H]
  show n1 ≤ 1 + L + sumTo (n1 * (L + 1)) (fun τ => indB (nearInc pos kap τ))
  omega

/-- **0.8's absorption sends each block to at most one first
    commitment's position**: the input's rate part is the block's values,
    and a full-rate first commitment's is the commitment itself. -/
theorem inner08_hdx {R p Q n1 : Nat} (hR : 0 < R) (hp : 0 < p) (hn : n1 ≤ p ^ R) (iv : Nat) :
    ∀ s s' x c c', c < n1 → c' < n1 → inner08 R (p ^ R) p Q s x = inner08 R (p ^ R) p Q iv c →
      inner08 R (p ^ R) p Q s' x = inner08 R (p ^ R) p Q iv c' → c = c' := by
  have rate : ∀ u y, inner08 R (p ^ R) p Q u y % p ^ R = vals08 R p y := fun u y => by
    unfold inner08; rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (vals08_lt hR hp y)]
  have full : ∀ c, c < p ^ R → vals08 R p c = c := fun c hc => by unfold vals08; rw [if_pos hc]
  intro s s' x c c' hc hc' e e'
  have a := congrArg (· % p ^ R) e
  have a' := congrArg (· % p ^ R) e'
  simp only [rate] at a a'
  rw [full c (Nat.lt_of_lt_of_le hc hn)] at a
  rw [full c' (Nat.lt_of_lt_of_le hc' hn)] at a'
  exact a.symm.trans a'

/-- **Chains that all meet are rare, first positions revisited**: `n1`
    chains from distinct first positions, each block sending at most one
    first commitment's position (`hdx`), all reach one state after `L + 1`
    absorptions on at most `((0 + ⋯ + (n1 (L+1) - 1)) F)^e / (e! (K - n1 (L+1))^e)`
    of the permutation tables, `e = n1 - 1 - L` (`allMeet_near3`, `nearN_tail`). -/
theorem allMeet_countP3 {K Kc F : Nat} (hK : 0 < K) (inner : Nat → Nat → Nat) (hin : ∀ s x, inner s x < K) (κ : Nat → Nat)
    (hκ : ∀ u, κ u < Kc) (hF : ∀ v, sumTo K (fun u => indB (decide (κ u = v))) ≤ F)
    (hpk2 : ∀ s s' x x', inner s x = inner s' x' → κ s = κ s') (iv : Nat) {n1 : Nat} (hn1 : 0 < n1)
    (cf : Nat → Nat) (hd : ∀ a b, a < n1 → b < n1 → a ≠ b → inner iv (cf a) ≠ inner iv (cf b)) (xs : List Nat) (L : Nat)
    (hdx : ∀ s s' x a b, a < n1 → b < n1 → inner s x = inner iv (cf a) → inner s' x = inner iv (cf b) → a = b) :
    fact (n1 - 1 - L) * ((K - n1 * (L + 1)) ^ (n1 - 1 - L) * sumTo (K ^ K) (fun H => indB (permB K H &&
        (List.range n1).all (fun j => chain1 K inner iv (cf j :: xs) H (L + 1) == chain1 K inner iv (cf 0 :: xs) H (L + 1))))) ≤
      (sumTo (n1 * (L + 1)) (fun j => j) * F) ^ (n1 - 1 - L) * sumTo (K ^ K) (fun H => indB (permB K H)) := by
  have hnx : ∀ l, nxtS inner iv n1 cf xs l < K := fun l => by unfold nxtS; split <;> exact hin _ _
  refine Nat.le_trans (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (sumTo_mono _ (fun H _ => ?_))))
    (nearN_tail hK (fun a b => decide (κ a = κ b)) (rel_symm κ) (fib_rel κ hF) (nxtS inner iv n1 cf xs) hnx (n1 * (L + 1)) (n1 - 1 - L))
  cases hP : permB K H
  · exact Nat.zero_le _
  cases ha : (List.range n1).all (fun j => chain1 K inner iv (cf j :: xs) H (L + 1) == chain1 K inner iv (cf 0 :: xs) H (L + 1))
  · exact Nat.zero_le _
  · have hall : ∀ j, j < n1 → chain1 K inner iv (cf j :: xs) H (L + 1) = chain1 K inner iv (cf 0 :: xs) H (L + 1) :=
      fun j hj => beq_iff_eq.1 (List.all_eq_true.1 ha j (List.mem_range.2 hj))
    have hm := allMeet_near3 inner hin κ hκ hpk2 iv hn1 cf hd hdx xs hP L hall
    have : n1 - 1 - L ≤ nearN K (fun a b => decide (κ a = κ b)) (runAdp K (nxtS inner iv n1 cf xs) H (n1 * (L + 1))) := by omega
    rw [decide_eq_true this]; exact Nat.le_refl _

/-- **Meeting tuples averaged over a uniform permutation, first positions
    revisited**: each block sending at most one first commitment's position
    (`hdxC`), `e! (K - t (L+1))^e` times the summed `meetM` is at most
    `n1^t ((0 + ⋯ + (t (L+1) - 1)) F)^e` per permutation table,
    `e = t - 1 - L`. -/
theorem meetM_countP3 {K Kc F : Nat} (hK : 0 < K) (inner : Nat → Nat → Nat) (hin : ∀ s x, inner s x < K) (κ : Nat → Nat)
    (hκ : ∀ u, κ u < Kc) (hF : ∀ v, sumTo K (fun u => indB (decide (κ u = v))) ≤ F)
    (hpk2 : ∀ s s' x x', inner s x = inner s' x' → κ s = κ s') (iv : Nat) {n1 : Nat} (hn : 0 < n1)
    (hd : ∀ a b, a < n1 → b < n1 → a ≠ b → inner iv a ≠ inner iv b) (xs : List Nat) (L : Nat)
    (hdxC : ∀ s s' x c c', c < n1 → c' < n1 → inner s x = inner iv c → inner s' x = inner iv c' → c = c')
    {t : Nat} (ht : 0 < t) :
    fact (t - 1 - L) * ((K - t * (L + 1)) ^ (t - 1 - L) * sumTo (K ^ K) (fun H => indB (permB K H) * meetM K inner iv n1 xs L t H)) ≤
      n1 ^ t * ((sumTo (t * (L + 1)) (fun j => j) * F) ^ (t - 1 - L) * sumTo (K ^ K) (fun H => indB (permB K H))) := by
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
    have hdxT : ∀ s s' x i j, i < t → j < t → inner s x = inner iv (rget n1 i a) → inner s' x = inner iv (rget n1 j a) →
        i = j := fun s s' x i j hi' hj e1 e2 =>
      Decidable.byContradiction (fun hij => injT_ne hn t a hi i j hi' hj hij
        (hdxC s s' x _ _ (rget_lt hn _ _) (rget_lt hn _ _) e1 e2))
    have hc := allMeet_countP3 hK inner hin κ hκ hF hpk2 iv ht (fun j => rget n1 j a) hdT xs L hdxT
    refine Nat.le_trans (Nat.le_of_eq ?_) hc
    congr 2
    refine sumTo_congr _ (fun H _ => ?_)
    rw [Bool.true_and, indB_and']


/-- The tuple load for every later transcript. -/
def loadTR (K : Nat) (inner : Nat → Nat → Nat) (iv n1 : Nat) (X L t s0 H : Nat) : Nat :=
  (s0 - 1) + n1 * sumTo (X ^ L) (fun i => indB (decide (ffac s0 t ≤ meetM K inner iv n1 (xsOf X L i) L t H)))

theorem preimage_loadTR (K : Nat) (inner : Nat → Nat → Nat) (iv : Nat) {n1 : Nat} (hn : 0 < n1)
    {X : Nat} (hX : 0 < X) (L t s0 : Nat) (xs : List Nat) (hxs : ∀ m, m < L → xs.getD m 0 < X)
    (H v : Nat) :
    sumTo n1 (fun c => indB (decide (chain1 K inner iv (c :: xs) H (L + 1) = v))) ≤ loadTR K inner iv n1 X L t s0 H := by
  obtain ⟨i, hi, hag⟩ := xsOf_cover hX xs hxs
  have hch : ∀ c, chain1 K inner iv (c :: xs) H (L + 1) = chain1 K inner iv (c :: xsOf X L i) H (L + 1) :=
    fun c => chain1_congr K inner iv _ _ H (L + 1) (fun j hj => by
      cases j with
      | zero => rfl
      | succ j => exact hag j (Nat.lt_of_succ_lt_succ hj))
  rw [sumTo_congr _ (fun c _ => by rw [hch c])]
  refine Nat.le_trans (preimage_loadT K inner iv hn (xsOf X L i) L t s0 H v) ?_
  unfold loadT loadTR
  exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (le_sumTo (fun i => indB
    (decide (ffac s0 t ≤ meetM K inner iv n1 (xsOf X L i) L t H))) _ hi)) _

/-- **Markov for meeting tuples**: per later block list. -/
theorem meet_markov3 {K Kc F : Nat} (hK : 0 < K) (inner : Nat → Nat → Nat) (hin : ∀ s x, inner s x < K) (κ : Nat → Nat)
    (hκ : ∀ u, κ u < Kc) (hF : ∀ v, sumTo K (fun u => indB (decide (κ u = v))) ≤ F)
    (hpk2 : ∀ s s' x x', inner s x = inner s' x' → κ s = κ s') (iv : Nat) {n1 : Nat} (hn : 0 < n1)
    (hd : ∀ a b, a < n1 → b < n1 → a ≠ b → inner iv a ≠ inner iv b) (xs : List Nat) (L : Nat)
    (hdxC : ∀ s s' x c c', c < n1 → c' < n1 → inner s x = inner iv c → inner s' x = inner iv c' → c = c')
    {t : Nat} (ht : 0 < t) (s0 : Nat) :
    fact (t - 1 - L) * (K - t * (L + 1)) ^ (t - 1 - L) * (ffac s0 t * sumTo (K ^ K) (fun H =>
        indB (permB K H && decide (ffac s0 t ≤ meetM K inner iv n1 xs L t H)))) ≤
      n1 ^ t * (sumTo (t * (L + 1)) (fun j => j) * F) ^ (t - 1 - L) * sumTo (K ^ K) (fun H => indB (permB K H)) := by
  have hm0 := meetM_countP3 hK inner hin κ hκ hF hpk2 iv hn hd xs L hdxC ht
  have mk : ffac s0 t * sumTo (K ^ K) (fun H => indB (permB K H && decide (ffac s0 t ≤ meetM K inner iv n1 xs L t H))) ≤
      sumTo (K ^ K) (fun H => indB (permB K H) * meetM K inner iv n1 xs L t H) := by
    rw [sumTo_mul]
    refine sumTo_mono _ (fun H _ => ?_)
    cases permB K H
    · simp [indB]
    · by_cases h : ffac s0 t ≤ meetM K inner iv n1 xs L t H
      · rw [decide_eq_true h]; simp only [Bool.true_and, show indB true = 1 from rfl, Nat.mul_one, Nat.one_mul]; exact h
      · rw [decide_eq_false h]; simp [indB]
  calc fact (t - 1 - L) * (K - t * (L + 1)) ^ (t - 1 - L) * (ffac s0 t * sumTo (K ^ K) (fun H =>
        indB (permB K H && decide (ffac s0 t ≤ meetM K inner iv n1 xs L t H))))
      ≤ fact (t - 1 - L) * (K - t * (L + 1)) ^ (t - 1 - L) * sumTo (K ^ K) (fun H => indB (permB K H) * meetM K inner iv n1 xs L t H) :=
        Nat.mul_le_mul_left _ mk
    _ = fact (t - 1 - L) * ((K - t * (L + 1)) ^ (t - 1 - L) * sumTo (K ^ K) (fun H => indB (permB K H) * meetM K inner iv n1 xs L t H)) :=
        Nat.mul_assoc _ _ _
    _ ≤ _ := by rw [Nat.mul_assoc (n1 ^ t)]; exact hm0

/-- **The tuple load averaged**: `e = t - 1 - L`, `Q = e! (K - t (L+1))^e`,
    `f = s0 (s0-1) ⋯ (s0-t+1)`; `Q f` times the summed `loadTR` is at most
    `Q f (s0 - 1) + n1 X^L n1^t ((0 + ⋯ + (t (L+1) - 1)) F)^e` per
    permutation table. -/
theorem loadTR_countP {K Kc F : Nat} (hK : 0 < K) (inner : Nat → Nat → Nat) (hin : ∀ s x, inner s x < K) (κ : Nat → Nat)
    (hκ : ∀ u, κ u < Kc) (hF : ∀ v, sumTo K (fun u => indB (decide (κ u = v))) ≤ F)
    (hpk2 : ∀ s s' x x', inner s x = inner s' x' → κ s = κ s') (iv : Nat) {n1 : Nat} (hn : 0 < n1)
    (hd : ∀ a b, a < n1 → b < n1 → a ≠ b → inner iv a ≠ inner iv b)
    (hdxC : ∀ s s' x c c', c < n1 → c' < n1 → inner s x = inner iv c → inner s' x = inner iv c' → c = c') (X L : Nat) {t : Nat} (ht : 0 < t) (s0 : Nat) :
    fact (t - 1 - L) * (K - t * (L + 1)) ^ (t - 1 - L) * ffac s0 t * sumTo (K ^ K) (fun H => indB (permB K H) * loadTR K inner iv n1 X L t s0 H) ≤
      (fact (t - 1 - L) * (K - t * (L + 1)) ^ (t - 1 - L) * ffac s0 t * (s0 - 1) +
        n1 * (X ^ L * (n1 ^ t * (sumTo (t * (L + 1)) (fun j => j) * F) ^ (t - 1 - L)))) * sumTo (K ^ K) (fun H => indB (permB K H)) := by
  let bad := fun i H => indB (permB K H && decide (ffac s0 t ≤ meetM K inner iv n1 (xsOf X L i) L t H))
  have each : ∀ i, fact (t - 1 - L) * (K - t * (L + 1)) ^ (t - 1 - L) * (ffac s0 t * sumTo (K ^ K) (fun H => bad i H)) ≤
      n1 ^ t * (sumTo (t * (L + 1)) (fun j => j) * F) ^ (t - 1 - L) * sumTo (K ^ K) (fun H => indB (permB K H)) :=
    fun i => meet_markov3 hK inner hin κ hκ hF hpk2 iv hn hd (xsOf X L i) L hdxC ht s0
  have e : ∀ H, indB (permB K H) * loadTR K inner iv n1 X L t s0 H = indB (permB K H) * (s0 - 1) +
      n1 * sumTo (X ^ L) (fun i => bad i H) := fun H => by
    unfold loadTR
    rw [Nat.mul_add, Nat.mul_left_comm, sumTo_mul]
    congr 2
    exact sumTo_congr _ (fun i _ => indB_and' _ _)
  have e2 : sumTo (K ^ K) (fun H => indB (permB K H) * (s0 - 1)) = (s0 - 1) * sumTo (K ^ K) (fun H => indB (permB K H)) := by
    rw [sumTo_mul]; exact sumTo_congr _ (fun H _ => Nat.mul_comm _ _)
  rw [sumTo_congr _ (fun H _ => e H), sumTo_add, e2, ← sumTo_mul, sumTo_exch _ (X ^ L) (K ^ K)]
  generalize hPi : sumTo (K ^ K) (fun H => indB (permB K H)) = Pi0 at *
  generalize hQ : fact (t - 1 - L) * (K - t * (L + 1)) ^ (t - 1 - L) = Q at *
  generalize hW : n1 ^ t * (sumTo (t * (L + 1)) (fun j => j) * F) ^ (t - 1 - L) = W at *
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
    `m % n1` and the later blocks `enc (m / n1) w`, each below `X`; the table's `δs' = δs loadTR` meets `hsp1` and
    `hφsp` for every `d`, `rest`, `w` and `v` (`s0 ≥ 2`). -/
theorem loadTR_hsp {D W : Type} {K NS1 n1 δs X : Nat} (inner : Nat → Nat → Nat) (iv : Nat) (hX : 0 < X) (L t : Nat)
    (enc : Nat → W → List Nat) (henc : ∀ r w i, i < L → (enc r w).getD i 0 < X)
    (Com1 : D → Nat → Nat) (hr1 : ∀ d σ, Com1 d σ < n1)
    (hsp1 : ∀ d v, sumTo NS1 (fun σ => indB (decide (Com1 d σ = v))) ≤ δs) {s0 : Nat} (hs0 : 2 ≤ s0) (H : Nat) :
    (∀ d v, sumTo NS1 (fun σ => indB (decide (Com1 d σ = v))) ≤ δs * loadTR K inner iv n1 X L t s0 H) ∧
      (∀ d rest w v, sumTo NS1 (fun σ1 => indB (decide
        ((fun m' w => chain1 K inner iv ((m' % n1) :: enc (m' / n1) w) H (L + 1)) (Com1 d σ1 + n1 * rest) w = v))) ≤
        δs * loadTR K inner iv n1 X L t s0 H) := by
  have h1 : 1 ≤ loadTR K inner iv n1 X L t s0 H := Nat.le_trans (Nat.le_sub_of_add_le hs0) (Nat.le_add_right _ _)
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
  exact Nat.mul_le_mul_left _ (preimage_loadTR K inner iv hn1 hX L t s0 (enc rest w) (henc rest w) H v)

theorem loadTR_δs_countP {K Kc F : Nat} (hK : 0 < K) (inner : Nat → Nat → Nat) (hin : ∀ s x, inner s x < K) (κ : Nat → Nat)
    (hκ : ∀ u, κ u < Kc) (hF : ∀ v, sumTo K (fun u => indB (decide (κ u = v))) ≤ F)
    (hpk2 : ∀ s s' x x', inner s x = inner s' x' → κ s = κ s') (iv : Nat) {n1 : Nat} (hn : 0 < n1)
    (hd : ∀ a b, a < n1 → b < n1 → a ≠ b → inner iv a ≠ inner iv b)
    (hdxC : ∀ s s' x c c', c < n1 → c' < n1 → inner s x = inner iv c → inner s' x = inner iv c' → c = c') (X L : Nat) {t : Nat} (ht : 0 < t) (s0 δs : Nat) :
    fact (t - 1 - L) * (K - t * (L + 1)) ^ (t - 1 - L) * ffac s0 t *
        sumTo (K ^ K) (fun H => indB (permB K H) * (δs * loadTR K inner iv n1 X L t s0 H)) ≤
      δs * ((fact (t - 1 - L) * (K - t * (L + 1)) ^ (t - 1 - L) * ffac s0 t * (s0 - 1) +
        n1 * (X ^ L * (n1 ^ t * (sumTo (t * (L + 1)) (fun j => j) * F) ^ (t - 1 - L)))) * sumTo (K ^ K) (fun H => indB (permB K H))) := by
  have h := loadTR_countP hK inner hin κ hκ hF hpk2 iv hn hd hdxC X L ht s0
  rw [sumTo_congr _ (fun H _ => Nat.mul_left_comm _ _ _), ← sumTo_mul, Nat.mul_left_comm]
  exact Nat.mul_le_mul_left _ h

/-- The spread the permutation `H` gives proof `ix`: `δ0 ix loadTR`. -/
def δsR (K : Nat) (inner : Nat → Nat → Nat) (iv n1 : Nat) (X L t s0 : Nat) (δ0 : Nat → Nat) (H ix : Nat) : Nat :=
  δ0 ix * loadTR K inner iv n1 X L t s0 H


section
open B Air Stmt Mach Sudoku SudokuText Compose CompM Wit

set_option maxRecDepth 100000 in
/-- **`sud_interleaveS` averaged over a uniform permutation, the index
    after the first commitment and any `L` later blocks** (`loadφA`): at each permutation table `P` with
    `δsR P = δ0 loadTR` (`loadTR_hsp`); the error the permutation-weighted
    sum of the tables' errors (`zkbT_avgW`). -/
theorem sud_interleaveLR {V Wv P1 P2 P3 W1 W2 W3 : Type} {kr kq : Nat} (φ1 : Nat → Nat → W1 → Nat) (nx1 : Nat → Nat → Nat → List Nat → Nat × Nat × W1) (G1 : Nat → Nat → Nat → List (List (List F)) → Nat → List Nat → P1) (φ2 : Nat → Nat → W2 → Nat) (nx2 : Nat → Nat → Nat → List Nat → Nat × Nat × W2) (G2 : Nat → Nat → Nat → List (List (List F)) → Nat → List Nat → P2) (φ3 : Nat → Nat → W3 → Nat) (nx3 : Nat → Nat → Nat → List Nat → Nat × Nat × W3) (G3 : Nat → Nat → Nat → List (List (List (List F))) × List (List (List F)) → Nat → List Nat → P3)
     (off : EF → String → EF) {puzzle : ∀ ix : Nat, List Nat} (hc : ∀ ix : Nat, CluesOK (cluesOf (puzzle ix))) {ρ : ∀ ix : Nat, Nat → Bool} {A : ∀ ix : Nat, List Cell} {k : ∀ ix : Nat, Nat} {row : ∀ ix : Nat, Nat → Air.Row} (hA : ∀ ix : Nat, AcceptsFrom (A ix) (stmtMachine (ρ ix) 729 (sudokuExpr (cluesOf (puzzle ix))) ACC REJ) (k ix) (row ix)) (hacc : ∀ ix : Nat, rd (A ix) ((row ix) ((k ix) - 1)).ctr ((row ix) ((k ix) - 1)).hd = some (.atom ACC)) (hlen : ∀ ix : Nat, (A ix).length = 2 ^ 16) (hk : ∀ ix : Nat, (k ix) ≤ 2 ^ 16) {tP : ∀ ix : Nat, Nat} (htp : ∀ ix : Nat, (tP ix) = progTp (stmtMachine (fun _ => false) 729 (sudokuExpr (cluesOf (puzzle ix))) ACC REJ).heap) (S16 S10 SP : ∀ ix : Nat, Nat → List F) (qv : ∀ ix : Nat, EF → EF → List EF → F → List F → List F → List EF) (wm wc ww wp : ∀ ix : Nat, Nat → List (EF → EF → List F)) {Lwm Lwc Lww Lwp : ∀ ix : Nat, Nat} (hlwm : ∀ ix : Nat, ∀ c, ((wm ix) c).length = (Lwm ix)) (hlwc : ∀ ix : Nat, ∀ c, ((wc ix) c).length = (Lwc ix)) (hlww : ∀ ix : Nat, ∀ c, ((ww ix) c).length = (Lww ix)) (hlwp : ∀ ix : Nat, ∀ c, ((wp ix) c).length = (Lwp ix)) {K2 K4 : Nat} (hK2 : 0 < K2) (hK4 : 0 < K4) (hS16 : ∀ ix : Nat, ∀ c4, ∀ x ∈ (S16 ix) c4, x ∉ cosetL 1 (bbGen 16) (2 ^ 16)) (hS10 : ∀ ix : Nat, ∀ c4, ∀ x ∈ (S10 ix) c4, x ∉ cosetL 1 (bbGen 10) (2 ^ 10)) (hSP : ∀ ix : Nat, ∀ c4, ∀ x ∈ (SP ix) c4, x ∉ cosetL 1 (bbGen ((tP ix) + 1)) (2 ^ ((tP ix) + 1))) (hsz16 : ∀ ix : Nat, ∀ c4, 2 * ((S16 ix) c4).length + 8 ≤ 2 ^ 16) (hsz : ∀ ix : Nat, ∀ c4, 2 * ((S10 ix) c4).length + 8 ≤ 2 ^ 10) (hszP : ∀ ix : Nat, ∀ c4, 2 * ((SP ix) c4).length + 8 ≤ 2 ^ ((tP ix) + 1)) {ncw : ∀ ix : Nat, Nat} (αd : ∀ ix : Nat, Nat → EF) {B4 : ∀ ix : Nat, Nat} (hB4 : ∀ ix : Nat, sumTo K4 (fun c4 => indB (!genB ((αd ix) c4))) ≤ (B4 ix)) (fri : ∀ ix : Nat, Nat → EF → EF → List (EF → EF) → V) (hncw : ∀ ix : Nat, 4 ≤ (ncw ix)) (NR2 : ∀ ix : Nat, Nat) (Rb : ∀ ix : Nat, Nat → EF → EF → Nat → List (EF → EF)) (Ro : ∀ ix : Nat, Nat → EF → EF → Nat → Wv) {n1 n2 n3 : Nat} {NS1 NS2 NS3 : ∀ ix : Nat, Nat} (Com1 : ∀ ix : Nat, List (List (List F)) → Nat → Nat) (hc1 : ∀ ix : Nat, ComHides (NS1 ix) (Com1 ix)) (hp1 : ∀ ix : Nat, ∀ c4 T1 T2 T3 T4 M, ComPfHides (NS1 ix) (Com1 ix) ((pfRdM (Q4 * Q4) K2 Q4 K4 n1 kr (φ1 ix) (nx1 ix) (G1 ix)) c4 T1 T2 T3 T4 M) (opF ((sudGroups (tP ix) ((S16 ix) c4) ((S10 ix) c4) ((SP ix) c4) EF.zero (qv ix)).map (·.base.S)) [0, 2, 4, 6])) (hr1 : ∀ ix : Nat, ∀ d σ, (Com1 ix) d σ < n1) (d1 : ∀ ix : Nat, List (List (List F))) (Com2 : ∀ ix : Nat, List (List (List F)) → Nat → Nat) (hc2 : ∀ ix : Nat, ComHides (NS2 ix) (Com2 ix)) (hp2 : ∀ ix : Nat, ∀ c4 T1 T2 T3 T4 M, ComPfHides (NS2 ix) (Com2 ix) ((pfRdM (Q4 * Q4) K2 Q4 K4 n1 kr (φ2 ix) (nx2 ix) (G2 ix)) c4 T1 T2 T3 T4 M) (opF ((sudGroups (tP ix) ((S16 ix) c4) ((S10 ix) c4) ((SP ix) c4) EF.zero (qv ix)).map (·.base.S)) [1, 3, 5, 7])) (hr2 : ∀ ix : Nat, ∀ d σ, (Com2 ix) d σ < n2) (d2 : ∀ ix : Nat, List (List (List F))) (Com3 : ∀ ix : Nat, List (List (List (List F))) × List (List (List F)) → Nat → Nat) (hc3 : ∀ ix : Nat, ComHides (NS3 ix) (Com3 ix)) (hp3 : ∀ ix : Nat, ∀ c4 T1 T2 T3 T4 M, ComPfHides (NS3 ix) (Com3 ix) ((pfRdM (Q4 * Q4) K2 Q4 K4 n1 kr (φ3 ix) (nx3 ix) (G3 ix)) c4 T1 T2 T3 T4 M) (fun d => (opQ (sudSsT ((S16 ix) c4) ((S10 ix) c4) ((SP ix) c4)) d.1, opCw (sudSsC (tP ix) ((S16 ix) c4) ((S10 ix) c4) ((SP ix) c4)) d.2))) (hr3 : ∀ ix : Nat, ∀ d σ, (Com3 ix) d σ < n3) (d3 : ∀ ix : Nat, List (List (List (List F))) × List (List (List F)))
    {Kp : Nat} (hKp : 0 < Kp) (inner : Nat → Nat → Nat) (hin : ∀ s x, inner s x < Kp) (κ : Nat → Nat) {Kc : Nat}
    (hκ : ∀ u, κ u < Kc) (hpk2 : ∀ s s' x x', inner s x = inner s' x' → κ s = κ s') (iv : Nat)
    (hd : ∀ a b, a < n1 → b < n1 → a ≠ b → inner iv a ≠ inner iv b)
    (hdxC : ∀ s s' x c c', c < n1 → c' < n1 → inner s x = inner iv c → inner s' x = inner iv c' → c = c')
    {X : Nat} (hX : 0 < X) (L : Nat) (enc : Nat → Option (List (List (List EF)) × List (List (List (List EF))) × List (List (List EF))) → List Nat) (henc : ∀ r w i, i < L → (enc r w).getD i 0 < X)
    (δ0 : Nat → Nat)
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
            cond (isQ n) 0 (((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) n).NS * (((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) n).NR * (Q4 ^ 2 * δsR Kp inner iv n1 X L t s0 δ0 P n))))))) n))) := by
  intro n
  exact zkbT_avgW (fun P => indB (permB Kp P)) (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo (K4 ^ Kp) (fun H4 => sumTo ((Q4 * Q4) ^ n1) (fun H1 => sumTo (K2 ^ (n1 * n2)) (fun H2 => sumTo (Q4 ^ (n1 * (n2 * n3))) (fun H3 => f (H1, H2, H3, H4)))))) (smPowD (X := fun _ => Nat × Nat × Nat × (Nat → Tup)) (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc 0) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).sm 2) n) (scPowD (C := fun _ => Nat × Nat × Nat × Nat) (fun _ => (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo K4 (fun c4 => sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo Q4 (fun c3 => f (c1, c2, c3, c4))))))) n)
    (fun P => (rvPowD (mixRv (Q4 * Q4) K2 Q4 K4 kq isQ nxtQ
        (fun i => read4T (Q4 * Q4) K2 Q4 K4 ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).m1 ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).m2 ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).m3 ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).q ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).out)) n)) (fun P => (pgPowD (pgRd (Q4 * Q4) K2 Q4 K4 (fun i => !isQ i) (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).pts) (fun _ c => c)) n)) (fun P => (svPowDT (pgRd (Q4 * Q4) K2 Q4 K4 (fun i => !isQ i) (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).pts) (fun _ c => c))
        (mixSv (Q4 * Q4) K2 Q4 K4 kq isQ nxtQ (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).sv)) n))
    (fun P => (errPowD (fun _ => (K4 * (Q4 * Q4 * (K2 * Q4)))) (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).sm 2) (fun _ => (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo K4 (fun c4 => sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo Q4 (fun c3 => f (c1, c2, c3, c4))))))) (fun i => cond (isQ i) 0 ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).ε)
        (fun n => (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo K4 (fun c4 => sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo Q4 (fun c3 => f (c1, c2, c3, c4)))))) (fun _ => (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo (K4 ^ Kp) (fun H4 => sumTo ((Q4 * Q4) ^ n1) (fun H1 => sumTo (K2 ^ (n1 * n2)) (fun H2 => sumTo (Q4 ^ (n1 * (n2 * n3))) (fun H3 => f (H1, H2, H3, H4)))))) (fun _ => smPowD (X := fun _ => Nat × Nat × Nat × (Nat → Tup)) (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).sm 2) n
          (fun _ => rSum (fun i => cond (isQ i) kq (4 + 3 * kr)) n *
            cond (isQ n) 0 (((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) n).NS * (((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) n).NR * (Q4 ^ 2 * δsR Kp inner iv n1 X L t s0 δ0 P n))))))) n)) (fun P _ hw =>
    sud_interleaveS φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3 off hc hA hacc hlen hk htp S16 S10 SP qv wm wc ww wp hlwm hlwc hlww hlwp
      hK2 hK4 (loadφA Kp inner iv n1 L enc P) (fun _ _ _ => rget_lt hKp _ _) hS16 hS10 hSP hsz16 hsz hszP αd hB4 fri hncw NR2 Rb Ro
      Com1 hc1 hp1 hr1 d1 Com2 hc2 hp2 hr2 d2 Com3 hc3 hp3 hr3 d3 (δsR Kp inner iv n1 X L t s0 δ0 P)
      (fun ix => (loadTR_hsp inner iv hX L t enc henc (Com1 ix) (hr1 ix) (hsp1 ix) hs0 P).1)
      (fun ix => (loadTR_hsp inner iv hX L t enc henc (Com1 ix) (hr1 ix) (hsp1 ix) hs0 P).2) isQ nxtQ n)


-- The statement unfolds `sudDD`'s fields at every `ix`; elaborating it exceeds the default heartbeats.
set_option maxHeartbeats 6000000 in
set_option maxRecDepth 100000 in
/-- **`sud_interleaveLR` with a number for its error**: `e = t - 1 - L`,
    `Kq = e! (Kp - t (L+1))^e s0 (s0-1) ⋯ (s0-t+1)` times the averaged real count
    is at most `Kq` times the averaged simulation plus `errPowD` at the
    errors `Kq W ε` and each spread `δ0 i (Kq (s0 - 1) + n1 X^L n1^t
    ((0 + ⋯ + (t (L+1) - 1)) F)^e) W`, `W` the number of permutation
    tables (`avg_err_bound`, `loadTR_δs_countP`). -/
theorem sud_interleaveLRN {V Wv P1 P2 P3 W1 W2 W3 : Type} {kr kq : Nat} (φ1 : Nat → Nat → W1 → Nat) (nx1 : Nat → Nat → Nat → List Nat → Nat × Nat × W1) (G1 : Nat → Nat → Nat → List (List (List F)) → Nat → List Nat → P1) (φ2 : Nat → Nat → W2 → Nat) (nx2 : Nat → Nat → Nat → List Nat → Nat × Nat × W2) (G2 : Nat → Nat → Nat → List (List (List F)) → Nat → List Nat → P2) (φ3 : Nat → Nat → W3 → Nat) (nx3 : Nat → Nat → Nat → List Nat → Nat × Nat × W3) (G3 : Nat → Nat → Nat → List (List (List (List F))) × List (List (List F)) → Nat → List Nat → P3)
     (off : EF → String → EF) {puzzle : ∀ ix : Nat, List Nat} (hc : ∀ ix : Nat, CluesOK (cluesOf (puzzle ix))) {ρ : ∀ ix : Nat, Nat → Bool} {A : ∀ ix : Nat, List Cell} {k : ∀ ix : Nat, Nat} {row : ∀ ix : Nat, Nat → Air.Row} (hA : ∀ ix : Nat, AcceptsFrom (A ix) (stmtMachine (ρ ix) 729 (sudokuExpr (cluesOf (puzzle ix))) ACC REJ) (k ix) (row ix)) (hacc : ∀ ix : Nat, rd (A ix) ((row ix) ((k ix) - 1)).ctr ((row ix) ((k ix) - 1)).hd = some (.atom ACC)) (hlen : ∀ ix : Nat, (A ix).length = 2 ^ 16) (hk : ∀ ix : Nat, (k ix) ≤ 2 ^ 16) {tP : ∀ ix : Nat, Nat} (htp : ∀ ix : Nat, (tP ix) = progTp (stmtMachine (fun _ => false) 729 (sudokuExpr (cluesOf (puzzle ix))) ACC REJ).heap) (S16 S10 SP : ∀ ix : Nat, Nat → List F) (qv : ∀ ix : Nat, EF → EF → List EF → F → List F → List F → List EF) (wm wc ww wp : ∀ ix : Nat, Nat → List (EF → EF → List F)) {Lwm Lwc Lww Lwp : ∀ ix : Nat, Nat} (hlwm : ∀ ix : Nat, ∀ c, ((wm ix) c).length = (Lwm ix)) (hlwc : ∀ ix : Nat, ∀ c, ((wc ix) c).length = (Lwc ix)) (hlww : ∀ ix : Nat, ∀ c, ((ww ix) c).length = (Lww ix)) (hlwp : ∀ ix : Nat, ∀ c, ((wp ix) c).length = (Lwp ix)) {K2 K4 : Nat} (hK2 : 0 < K2) (hK4 : 0 < K4) (hS16 : ∀ ix : Nat, ∀ c4, ∀ x ∈ (S16 ix) c4, x ∉ cosetL 1 (bbGen 16) (2 ^ 16)) (hS10 : ∀ ix : Nat, ∀ c4, ∀ x ∈ (S10 ix) c4, x ∉ cosetL 1 (bbGen 10) (2 ^ 10)) (hSP : ∀ ix : Nat, ∀ c4, ∀ x ∈ (SP ix) c4, x ∉ cosetL 1 (bbGen ((tP ix) + 1)) (2 ^ ((tP ix) + 1))) (hsz16 : ∀ ix : Nat, ∀ c4, 2 * ((S16 ix) c4).length + 8 ≤ 2 ^ 16) (hsz : ∀ ix : Nat, ∀ c4, 2 * ((S10 ix) c4).length + 8 ≤ 2 ^ 10) (hszP : ∀ ix : Nat, ∀ c4, 2 * ((SP ix) c4).length + 8 ≤ 2 ^ ((tP ix) + 1)) {ncw : ∀ ix : Nat, Nat} (αd : ∀ ix : Nat, Nat → EF) {B4 : ∀ ix : Nat, Nat} (hB4 : ∀ ix : Nat, sumTo K4 (fun c4 => indB (!genB ((αd ix) c4))) ≤ (B4 ix)) (fri : ∀ ix : Nat, Nat → EF → EF → List (EF → EF) → V) (hncw : ∀ ix : Nat, 4 ≤ (ncw ix)) (NR2 : ∀ ix : Nat, Nat) (Rb : ∀ ix : Nat, Nat → EF → EF → Nat → List (EF → EF)) (Ro : ∀ ix : Nat, Nat → EF → EF → Nat → Wv) {n1 n2 n3 : Nat} {NS1 NS2 NS3 : ∀ ix : Nat, Nat} (Com1 : ∀ ix : Nat, List (List (List F)) → Nat → Nat) (hc1 : ∀ ix : Nat, ComHides (NS1 ix) (Com1 ix)) (hp1 : ∀ ix : Nat, ∀ c4 T1 T2 T3 T4 M, ComPfHides (NS1 ix) (Com1 ix) ((pfRdM (Q4 * Q4) K2 Q4 K4 n1 kr (φ1 ix) (nx1 ix) (G1 ix)) c4 T1 T2 T3 T4 M) (opF ((sudGroups (tP ix) ((S16 ix) c4) ((S10 ix) c4) ((SP ix) c4) EF.zero (qv ix)).map (·.base.S)) [0, 2, 4, 6])) (hr1 : ∀ ix : Nat, ∀ d σ, (Com1 ix) d σ < n1) (d1 : ∀ ix : Nat, List (List (List F))) (Com2 : ∀ ix : Nat, List (List (List F)) → Nat → Nat) (hc2 : ∀ ix : Nat, ComHides (NS2 ix) (Com2 ix)) (hp2 : ∀ ix : Nat, ∀ c4 T1 T2 T3 T4 M, ComPfHides (NS2 ix) (Com2 ix) ((pfRdM (Q4 * Q4) K2 Q4 K4 n1 kr (φ2 ix) (nx2 ix) (G2 ix)) c4 T1 T2 T3 T4 M) (opF ((sudGroups (tP ix) ((S16 ix) c4) ((S10 ix) c4) ((SP ix) c4) EF.zero (qv ix)).map (·.base.S)) [1, 3, 5, 7])) (hr2 : ∀ ix : Nat, ∀ d σ, (Com2 ix) d σ < n2) (d2 : ∀ ix : Nat, List (List (List F))) (Com3 : ∀ ix : Nat, List (List (List (List F))) × List (List (List F)) → Nat → Nat) (hc3 : ∀ ix : Nat, ComHides (NS3 ix) (Com3 ix)) (hp3 : ∀ ix : Nat, ∀ c4 T1 T2 T3 T4 M, ComPfHides (NS3 ix) (Com3 ix) ((pfRdM (Q4 * Q4) K2 Q4 K4 n1 kr (φ3 ix) (nx3 ix) (G3 ix)) c4 T1 T2 T3 T4 M) (fun d => (opQ (sudSsT ((S16 ix) c4) ((S10 ix) c4) ((SP ix) c4)) d.1, opCw (sudSsC (tP ix) ((S16 ix) c4) ((S10 ix) c4) ((SP ix) c4)) d.2))) (hr3 : ∀ ix : Nat, ∀ d σ, (Com3 ix) d σ < n3) (d3 : ∀ ix : Nat, List (List (List (List F))) × List (List (List F)))
    {Kp : Nat} (hKp : 0 < Kp) (inner : Nat → Nat → Nat) (hin : ∀ s x, inner s x < Kp) (κ : Nat → Nat) {Kc : Nat}
    (hκ : ∀ u, κ u < Kc) (hpk2 : ∀ s s' x x', inner s x = inner s' x' → κ s = κ s') (iv : Nat)
    (hd : ∀ a b, a < n1 → b < n1 → a ≠ b → inner iv a ≠ inner iv b)
    (hdxC : ∀ s s' x c c', c < n1 → c' < n1 → inner s x = inner iv c → inner s' x = inner iv c' → c = c')
    {X : Nat} (hX : 0 < X) (L : Nat) (enc : Nat → Option (List (List (List EF)) × List (List (List (List EF))) × List (List (List EF))) → List Nat) (henc : ∀ r w i, i < L → (enc r w).getD i 0 < X)
    (δ0 : Nat → Nat) (hn1 : 0 < n1) {F : Nat} (hF : ∀ v, sumTo Kp (fun u => indB (decide (κ u = v))) ≤ F)
    (hsp1 : ∀ ix d v, sumTo (NS1 ix) (fun σ => indB (decide (Com1 ix d σ = v))) ≤ δ0 ix) {t : Nat} (ht : 0 < t) {s0 : Nat} (hs0 : 2 ≤ s0)
    (isQ : Nat → Bool) (nxtQ : Nat → List Nat → Nat × Nat × Unit) :
    ∀ n (E : Nat × (Nat × Nat × Nat × Nat) → _ → Bool),
      (fact (t - 1 - L) * (Kp - t * (L + 1)) ^ (t - 1 - L) * ffac s0 t) * ((KPowD (fun _ => (K4 * (Q4 * Q4 * (K2 * Q4)))) n) * (fun (f : Nat × (Nat × Nat × Nat × Nat) → Nat) => sumTo (Kp ^ Kp) (fun P => indB (permB Kp P) * (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo (K4 ^ Kp) (fun H4 => sumTo ((Q4 * Q4) ^ n1) (fun H1 => sumTo (K2 ^ (n1 * n2)) (fun H2 => sumTo (Q4 ^ (n1 * (n2 * n3))) (fun H3 => f (H1, H2, H3, H4)))))) (fun H => f (P, H)))) (fun H => (smPowD (X := fun _ => Nat × Nat × Nat × (Nat → Tup)) (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc 0) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).sm 2) n) (fun x => indB (E H ((fun PH x => (rvPowD (mixRv (Q4 * Q4) K2 Q4 K4 kq isQ nxtQ
        (fun i => read4T (Q4 * Q4) K2 Q4 K4 ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc PH.1) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).m1 ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc PH.1) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).m2 ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc PH.1) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).m3 ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc PH.1) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).q ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc PH.1) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).out)) n) PH.2 x) H x))))) ≤
        (fact (t - 1 - L) * (Kp - t * (L + 1)) ^ (t - 1 - L) * ffac s0 t) * (fun (f : Nat × (Nat × Nat × Nat × Nat) → Nat) => sumTo (Kp ^ Kp) (fun P => indB (permB Kp P) * (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo (K4 ^ Kp) (fun H4 => sumTo ((Q4 * Q4) ^ n1) (fun H1 => sumTo (K2 ^ (n1 * n2)) (fun H2 => sumTo (Q4 ^ (n1 * (n2 * n3))) (fun H3 => f (H1, H2, H3, H4)))))) (fun H => f (P, H)))) (fun H => (scPowD (C := fun _ => Nat × Nat × Nat × Nat) (fun _ => (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo K4 (fun c4 => sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo Q4 (fun c3 => f (c1, c2, c3, c4))))))) n) (fun c => (smPowD (X := fun _ => Nat × Nat × Nat × (Nat → Tup)) (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc 0) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).sm 2) n) (fun x => indB (E ((fun PH c x => (PH.1, (pgPowD (pgRd (Q4 * Q4) K2 Q4 K4 (fun i => !isQ i) (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc PH.1) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).pts) (fun _ c => c)) n) PH.2 c x)) H c x) ((fun PH c x => (svPowDT (pgRd (Q4 * Q4) K2 Q4 K4 (fun i => !isQ i) (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc PH.1) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).pts) (fun _ c => c))
        (mixSv (Q4 * Q4) K2 Q4 K4 kq isQ nxtQ (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc PH.1) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).sv)) n) PH.2 c x) H c x))))) +
        errPowD (fun _ => (K4 * (Q4 * Q4 * (K2 * Q4)))) (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc 0) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).sm 2) (fun _ => (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo K4 (fun c4 => sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo Q4 (fun c3 => f (c1, c2, c3, c4))))))) (fun i => (fact (t - 1 - L) * (Kp - t * (L + 1)) ^ (t - 1 - L) * ffac s0 t) * (sumTo (Kp ^ Kp) (fun P => indB (permB Kp P))) * (fun i => cond (isQ i) 0 ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc 0) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).ε) i) (fun i => (fun n x => (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo K4 (fun c4 => sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo Q4 (fun c3 => f (c1, c2, c3, c4)))))) (fun _ => (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo (K4 ^ Kp) (fun H4 => sumTo ((Q4 * Q4) ^ n1) (fun H1 => sumTo (K2 ^ (n1 * n2)) (fun H2 => sumTo (Q4 ^ (n1 * (n2 * n3))) (fun H3 => f (H1, H2, H3, H4)))))) (fun _ => smPowD (X := fun _ => Nat × Nat × Nat × (Nat → Tup)) (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc 0) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).sm 2) n
          (fun _ => rSum (fun i => cond (isQ i) kq (4 + 3 * kr)) n *
            cond (isQ n) 0 (((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc 0) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) n).NS * (((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc 0) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) n).NR * (Q4 ^ 2 * x))))))) i ((fun i => δ0 i * ((fact (t - 1 - L) * (Kp - t * (L + 1)) ^ (t - 1 - L) * ffac s0 t * (s0 - 1) + n1 * (X ^ L * (n1 ^ t * (sumTo (t * (L + 1)) (fun j => j) * F) ^ (t - 1 - L)))) * (sumTo (Kp ^ Kp) (fun P => indB (permB Kp P))))) i)) n := by
  intro n E
  have h := sud_interleaveLR (kq := kq) φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3 off hc hA hacc hlen hk htp S16 S10 SP qv wm wc ww wp hlwm hlwc hlww hlwp hK2 hK4 hS16 hS10 hSP hsz16 hsz hszP αd hB4 fri hncw NR2 Rb Ro Com1 hc1 hp1 hr1 d1 Com2 hc2 hp2 hr2 d2 Com3 hc3 hp3 hr3 d3 hKp inner hin κ hκ hpk2 iv hd hdxC hX L enc henc δ0 hsp1 ht hs0 isQ nxtQ n
  have hb := (avg_err_bound (fun _ => (K4 * (Q4 * Q4 * (K2 * Q4)))) (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc 0) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).sm 2) (fun _ => (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo K4 (fun c4 => sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo Q4 (fun c3 => f (c1, c2, c3, c4))))))) (fun i => cond (isQ i) 0 ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc 0) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).ε) (Kp ^ Kp) (fun P => indB (permB Kp P))
      (fun P i => δsR Kp inner iv n1 X L t s0 δ0 P i) (fun n x => (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo K4 (fun c4 => sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo Q4 (fun c3 => f (c1, c2, c3, c4)))))) (fun _ => (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo (K4 ^ Kp) (fun H4 => sumTo ((Q4 * Q4) ^ n1) (fun H1 => sumTo (K2 ^ (n1 * n2)) (fun H2 => sumTo (Q4 ^ (n1 * (n2 * n3))) (fun H3 => f (H1, H2, H3, H4)))))) (fun _ => smPowD (X := fun _ => Nat × Nat × Nat × (Nat → Tup)) (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc 0) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).sm 2) n
          (fun _ => rSum (fun i => cond (isQ i) kq (4 + 3 * kr)) n *
            cond (isQ n) 0 (((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc 0) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) n).NS * (((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc 0) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) n).NR * (Q4 ^ 2 * x)))))))
      (fun i x => wrap_scale (lin_sum4 _ _ _ _) (lin_sum4 _ _ _ _) (lin_smPowD (fun _ => lin_sm _ _ _ _) i) _ _ _ _ _ x)
      (fact (t - 1 - L) * (Kp - t * (L + 1)) ^ (t - 1 - L) * ffac s0 t) (fun i => δ0 i * ((fact (t - 1 - L) * (Kp - t * (L + 1)) ^ (t - 1 - L) * ffac s0 t * (s0 - 1) + n1 * (X ^ L * (n1 ^ t * (sumTo (t * (L + 1)) (fun j => j) * F) ^ (t - 1 - L)))) * (sumTo (Kp ^ Kp) (fun P => indB (permB Kp P))))) (fun i => loadTR_δs_countP hKp inner hin κ hκ hF hpk2 iv hn1 hd hdxC X L ht s0 (δ0 i)) n)
  exact zkbT_err_le h _ _ hb E

end

end Circuit
