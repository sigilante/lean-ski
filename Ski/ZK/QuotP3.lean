import Ski.ZK.QuotInst

/-!
# Plonky3's chunks, built

`tabsHonest_air` takes the chunk domains, scales and weights as
hypotheses.  This file builds them as Plonky3's `get_quotient_ldes` does
and proves those hypotheses once.
- **Domains:** chunk `i` of `l + 1` is the coset `shift · ωⁱ · ⟨ω^{l+1}⟩`
  (`split_domains`).
- **Scales:** `c_i = s_i⁻ⁿ`, so `c_i ∏ (X - a)` is Plonky3's
  `Z_i = (X / s_i)ⁿ - 1`.
- **Weights:** `cis_i = 1 / ∏_{j ≠ i} v_j(s_i)`, `κ = cis_l` and
  `m_i = cis_i / cis_l` (`get_zp_cis`, `mul_coeffs`).

`p3_static` gives `hdom`, `hc`, `hcl`, `hκ` and `hw` for them.  What is
left for a named circuit is numbers: `shift ≠ 0`, `ω^(2^k) = -1` (for
BabyBear, `bbGen_half`), `0 < n` and `(l + 1) n = 2^(k+1)`.
-/

namespace Circuit

open ZKF

theorem opv_hc (x : F) : ∀ (L L' : List (List F × F × F × List F)) (k : Nat),
    L.map (fun p => (p.1, p.2.1)) = L'.map (fun p => (p.1, p.2.1)) → opv x L k = opv x L' k
  | [], [], _, _ => rfl
  | _ :: L, _ :: L', 0, h => by
    show fval x (rpoly.ppoly L) = fval x (rpoly.ppoly L')
    rw [ppoly_hc L L' (List.cons.inj h).2]
  | (H, c, μ, q) :: L, (H', c', μ', q') :: L', k + 1, h => by
    have e := List.cons.inj h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj e.1
    show c * fval x (fvan H) * opv x L k = c * fval x (fvan H) * opv x L' k
    rw [opv_hc x L L' k e.2]
  | [], _ :: _, _, h => nomatch h
  | _ :: _, [], _, h => nomatch h

theorem finv_ne {x : F} (hx : x ≠ 0) : finv x ≠ 0 := fun e => by
  have := mul_finv hx; rw [e, mul_zero'] at this; exact absurd this (by decide)

section
variable (shift ω : F) (l n : Nat)

/-- Chunk `i`'s domain, first point and scale. -/
def p3dom (i : Nat) : List F := cosetL (shift * fpow ω i) (fpow ω (l + 1)) n
def p3s (i : Nat) : F := shift * fpow ω i
def p3c (i : Nat) : F := finv (fpow (p3s shift ω i) n)

/-- The chunks as `(H, c, μ, q)` with placeholder weights and data:
    `∏_{j ≠ i} v_j` reads only the domains and scales. -/
def p3L0 : List (List F × F × F × List F) :=
  (List.range (l + 1)).map fun i => (p3dom shift ω l n i, p3c shift ω n i, 0, [])

/-- `∏_{j ≠ i} v_j(s_i)`, and Plonky3's `κ = cis_l` and weights. -/
def p3o (i : Nat) : F := opv (p3s shift ω i) (p3L0 shift ω l n) i
def p3κ : F := finv (p3o shift ω l n l)
def p3m (i : Nat) : F := finv (p3o shift ω l n i) * finv (p3κ shift ω l n)

/-- **Plonky3's chunks**: all but the last, with their weights. -/
def p3cs : List Chunk := (List.range l).map fun i => ⟨p3dom shift ω l n i, p3c shift ω n i, p3m shift ω l n i⟩
end

theorem p3L0_length (shift ω : F) (l n : Nat) : (p3L0 shift ω l n).length = l + 1 := by
  unfold p3L0; rw [List.length_map, List.length_range]

theorem p3_doms (shift ω : F) (l n : Nat) :
    (p3cs shift ω l n).map (·.H) ++ [p3dom shift ω l n l] = splitD shift ω (l + 1) n := by
  unfold p3cs splitD
  rw [List.map_map, List.range_succ, List.map_append]
  rfl

/-- **`allL` of Plonky3's chunks, entry by entry.** -/
theorem p3_allL (shift ω : F) (l n : Nat) (qs : List (List F)) (ql : List F) (hq : qs.length = l) :
    (allL (p3cs shift ω l n) (p3dom shift ω l n l) (p3c shift ω n l) qs ql).length = l + 1 ∧
    ∀ j (hj : j < l + 1) (hj' : j < (allL (p3cs shift ω l n) (p3dom shift ω l n l) (p3c shift ω n l) qs ql).length),
      ((allL (p3cs shift ω l n) (p3dom shift ω l n l) (p3c shift ω n l) qs ql)[j]'hj').1 = p3dom shift ω l n j ∧
      ((allL (p3cs shift ω l n) (p3dom shift ω l n l) (p3c shift ω n l) qs ql)[j]'hj').2.1 = p3c shift ω n j ∧
      ((allL (p3cs shift ω l n) (p3dom shift ω l n l) (p3c shift ω n l) qs ql)[j]'hj').2.2.1 =
        if j < l then p3m shift ω l n j else 1 := by
  have hcs : (p3cs shift ω l n).length = l := by unfold p3cs; rw [List.length_map, List.length_range]
  have hz : (List.zipWith (fun (ch : Chunk) q => (ch.H, ch.c, ch.m, q)) (p3cs shift ω l n) qs).length = l := by
    rw [List.length_zipWith, hcs, hq, Nat.min_self]
  refine ⟨by unfold allL; rw [List.length_append, hz]; rfl, fun j hj hj' => ?_⟩
  unfold allL
  by_cases hjl : j < l
  · rw [List.getElem_append_left (by rw [hz]; exact hjl), List.getElem_zipWith, if_pos hjl]
    unfold p3cs
    simp only [List.getElem_map, List.getElem_range]
    refine ⟨?_, ?_, ?_⟩ <;> first | trivial | rfl
  · have hjl' : j = l := by omega
    subst hjl'
    rw [List.getElem_append_right (by rw [hz]; exact Nat.le_refl _), if_neg hjl]
    simp only [hz, Nat.sub_self, List.getElem_singleton]
    refine ⟨?_, ?_, ?_⟩ <;> first | trivial | rfl

theorem p3_allL_hc (shift ω : F) (l n : Nat) (qs : List (List F)) (ql : List F) (hq : qs.length = l) :
    (allL (p3cs shift ω l n) (p3dom shift ω l n l) (p3c shift ω n l) qs ql).map (fun p => (p.1, p.2.1)) =
      (p3L0 shift ω l n).map (fun p => (p.1, p.2.1)) := by
  obtain ⟨hlen, hent⟩ := p3_allL shift ω l n qs ql hq
  refine List.ext_getElem (by rw [List.length_map, List.length_map, hlen, p3L0_length]) (fun j h1 h2 => ?_)
  rw [List.length_map] at h1
  rw [List.getElem_map, List.getElem_map]
  obtain ⟨e1, e2, _⟩ := hent j (by rw [hlen] at h1; exact h1) h1
  rw [e1, e2]
  unfold p3L0
  simp only [List.getElem_map, List.getElem_range]

/-- **Plonky3's chunks meet `tabsHonest_air`'s static hypotheses on the
    chunks**: the split domains, nonzero scales, `κ ≠ 0`, and the weights
    `cis_k / κ` at every first point. -/
theorem p3_static {shift ω : F} {l n k : Nat} (hs : shift ≠ 0) (hhalf : fpow ω (2 ^ k) = -1)
    (hN : (l + 1) * n = 2 ^ (k + 1)) (hn : 0 < n) :
    (p3cs shift ω l n).map (·.H) ++ [p3dom shift ω l n l] = splitD shift ω ((p3cs shift ω l n).length + 1) n ∧
    (∀ ch ∈ p3cs shift ω l n, ch.c ≠ 0) ∧ p3c shift ω n l ≠ 0 ∧ p3κ shift ω l n ≠ 0 ∧
    (∀ (qs : List (List F)) (ql : List F), qs.length = (p3cs shift ω l n).length →
      ∀ j (hj : j < (allL (p3cs shift ω l n) (p3dom shift ω l n l) (p3c shift ω n l) qs ql).length) s',
      ((allL (p3cs shift ω l n) (p3dom shift ω l n l) (p3c shift ω n l) qs ql)[j]'hj).1 =
        cosetL s' (fpow ω ((p3cs shift ω l n).length + 1)) n →
      ((allL (p3cs shift ω l n) (p3dom shift ω l n l) (p3c shift ω n l) qs ql)[j]'hj).2.2.1 =
        finv (opv s' (allL (p3cs shift ω l n) (p3dom shift ω l n l) (p3c shift ω n l) qs ql) j) *
          finv (p3κ shift ω l n)) ∧
    (∀ ch ∈ p3cs shift ω l n, ch.m ≠ 0) := by
  have hcs : (p3cs shift ω l n).length = l := by unfold p3cs; rw [List.length_map, List.length_range]
  have hsc : ∀ i, p3c shift ω n i ≠ 0 := fun i =>
    finv_ne (fpow_ne_zero' (mul_ne_zero' hs (fpow_ne_zero' (fun e => by
      rw [e, show 2 ^ k = (2 ^ k - 1) + 1 by have := Nat.one_le_two_pow (n := k); omega] at hhalf
      exact absurd (by rw [← hhalf]; show (0 : F) = fpow 0 (2 ^ k - 1) * 0; rw [mul_zero'])
        (by decide : (0 : F) ≠ -1)) i)) n)
  -- the placeholder list's domains are the split, so disjoint
  have hd0 : (p3L0 shift ω l n).map (·.1) = splitD shift ω (l + 1) n := by
    unfold p3L0 splitD; rw [List.map_map]; rfl
  have hnd0 := split_nodup hs hhalf hN
  rw [← hd0] at hnd0
  have hdis0 := (dis_of_nodup _ hnd0).2
  have hc0 : ∀ p ∈ p3L0 shift ω l n, p.2.1 ≠ 0 := fun p hp => by
    obtain ⟨i, _, rfl⟩ := List.mem_map.1 hp; exact hsc i
  have hget0 : ∀ i (hi : i < (p3L0 shift ω l n).length), (p3L0 shift ω l n)[i] = (p3dom shift ω l n i, p3c shift ω n i, 0, []) :=
    fun i hi => by unfold p3L0; simp only [List.getElem_map, List.getElem_range]
  have hfirst : ∀ i, i < l + 1 → p3s shift ω i ∈ p3dom shift ω l n i := fun i _ => by
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    exact List.mem_cons_self
  have ho : ∀ i, i < l + 1 → p3o shift ω l n i ≠ 0 := fun i hi =>
    opv_ne _ i (by rw [p3L0_length]; exact hi) hc0 (fun j hj hji => by
      have := hdis0 i j (by rw [p3L0_length]; exact hi) hj hji (p3s shift ω i) (by rw [hget0]; exact hfirst i hi)
      exact this)
  have hκ : p3κ shift ω l n ≠ 0 := finv_ne (ho l (Nat.lt_succ_self l))
  refine ⟨by rw [hcs]; exact p3_doms shift ω l n, fun ch hch => ?_, hsc l, hκ, fun qs ql hq j hj s' hs' => ?_,
    fun ch hch => ?_⟩
  · obtain ⟨i, _, rfl⟩ := List.mem_map.1 hch; exact hsc i
  · rw [hcs] at hq hs'
    obtain ⟨hlen, hent⟩ := p3_allL shift ω l n qs ql hq
    have hj1 : j < l + 1 := by rw [hlen] at hj; exact hj
    obtain ⟨e1, _, e3⟩ := hent j hj1 hj
    -- the first point is `s_j`
    have hsj : s' = p3s shift ω j := by
      rw [e1] at hs'
      obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
      exact (List.cons.inj hs').1.symm
    rw [e3, hsj, opv_hc _ _ (p3L0 shift ω l n) j (p3_allL_hc shift ω l n qs ql hq)]
    by_cases hjl : j < l
    · rw [if_pos hjl]; rfl
    · have hjl' : j = l := by omega
      rw [if_neg hjl]
      -- `1 = cis_l / cis_l`
      have h2 : finv (p3o shift ω l n j) * finv (p3κ shift ω l n) = 1 := by
        rw [hjl']; exact mul_finv hκ
      exact h2.symm
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hch
    exact mul_ne_zero' (finv_ne (ho i (by have := List.mem_range.1 hi; omega))) (finv_ne hκ)

-- ---------------------------------------------------------------------------
-- BabyBear's trace domain and masks
-- ---------------------------------------------------------------------------

/-- **BabyBear's trace domain of `2^(t+1)` rows**: `g = bbGen (t+1)` has
    `g^(2^(t+1)) = 1` and distinct powers below it. -/
theorem bb_trace (t : Nat) (ht : t ≤ 26) :
    fpow (bbGen (t + 1)) (2 ^ (t + 1)) = 1 ∧
    ∀ a b, a < 2 ^ (t + 1) → b < 2 ^ (t + 1) → fpow (bbGen (t + 1)) a = fpow (bbGen (t + 1)) b → a = b := by
  have half := bbGen_half t ht
  refine ⟨?_, fun a b ha hb e => fpow_inj half ha hb e⟩
  rw [Nat.pow_succ, fpow_mul', half]; exact neg_one_sq

theorem fpow_sq (x : F) (r : Nat) : fpow (x * x) r = fpow x (2 * r) := by
  rw [fpow_mul_distrib, ← fpow_add', Nat.two_mul]

/-- **The ZK masks lie off the trace**: the trace points `gʳ` and the mask
    points `g' gʳ`, with `g'² = g` (`HidingFriPcs` interleaves random rows
    on the domain of twice the size), are all distinct. -/
theorem bb_masks (t : Nat) (ht : t ≤ 25) :
    (cosetL 1 (bbGen (t + 1)) (2 ^ (t + 1)) ++ cosetL (bbGen (t + 2)) (bbGen (t + 1)) (2 ^ (t + 1))).Nodup := by
  have hsq : bbGen (t + 2) * bbGen (t + 2) = bbGen (t + 1) :=
    of_decide_eq_true (List.all_eq_true.1 bbGen_chain.1 t (List.mem_range.2 (by omega)))
  have half := bbGen_half (t + 1) (by omega)
  have inj : ∀ a b, a < 2 ^ (t + 2) → b < 2 ^ (t + 2) → fpow (bbGen (t + 2)) a = fpow (bbGen (t + 2)) b → a = b :=
    fun a b ha hb e => fpow_inj half ha hb e
  have hT : ∀ x ∈ cosetL 1 (bbGen (t + 1)) (2 ^ (t + 1)), ∃ r, r < 2 ^ (t + 1) ∧ x = fpow (bbGen (t + 2)) (2 * r) :=
    fun x hx => by
      obtain ⟨r, hr, rfl⟩ := mem_coset hx
      exact ⟨r, hr, by rw [one_mul', ← hsq, fpow_sq]⟩
  have hR : ∀ x ∈ cosetL (bbGen (t + 2)) (bbGen (t + 1)) (2 ^ (t + 1)), ∃ r, r < 2 ^ (t + 1) ∧
      x = fpow (bbGen (t + 2)) (2 * r + 1) := fun x hx => by
    obtain ⟨r, hr, rfl⟩ := mem_coset hx
    exact ⟨r, hr, by rw [← hsq, fpow_sq, mul_comm']; rfl⟩
  have h2 : 2 ^ (t + 2) = 2 * 2 ^ (t + 1) := by rw [Nat.pow_succ, Nat.mul_comm]
  refine List.nodup_append.2 ⟨?_, ?_, fun a ha b hb e => ?_⟩
  · refine coset_nodup _ _ 1 (fun r r' hr hr' e => ?_)
    rw [one_mul', one_mul', ← hsq, fpow_sq, fpow_sq] at e
    have := inj _ _ (by omega) (by omega) e; omega
  · refine coset_nodup _ _ _ (fun r r' hr hr' e => ?_)
    rw [← hsq, fpow_sq, fpow_sq, mul_comm', mul_comm' _ (fpow _ (2 * r'))] at e
    have := inj (2 * r + 1) (2 * r' + 1) (by omega) (by omega) e; omega
  · obtain ⟨r, hr, rfl⟩ := hT a ha
    obtain ⟨r', hr', rfl⟩ := hR b hb
    have := inj _ _ (by omega) (by omega) e; omega

/-- **The table's sets meet `CSet.OK`** from its parts. -/
theorem airQTab_ok {A : AirD} {g : F} {m : Nat} {preP : Nat → List F} {gi : Nat} {κ : F} {cs : List Chunk}
    {Hl : List F} {cl : F} {S : List F} {ζ : EF} {ws : List (EF → EF → List F)} (hζ : ∀ x : F, EF.ofF x ≠ ζ)
    (hdet : (mz ζ).det ≠ 0) (hS4 : S.length + 4 ≤ m + 1) (hcm : ∀ ch ∈ cs, ch.c ≠ 0 ∧ ch.m ≠ 0) (hcl : cl ≠ 0) :
    ∀ c ∈ (airQTab A g m preP gi κ cs Hl cl S ζ ws).sets, c.OK := fun c hc => by
  unfold QTab.sets airQTab at hc
  obtain ⟨_, _, rfl⟩ := List.mem_map.1 hc
  exact ⟨hζ, hdet, hS4, hcm, hcl⟩

theorem split_member_nodup {shift ω : F} {L n k : Nat} (hs : shift ≠ 0) (hhalf : fpow ω (2 ^ k) = -1)
    (hN : L * n = 2 ^ (k + 1)) {H : List F} (hH : H ∈ splitD shift ω L n) : H.Nodup :=
  (List.pairwise_flatten.1 (split_nodup hs hhalf hN)).1 H hH

/-- **The composed hiding PCS over BabyBear with Plonky3's chunks**:
    `pcsCloseN_fri_air` with the trace domain `⟨bbGen (tb+1)⟩` of
    `2^(tb+1)` rows, the masks on the interleaved coset, and Plonky3's
    chunks of the quotient domain `31 · ⟨bbGen (k+1)⟩`, every hypothesis
    on the chunks' domains, scales and weights discharged.  Left: the
    group's trace and mask points and next row (`hT`, `hRq`, `hZq`,
    `hnxt`), the AIR's `Sat` at each trace with its constraints in the
    window, guarded, and of degree `D ≤ 2^lq` (`hsatT`, `hgd`, `hD`,
    `hsd`), the preprocessed columns' length (`hpreL`), the field-size
    bound (`hPsz`), the query points (off the trace, `|S| + 4 ≤ m + 1`)
    and the out-of-domain point (`ζ` generating the extension). -/
theorem pcsCloseN_fri_bb {V : Type} {qs : List QGroup} {ks : List Nat} {cols : (Nat → Tup) → EF → EF → List (List (List F))}
    {ncw : Nat} {αb : EF} {fri : EF → EF → List (EF → EF) → V}
    (hokq : ∀ q ∈ qs, q.OK) (hks : ks.length = qs.length)
    (hcols : ∀ t α β, Shaped (qs.map QGroup.ext) (cols t α β) ∧ (cols t α β).map List.length = ks)
    (hdet : (mz αb).det ≠ 0) (haw : ∀ w, apow αb w ≠ EF.zero) (hncw : 4 ≤ ncw)
    (off : EF → String → EF) (tv : (String → EF) → EF → (Nat → Tup) → List EF)
    {A : AirD} {preP : Nat → List F} {gi : Nat} {S : List F} {ζ : EF} {ws : List (EF → EF → List F)} {nR : Nat}
    {tb l k lq D s m : Nat} (ht : tb ≤ 25) (hm : m + 1 = 2 ^ (tb + 1)) (hk : k ≤ 26)
    (hN : (l + 1) * (m + 1) = 2 ^ (k + 1)) (hL : l + 1 = 2 ^ (lq + 1))
    (hgi : gi < qs.length) (hcl' : ∀ t α β, gi < (cols t α β).length)
    (hT : (qs[gi]'hgi).base.T = cosetL 1 (bbGen (tb + 1)) (m + 1))
    (hRq : (qs[gi]'hgi).base.R = cosetL (bbGen (tb + 2)) (bbGen (tb + 1)) (m + 1)) (hSq : (qs[gi]'hgi).base.S = S)
    (hZq : (qs[gi]'hgi).base.Z = [ζ, (EF.ofF (bbGen (tb + 1))).mul ζ]) (hnq : (qs[gi]'hgi).base.n = nR)
    (hnxt : (qs[gi]'hgi).nxt = (bbGen (tb + 1) * ·))
    (hsatT : ∀ t' α β, ∃ Tb : Table, Sat A Tb ∧ Tb.h = m + 1 ∧
      (∀ c ∈ A.cons, c.win ((cols t' α β)[gi]'(hcl' t' α β)).length = true) ∧
      (∀ i (hi : i < ((cols t' α β)[gi]'(hcl' t' α β)).length),
        (((cols t' α β)[gi]'(hcl' t' α β))[i]).length = m + 1 ∧
        ∀ r (hr : r < (((cols t' α β)[gi]'(hcl' t' α β))[i]).length),
          (((cols t' α β)[gi]'(hcl' t' α β))[i])[r] = Tb.main r i) ∧
      (∀ r i, r < m + 1 → fval (fpow (bbGen (tb + 1)) r) (preP i) = Tb.pre r i))
    (hgd : ∀ c ∈ A.cons, c.guarded = true) (hpreL : ∀ i, (preP i).length ≤ 2 * (m + 1))
    (hζ : ∀ x : F, EF.ofF x ≠ ζ) (hS : ∀ x ∈ S, fval x (fvan (cosetL 1 (bbGen (tb + 1)) (m + 1))) ≠ 0)
    (hD : ∀ e ∈ A.cons, e.pdeg ≤ D) (hDlq : D ≤ 2 ^ lq)
    (hsd : ∀ e ∈ A.cons, e.sdeg ≤ s) (hs : s < m + 1) (hPsz : D * (2 * (m + 1) - 1) + s + 1 ≤ P)
    (hdetζ : (mz ζ).det ≠ 0) (hS4 : S.length + 4 ≤ m + 1) :
    PCSCloseN off (P ^ (friN1 qs ks [airQTab A (bbGen (tb + 1)) m preP gi (p3κ 31 (bbGen (k + 1)) l (m + 1))
        (p3cs 31 (bbGen (k + 1)) l (m + 1)) (p3dom 31 (bbGen (k + 1)) l (m + 1) l) (p3c 31 (bbGen (k + 1)) (m + 1) l)
        S ζ ws] +
      friN2 qs [airQTab A (bbGen (tb + 1)) m preP gi (p3κ 31 (bbGen (k + 1)) l (m + 1))
        (p3cs 31 (bbGen (k + 1)) l (m + 1)) (p3dom 31 (bbGen (k + 1)) l (m + 1) l) (p3c 31 (bbGen (k + 1)) (m + 1) l)
        S ζ ws] ncw)) tv
      (pcsFri off tv qs ks cols [airQTab A (bbGen (tb + 1)) m preP gi (p3κ 31 (bbGen (k + 1)) l (m + 1))
        (p3cs 31 (bbGen (k + 1)) l (m + 1)) (p3dom 31 (bbGen (k + 1)) l (m + 1) l) (p3c 31 (bbGen (k + 1)) (m + 1) l)
        S ζ ws]
        (fun t α β ms => [airData A (bbGen (tb + 1)) m preP (p3cs 31 (bbGen (k + 1)) l (m + 1))
          (p3dom 31 (bbGen (k + 1)) l (m + 1) l) ws α β ((mpolysMulti (qs.map QGroup.ext) (cols t α β) ms).getD gi [])])
        ncw αb fri)
      (psimFri qs ks [airQTab A (bbGen (tb + 1)) m preP gi (p3κ 31 (bbGen (k + 1)) l (m + 1))
        (p3cs 31 (bbGen (k + 1)) l (m + 1)) (p3dom 31 (bbGen (k + 1)) l (m + 1) l) (p3c 31 (bbGen (k + 1)) (m + 1) l)
        S ζ ws] ncw αb fri) 0 := by
  have h31 : (31 : F) ≠ 0 := by decide
  have hhalf := bbGen_half k hk
  obtain ⟨hdom, hc, hcl, hκ, hw, hm0⟩ := p3_static h31 hhalf hN (by omega)
  obtain ⟨hg, hinj⟩ := bb_trace tb (by omega)
  have hcs : (p3cs 31 (bbGen (k + 1)) l (m + 1)).length = l := by unfold p3cs; rw [List.length_map, List.length_range]
  have hnd := bb_masks tb ht
  rw [← hm] at hg hinj hnd
  have hNodup : ∀ H ∈ splitD 31 (bbGen (k + 1)) (l + 1) (m + 1), H.Nodup := fun H hH => split_member_nodup h31 hhalf hN hH
  rw [hcs] at hdom
  refine pcsCloseN_fri_air hokq hks hcols hdet haw hncw off tv (A := A) (preP := preP) (gi := gi) (ws := ws)
    (R := cosetL (bbGen (tb + 2)) (bbGen (tb + 1)) (m + 1)) (nR := nR) (g := bbGen (tb + 1)) (m := m)
    hgi hcl' hT hRq hSq hZq hnq hnxt hsatT hg hinj hgd (by rw [cosetL_length]; exact Nat.le_refl _) hnd hpreL hζ hS hc hcl hκ h31 hhalf
    (by rw [hcs]; exact hN) (by rw [hcs]; exact hdom) (by rw [hcs]; exact hL) hD hDlq hsd hs hPsz
    (fun qs' ql h => hw qs' ql h) (airQTab_ok hζ hdetζ hS4 (fun ch hch => ⟨hc ch hch, hm0 ch hch⟩) hcl)
    (fun ch hch => hNodup _ (by rw [← hdom]; exact List.mem_append_left _ (List.mem_map_of_mem hch)))
    (hNodup _ (by rw [← hdom]; exact List.mem_append_right _ List.mem_cons_self))

end Circuit
