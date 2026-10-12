import Ski.ZK.MaskCoset

/-!
# Plonky3's split domains

Plonky3 splits the quotient domain `shift · ⟨ω⟩` of size `L n` into
`L` chunk domains (`split_domains`): chunk `i` is the coset
`shift · ωⁱ · ⟨ω^L⟩`, of size `n`.  `quotOK_honest` asks that these be
cosets of one subgroup `⟨g⟩` with `gⁿ = 1` and no repeated points.  This
file proves both from one fact about `ω`: `ω^(2^(k-1)) = -1` when
`L n = 2^k`, which is what makes `ω` a primitive `2^k`-th root of unity.

`fpow_inj` derives that `e ↦ ωᵉ` is injective on `[0, 2^k)`.  The
difference of two exponents is `2^j (2o + 1)` with `j < k`, and raising
`ω^(2^j (2o+1)) = 1` to `2^(k-1-j)` would give `-1 = 1`.  `split_nodup`
then shows the chunk domains have no repeated points, and `split_pow`
shows `(ω^L)ⁿ = 1`.
-/

namespace Circuit

open ZKF

theorem fpow_add' (x : F) (a : Nat) : ∀ b, fpow x (a + b) = fpow x a * fpow x b
  | 0 => by show fpow x a = fpow x a * 1; rw [mul_one']
  | b + 1 => by
    show fpow x (a + b) * x = fpow x a * (fpow x b * x)
    rw [fpow_add' x a b, mul_assoc']

theorem fpow_mul' (x : F) (a : Nat) : ∀ b, fpow x (a * b) = fpow (fpow x a) b
  | 0 => rfl
  | b + 1 => by
    show fpow x (a * b + a) = fpow (fpow x a) b * fpow x a
    rw [fpow_add', fpow_mul' x a b]

theorem fpow_one' : ∀ n, fpow (1 : F) n = 1
  | 0 => rfl
  | n + 1 => by show fpow 1 n * 1 = 1; rw [fpow_one' n, mul_one']

theorem fpow_ne_zero' {x : F} (hx : x ≠ 0) : ∀ n, fpow x n ≠ 0
  | 0 => by show (1 : F) ≠ 0; decide
  | n + 1 => mul_ne_zero' (fpow_ne_zero' hx n) hx

theorem neg_one_sq : (-1 : F) * -1 = 1 := by decide

theorem fpow_neg_one_odd : ∀ o, fpow (-1 : F) (2 * o + 1) = -1
  | 0 => by decide
  | o + 1 => by
    rw [show 2 * (o + 1) + 1 = (2 * o + 1) + 1 + 1 by omega]
    show fpow (-1 : F) (2 * o + 1) * -1 * -1 = -1
    rw [fpow_neg_one_odd o, neg_one_sq, one_mul']

/-- Every positive number is `2^j` times an odd number. -/
theorem two_adic_split : ∀ d, 0 < d → ∃ j o, d = 2 ^ j * (2 * o + 1)
  | d, hd => by
    rcases Nat.mod_two_eq_zero_or_one d with h | h
    · have hm : 0 < d / 2 := by omega
      obtain ⟨j, o, e⟩ := two_adic_split (d / 2) hm
      exact ⟨j + 1, o, by rw [Nat.pow_succ, Nat.mul_comm (2 ^ j) 2, Nat.mul_assoc, ← e]; omega⟩
    · exact ⟨0, d / 2, by rw [Nat.pow_zero, Nat.one_mul]; omega⟩
termination_by d => d
decreasing_by omega

/-- **No power of `ω` below `2^k` is one**, except `ω⁰`. -/
theorem fpow_ne_one {ω : F} {k : Nat} (hhalf : fpow ω (2 ^ k) = -1) : ∀ d, 0 < d → d < 2 ^ (k + 1) → fpow ω d ≠ 1 := by
  intro d hd hlt h
  obtain ⟨j, o, rfl⟩ := two_adic_split d hd
  have hj : j ≤ k := Nat.le_of_not_lt fun h => absurd hlt (Nat.not_lt_of_le
    (Nat.le_trans (Nat.pow_le_pow_right (by decide) h) (Nat.le_mul_of_pos_right _ (by omega))))
  have e1 : fpow ω (2 ^ k * (2 * o + 1)) = 1 := by
    rw [show 2 ^ k = 2 ^ j * 2 ^ (k - j) by rw [← Nat.pow_add]; congr 1; omega,
      Nat.mul_assoc, Nat.mul_comm (2 ^ (k - j)), ← Nat.mul_assoc, fpow_mul', h, fpow_one']
  rw [fpow_mul', hhalf, fpow_neg_one_odd] at e1
  exact absurd e1 (by decide)

/-- **`e ↦ ωᵉ` is injective on `[0, 2^(k+1))`** when `ω^(2^k) = -1`. -/
theorem fpow_inj {ω : F} {k : Nat} (hhalf : fpow ω (2 ^ k) = -1) {a b : Nat} (ha : a < 2 ^ (k + 1))
    (hb : b < 2 ^ (k + 1)) (h : fpow ω a = fpow ω b) : a = b := by
  have hω : ω ≠ 0 := fun e => by
    rw [e, show 2 ^ k = (2 ^ k - 1) + 1 by have := Nat.one_le_two_pow (n := k); omega] at hhalf
    exact absurd (by rw [← hhalf]; show (0 : F) = fpow 0 (2 ^ k - 1) * 0; rw [mul_zero'])
      (by decide : (0 : F) ≠ -1)
  have key : ∀ a b, a < b → b < 2 ^ (k + 1) → fpow ω a ≠ fpow ω b := fun a b hab hb e => by
    rw [show b = a + (b - a) by omega, fpow_add'] at e
    have : fpow ω a * (fpow ω (b - a) - 1) = 0 := by
      rw [show fpow ω a * (fpow ω (b - a) - 1) = fpow ω a * fpow ω (b - a) - fpow ω a from
        fid (e := v 0 * (v 1 - .const 1)) (e' := v 0 * v 1 - v 0) (by decide) [fpow ω a, fpow ω (b - a)], ← e, sub_self']
    rcases mul_eq_zero this with e | e
    · exact fpow_ne_zero' hω a e
    · exact fpow_ne_one hhalf (b - a) (by omega) (by omega) (sub_eq_zero e)
  rcases Nat.lt_trichotomy a b with hab | hab | hab
  · exact absurd h (key a b hab hb)
  · exact hab
  · exact absurd h.symm (key b a hab ha)

theorem cosetL_length (s g : F) : ∀ n, (cosetL s g n).length = n
  | 0 => rfl
  | n + 1 => by show (cosetL (s * g) g n).length + 1 = n + 1; rw [cosetL_length]

theorem mem_coset_iff {x s g : F} : ∀ {n}, x ∈ cosetL s g n ↔ ∃ t, t < n ∧ x = s * fpow g t
  | 0 => ⟨fun h => (nomatch h), fun ⟨_, ht, _⟩ => absurd ht (Nat.not_lt_zero _)⟩
  | n + 1 => ⟨mem_coset, fun ⟨t, ht, e⟩ => by
    cases t with
    | zero => rw [e]; exact List.mem_cons.2 (.inl (mul_one' s))
    | succ t =>
      refine List.mem_cons_of_mem _ (mem_coset_iff.2 ⟨t, Nat.lt_of_succ_lt_succ ht, ?_⟩)
      rw [e, mul_assoc', fpow_succ']⟩

/-- A coset whose points `s gᵗ` are distinct has no repeats. -/
theorem coset_nodup (g : F) : ∀ (n : Nat) (s : F), (∀ t t', t < n → t' < n → s * fpow g t = s * fpow g t' → t = t') →
    (cosetL s g n).Nodup
  | 0, _, _ => List.nodup_nil
  | n + 1, s, h => by
    refine List.nodup_cons.2 ⟨fun hm => ?_, coset_nodup g n (s * g) (fun t t' ht ht' e => ?_)⟩
    · obtain ⟨t, ht, e⟩ := mem_coset hm
      rw [mul_assoc', fpow_succ'] at e
      have := h 0 (t + 1) (Nat.succ_pos n) (Nat.succ_lt_succ ht) (by rw [← e]; exact mul_one' s)
      exact Nat.succ_ne_zero t this.symm
    · rw [mul_assoc', mul_assoc', fpow_succ', fpow_succ'] at e
      exact Nat.succ.inj (h (t + 1) (t' + 1) (Nat.succ_lt_succ ht) (Nat.succ_lt_succ ht') e)

/-- **Plonky3's split domains**: chunk `i` is `shift · ωⁱ · ⟨ω^L⟩`. -/
def splitD (shift ω : F) (L n : Nat) : List (List F) :=
  (List.range L).map fun i => cosetL (shift * fpow ω i) (fpow ω L) n

theorem mem_split {shift ω x : F} {L n : Nat} {H : List F} (hH : H ∈ splitD shift ω L n) (hx : x ∈ H) :
    ∃ i t, i < L ∧ t < n ∧ H = cosetL (shift * fpow ω i) (fpow ω L) n ∧ x = shift * fpow ω (i + L * t) := by
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hH
  obtain ⟨t, ht, rfl⟩ := mem_coset hx
  exact ⟨i, t, List.mem_range.1 hi, ht, rfl, by rw [fpow_add', fpow_mul', mul_assoc']⟩

theorem split_exp_lt {L n i t : Nat} (hi : i < L) (ht : t < n) : i + L * t < L * n := by
  have : L * t + L ≤ L * n := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left L ht
  omega

/-- **The split domains have no repeated points** when `ω^(2^k) = -1`,
    `L n = 2^(k+1)` and `shift ≠ 0`. -/
theorem split_nodup {shift ω : F} {L n k : Nat} (hs : shift ≠ 0) (hhalf : fpow ω (2 ^ k) = -1)
    (hN : L * n = 2 ^ (k + 1)) : (splitD shift ω L n).flatten.Nodup := by
  have inj : ∀ i t i' t', i < L → t < n → i' < L → t' < n →
      shift * fpow ω (i + L * t) = shift * fpow ω (i' + L * t') → i = i' ∧ t = t' := by
    intro i t i' t' hi ht hi' ht' e
    have e' : fpow ω (i + L * t) = fpow ω (i' + L * t') := by
      have := congrArg (fun y => finv shift * y) e
      rwa [← mul_assoc', ← mul_assoc', finv_mul hs, one_mul', one_mul'] at this
    have := fpow_inj hhalf (by rw [← hN]; exact split_exp_lt hi ht) (by rw [← hN]; exact split_exp_lt hi' ht') e'
    have hm := congrArg (· % L) this
    simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hi'] at hm
    subst hm
    have hL : 0 < L := Nat.lt_of_le_of_lt (Nat.zero_le _) hi
    exact ⟨rfl, Nat.eq_of_mul_eq_mul_left hL (Nat.add_left_cancel this)⟩
  refine List.pairwise_flatten.2 ⟨fun H hH => ?_, ?_⟩
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hH
    refine coset_nodup _ n _ (fun t t' ht ht' e => ?_)
    rw [← fpow_mul', ← fpow_mul', mul_assoc', mul_assoc', ← fpow_add', ← fpow_add'] at e
    exact (inj i t i t' (List.mem_range.1 hi) ht (List.mem_range.1 hi) ht' e).2
  · refine List.pairwise_map.2 (List.pairwise_iff_getElem.2 fun a b ha hb hab x hx y hy hxy => ?_)
    rw [List.getElem_range] at hx hy
    have ha' : a < L := by rw [List.length_range] at ha; exact ha
    have hb' : b < L := by rw [List.length_range] at hb; exact hb
    obtain ⟨t, ht, rfl⟩ := mem_coset hx
    obtain ⟨t', ht', rfl⟩ := mem_coset hy
    rw [← fpow_mul', ← fpow_mul', mul_assoc', mul_assoc', ← fpow_add', ← fpow_add'] at hxy
    exact absurd (inj a t b t' ha' ht hb' ht' hxy).1 (Nat.ne_of_lt hab)

/-- **The chunk domains are cosets of one subgroup of order dividing
    `n`**: `(ω^L)ⁿ = 1` when `L n = 2^(k+1)` and `ω^(2^k) = -1`. -/
theorem split_pow {ω : F} {L n k : Nat} (hhalf : fpow ω (2 ^ k) = -1) (hN : L * n = 2 ^ (k + 1)) :
    fpow (fpow ω L) n = 1 := by
  rw [← fpow_mul', hN, Nat.pow_succ, fpow_mul', hhalf]; exact neg_one_sq

theorem split_coset {shift ω : F} {L n : Nat} {H : List F} (hH : H ∈ splitD shift ω L n) :
    ∃ s, H = cosetL s (fpow ω L) n := by
  obtain ⟨i, _, rfl⟩ := List.mem_map.1 hH
  exact ⟨_, rfl⟩

theorem split_length {shift ω : F} {L n : Nat} {H : List F} (hH : H ∈ splitD shift ω L n) : H.length = n := by
  obtain ⟨i, _, rfl⟩ := List.mem_map.1 hH
  exact cosetL_length _ _ n

theorem allL_doms (Hl : List F) (cl : F) (ql : List F) (Qp : List F) : ∀ cs : List Chunk,
    (allL cs Hl cl (cs.map fun ch => chunkOf ch.H Qp) ql).map (·.1) = cs.map (·.H) ++ [Hl]
  | [] => rfl
  | ch :: cs => by
    have := allL_doms Hl cl ql Qp cs
    unfold allL at this ⊢
    rw [List.map_cons, List.zipWith_cons_cons, List.cons_append, List.map_cons, this]; rfl

/-- **Honest chunks on Plonky3's split domains meet `QuotOK`**: what is
    left is the quotient's degree and the selectors at each first point. -/
theorem quotOK_split {cs : List Chunk} {Hl : List F} {cl κ : F} {Qp : List F} (hκ : κ ≠ 0) {shift ω : F} {L n k : Nat}
    (hs : shift ≠ 0) (hhalf : fpow ω (2 ^ k) = -1) (hN : L * n = 2 ^ (k + 1))
    (hdom : cs.map (·.H) ++ [Hl] = splitD shift ω L n) (hQ : Qp.length ≤ L * n)
    (hfirst : ∀ j (hj : j < (allL cs Hl cl (cs.map fun ch => chunkOf ch.H Qp) (chunkOf Hl Qp)).length), ∀ s,
      ((allL cs Hl cl (cs.map fun ch => chunkOf ch.H Qp) (chunkOf Hl Qp))[j]'hj).1 = cosetL s (fpow ω L) n →
      κ * ((allL cs Hl cl (cs.map fun ch => chunkOf ch.H Qp) (chunkOf Hl Qp))[j]'hj).2.2.1 *
        opv s (allL cs Hl cl (cs.map fun ch => chunkOf ch.H Qp) (chunkOf Hl Qp)) j = 1) :
    QuotOK cs Hl cl (cs.map fun ch => chunkOf ch.H Qp) (chunkOf Hl Qp) κ Qp := by
  have hd := (allL_doms Hl cl (chunkOf Hl Qp) Qp cs).trans hdom
  have hmem : ∀ p ∈ allL cs Hl cl (cs.map fun ch => chunkOf ch.H Qp) (chunkOf Hl Qp), p.1 ∈ splitD shift ω L n :=
    fun p hp => by rw [← hd]; exact List.mem_map_of_mem hp
  have hlenL : (allL cs Hl cl (cs.map fun ch => chunkOf ch.H Qp) (chunkOf Hl Qp)).length = L := by
    rw [← List.length_map (f := (·.1)), hd, splitD, List.length_map, List.length_range]
  refine quotOK_honest hκ (fpow ω L) n (split_pow hhalf hN) (fun p hp => split_coset (hmem p hp))
    (fun p hp => split_length (hmem p hp)) (by rw [hlenL]; exact hQ) (by rw [hd]; exact split_nodup hs hhalf hN) hfirst

-- ---------------------------------------------------------------------------
-- BabyBear's two-adic generators
-- ---------------------------------------------------------------------------

/-- **BabyBear's two-adic generators**, Plonky3's `TWO_ADIC_GENERATORS`
    (`baby-bear/src/baby_bear.rs`): entry `b` generates the subgroup of
    order `2^b`. -/
def bbGens : List F :=
  [0x1, 0x78000000, 0x67055c21, 0x5ee99486, 0xbb4c4e4, 0x2d4cc4da, 0x669d6090, 0x17b56c64,
   0x67456167, 0x688442f9, 0x145e952d, 0x4fe61226, 0x4c734715, 0x11c33e2a, 0x62c3d2b1,
   0x77cad399, 0x54c131f4, 0x4cabd6a6, 0x5cf5713f, 0x3e9430e8, 0xba067a3, 0x18adc27d,
   0x21fd55bc, 0x4b859b3d, 0x3bd57996, 0x4483d85a, 0x3a26eef8, 0x1a427a41]

def bbGen (b : Nat) : F := bbGens.getD b 0

/-- Each generator squares to the one before it, and the first is `-1`. -/
theorem bbGen_chain : (List.range 26).all (fun b => decide (bbGen (b + 2) * bbGen (b + 2) = bbGen (b + 1))) = true ∧
    bbGen 1 = -1 := by decide

theorem fpow_two_mul (x : F) (m : Nat) : fpow x (2 * m) = fpow (x * x) m := by
  rw [fpow_mul']; show fpow (1 * x * x) m = _; rw [one_mul']

/-- **`bbGen (k+1)` meets `split_nodup`'s hypothesis**: its `2^k`-th power
    is `-1`, for `k ≤ 26`. -/
theorem bbGen_half : ∀ k, k ≤ 26 → fpow (bbGen (k + 1)) (2 ^ k) = -1
  | 0, _ => by show 1 * bbGen 1 = -1; rw [one_mul']; exact bbGen_chain.2
  | k + 1, hk => by
    have hsq : bbGen (k + 2) * bbGen (k + 2) = bbGen (k + 1) :=
      of_decide_eq_true (List.all_eq_true.1 bbGen_chain.1 k (List.mem_range.2 (by omega)))
    rw [Nat.pow_succ, Nat.mul_comm, fpow_two_mul, hsq]
    exact bbGen_half k (by omega)

/-- **Plonky3's split domains over BabyBear have no repeated points**, and
    are cosets of one subgroup: the quotient domain `shift · ⟨ω⟩` of size
    `L n = 2^(k+1)`, `ω = bbGen (k+1)`. -/
theorem bb_split {shift : F} {L n k : Nat} (hs : shift ≠ 0) (hk : k ≤ 26) (hN : L * n = 2 ^ (k + 1)) :
    (splitD shift (bbGen (k + 1)) L n).flatten.Nodup ∧ fpow (fpow (bbGen (k + 1)) L) n = 1 :=
  ⟨split_nodup hs (bbGen_half k hk) hN, split_pow (bbGen_half k hk) hN⟩

end Circuit
