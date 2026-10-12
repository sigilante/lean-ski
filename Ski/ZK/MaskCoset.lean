import Ski.ZK.MaskRec

/-!
# The selectors on cosets

`QuotOK` asks normalized selectors: `κ μ_k ∏_{j ≠ k} v_j(x) = 1` at
every point `x` of chunk `k`'s domain.  Plonky3's chunk domains are
cosets `s_j ⟨g⟩` of one subgroup of order `n`, and `get_zp_cis` meets
the condition at each domain's first point only.  This file shows that
the first point suffices.  The vanishing polynomial of a coset of `⟨g⟩`
takes one value on every coset of `⟨g⟩`: `∏_i (y g - s gⁱ) = ∏_i (y - s
gⁱ)` when `gⁿ = 1` (`pr_rot`), so `v_j` is constant on `H_k`
(`coset_const`), and so is `∏_{j ≠ k} v_j` (`opv_congr`).
`sel_of_coset` derives the normalization from its value at each first
point, and `quotOK_of_coset` builds `QuotOK` with that hypothesis in
place of the pointwise one.

Plonky3's chunk `j` is the coset `shift · gen^j · ⟨gen^L⟩`, with first
point `s_j = shift · gen^j` and vanishing polynomial `Z_j = (X / s_j)ⁿ -
1`.  The model's `c_j · ∏_i (X - s_j gⁱ)` is `Z_j` when `c_j = s_j⁻ⁿ`.
With that scale, `κ = cis_l` and `m_k = cis_k / cis_l`, the first-point
hypothesis is `get_zp_cis`'s definition.

The honest chunks.  `chunkOf H Qp` interpolates `Qp`'s values on `H`.
With every chunk built this way, `quotOK_honest` discharges the
interpolation, the chunks' degrees and the disjointness.  What is left
is the domains' shape, the quotient's degree, and the selectors at each
first point.

The targets.  `qtg_ctg` and `qtgE_ctgE` rewrite the targets through the
quotient's defining identity `Qp Z_H = C`: they become `C / Z_H` on a
domain and `C / (Z_H κ ∏_j v_j)` off every domain.  `C`'s value at `ζ`
is the verifier's evaluation of the constraints on the opened trace
values, and the other factors are public domain data.  An instance for
a circuit still has to show that its `CSet` targets compute these values
from the openings.
-/

namespace Circuit

open ZKF

/-- `∏_{i < n} f i`. -/
def pr (f : Nat → F) : Nat → F
  | 0 => 1
  | n + 1 => pr f n * f n

theorem pr_cons (f : Nat → F) : ∀ n, pr f (n + 1) = f 0 * pr (fun i => f (i + 1)) n
  | 0 => by show 1 * f 0 = f 0 * 1; rw [one_mul', mul_one']
  | n + 1 => by
    show pr f (n + 1) * f (n + 1) = f 0 * (pr (fun i => f (i + 1)) n * f (n + 1))
    rw [pr_cons f n, mul_assoc']

theorem mul4 (a b c d : F) : a * b * (c * d) = a * c * (b * d) :=
  fid (e := v 0 * v 1 * (v 2 * v 3)) (e' := v 0 * v 2 * (v 1 * v 3)) (by decide) [a, b, c, d]

theorem pr_scale (c : F) (f : Nat → F) : ∀ m, pr (fun i => c * f i) m = fpow c m * pr f m
  | 0 => by show (1 : F) = 1 * 1; rw [one_mul']
  | m + 1 => by
    show pr (fun i => c * f i) m * (c * f m) = (fpow c m * c) * (pr f m * f m)
    rw [pr_scale c f m, mul4]

theorem pr_congr {f f' : Nat → F} (h : ∀ i, f i = f' i) (n : Nat) : pr f n = pr f' n := by
  rw [show f = f' from funext h]

/-- **A coset** `s, s g, …, s gⁿ⁻¹`. -/
def cosetL (s g : F) : Nat → List F
  | 0 => []
  | n + 1 => s :: cosetL (s * g) g n

theorem fpow_succ' (g : F) (i : Nat) : g * fpow g i = fpow g (i + 1) := mul_comm' g (fpow g i)

theorem fval_coset (x g : F) : ∀ n s, fval x (fvan (cosetL s g n)) = pr (fun i => x - s * fpow g i) n
  | 0, _ => fval_one x
  | n + 1, s => by
    show fval x (fclin s (fvan (cosetL (s * g) g n))) = _
    rw [fval_fclin, fval_coset x g n (s * g), pr_cons]
    show _ = (x - s * 1) * _
    rw [mul_one']
    exact congrArg _ (pr_congr (fun i => by rw [mul_assoc', fpow_succ']) n)

theorem mem_coset {x s g : F} : ∀ {n}, x ∈ cosetL s g n → ∃ t, t < n ∧ x = s * fpow g t
  | 0, h => nomatch h
  | n + 1, h => by
    rcases List.mem_cons.1 h with h | h
    · exact ⟨0, Nat.succ_pos n, by rw [h]; show s = s * 1; rw [mul_one']⟩
    · obtain ⟨t, ht, e⟩ := mem_coset h
      exact ⟨t + 1, Nat.succ_lt_succ ht, by rw [e, mul_assoc', fpow_succ']⟩

theorem rot1 (y g s p : F) : y * g - s * (p * g) = g * (y - s * p) :=
  fid (e := v 0 * v 1 - v 2 * (v 3 * v 1)) (e' := v 1 * (v 0 - v 2 * v 3)) (by decide) [y, g, s, p]

theorem rot2 (y g s G Q : F) (h : G * g = 1) : (y * g - s) * (G * Q) = Q * (y - s * G) := by
  have e : (y * g - s) * (G * Q) = (G * g) * (y * Q) - Q * (s * G) :=
    fid (e := (v 0 * v 1 - v 2) * (v 3 * v 4)) (e' := (v 3 * v 1) * (v 0 * v 4) - v 4 * (v 2 * v 3)) (by decide)
      [y, g, s, G, Q]
  rw [e, h, one_mul']
  exact fid (e := v 0 * v 1 - v 1 * (v 2 * v 3)) (e' := v 1 * (v 0 - v 2 * v 3)) (by decide) [y, Q, s, G]

/-- **A coset's vanishing product is invariant under `y ↦ y g`** when
    `gⁿ = 1`. -/
theorem pr_rot (y s g : F) (m : Nat) (hg : fpow g (m + 1) = 1) :
    pr (fun i => y * g - s * fpow g i) (m + 1) = pr (fun i => y - s * fpow g i) (m + 1) := by
  rw [pr_cons, pr_congr (f := fun i => y * g - s * fpow g (i + 1)) (f' := fun i => g * (y - s * fpow g i))
    (fun i => rot1 y g s (fpow g i)) m, pr_scale, show fpow g 0 = 1 from rfl, mul_one']
  exact rot2 y g s (fpow g m) _ hg

theorem pr_inv (s g y : F) (n : Nat) (hg : fpow g n = 1) : ∀ t,
    pr (fun i => y * fpow g t - s * fpow g i) n = pr (fun i => y - s * fpow g i) n
  | 0 => pr_congr (fun i => by show y * 1 - _ = _; rw [mul_one']) n
  | t + 1 => by
    rw [pr_congr (f' := fun i => y * fpow g t * g - s * fpow g i)
      (fun i => by show y * (fpow g t * g) - _ = _; rw [mul_assoc']) n]
    cases n with
    | zero => rfl
    | succ m => rw [pr_rot _ s g m hg]; exact pr_inv s g y (m + 1) hg t

/-- **A coset's vanishing polynomial is constant on every coset** of the
    same subgroup. -/
theorem coset_const {g sk sj x : F} {n : Nat} (hg : fpow g n = 1) (hx : x ∈ cosetL sk g n) :
    fval x (fvan (cosetL sj g n)) = fval sk (fvan (cosetL sj g n)) := by
  obtain ⟨t, _, rfl⟩ := mem_coset hx
  rw [fval_coset, fval_coset]
  exact pr_inv sj g sk n hg t

theorem ppoly_congr {x y : F} : ∀ L : List (List F × F × F × List F), (∀ p ∈ L, fval x (fvan p.1) = fval y (fvan p.1)) →
    fval x (rpoly.ppoly L) = fval y (rpoly.ppoly L)
  | [], _ => by rw [show rpoly.ppoly [] = [1] from rfl, fval_one, fval_one]
  | (H, c, μ, q) :: L, h => by
    show fval x (fmul (vpoly H c) (rpoly.ppoly L)) = fval y (fmul (vpoly H c) (rpoly.ppoly L))
    rw [fval_fmul, fval_fmul, fval_vpoly, fval_vpoly, h _ List.mem_cons_self,
      ppoly_congr L (fun p hp => h p (List.mem_cons_of_mem _ hp))]

/-- `∏_{j ≠ k} v_j` takes equal values where every `v_j` does. -/
theorem opv_congr {x y : F} : ∀ (L : List (List F × F × F × List F)) (k : Nat),
    (∀ p ∈ L, fval x (fvan p.1) = fval y (fvan p.1)) → opv x L k = opv y L k
  | [], _, _ => rfl
  | _ :: L, 0, h => ppoly_congr L (fun p hp => h p (List.mem_cons_of_mem _ hp))
  | (H, c, μ, q) :: L, k + 1, h => by
    show c * fval x (fvan H) * opv x L k = c * fval y (fvan H) * opv y L k
    rw [h _ List.mem_cons_self, opv_congr L k (fun p hp => h p (List.mem_cons_of_mem _ hp))]

/-- **The selectors are normalized from each first point**: when every
    domain is a coset of `⟨g⟩` with `gⁿ = 1`, `κ μ_k ∏_{j ≠ k} v_j = 1` at
    each domain's first point `s_k` (Plonky3's `get_zp_cis`) gives it on
    the whole domain. -/
theorem sel_of_coset (κ g : F) (n : Nat) (hg : fpow g n = 1) (L : List (List F × F × F × List F))
    (hcos : ∀ p ∈ L, ∃ s, p.1 = cosetL s g n)
    (hfirst : ∀ k (hk : k < L.length), ∀ s, (L[k]'hk).1 = cosetL s g n → κ * (L[k]'hk).2.2.1 * opv s L k = 1) :
    ∀ k (hk : k < L.length), ∀ x ∈ (L[k]'hk).1, κ * (L[k]'hk).2.2.1 * opv x L k = 1 := by
  intro k hk x hx
  obtain ⟨s, hs⟩ := hcos _ (List.getElem_mem hk)
  rw [hs] at hx
  rw [opv_congr (y := s) L k (fun p hp => by
    obtain ⟨sp, hsp⟩ := hcos p hp
    rw [hsp]; exact coset_const hg hx)]
  exact hfirst k hk s hs

/-- **`QuotOK` on cosets**: the normalization asked only at each
    domain's first point. -/
theorem quotOK_of_coset {cs : List Chunk} {Hl : List F} {cl : F} {qs : List (List F)} {ql : List F} {κ : F}
    {Qp : List F} (hκ : κ ≠ 0) (g : F) (n : Nat) (hg : fpow g n = 1)
    (hcos : ∀ p ∈ allL cs Hl cl qs ql, ∃ s, p.1 = cosetL s g n)
    (hsz : ∀ p ∈ allL cs Hl cl qs ql, p.1.length = n ∧ p.2.2.2.length ≤ n)
    (hQ : Qp.length ≤ (allL cs Hl cl qs ql).length * n) (hnd : ((allL cs Hl cl qs ql).map (·.1)).flatten.Nodup)
    (hdis : ∀ k j (hk : k < (allL cs Hl cl qs ql).length) (hj : j < (allL cs Hl cl qs ql).length), j ≠ k →
      ∀ x ∈ ((allL cs Hl cl qs ql)[k]'hk).1, x ∉ ((allL cs Hl cl qs ql)[j]'hj).1)
    (hint : ∀ p ∈ allL cs Hl cl qs ql, ∀ x ∈ p.1, fval x p.2.2.2 = fval x Qp)
    (hfirst : ∀ k (hk : k < (allL cs Hl cl qs ql).length), ∀ s, ((allL cs Hl cl qs ql)[k]'hk).1 = cosetL s g n →
      κ * ((allL cs Hl cl qs ql)[k]'hk).2.2.1 * opv s (allL cs Hl cl qs ql) k = 1) :
    QuotOK cs Hl cl qs ql κ Qp :=
  ⟨hκ, n, hsz, hQ, hnd, hdis, hint, sel_of_coset κ g n hg _ hcos hfirst⟩

-- ---------------------------------------------------------------------------
-- The targets from the constraint polynomial
-- ---------------------------------------------------------------------------

theorem cdiv_c (Z K Q fk : F) : Z * (K * (Q * fk)) = (K * fk) * (Q * Z) :=
  fid (e := v 0 * (v 1 * (v 2 * v 3))) (e' := (v 1 * v 3) * (v 2 * v 0)) (by decide) [Z, K, Q, fk]

/-- `Q / K = C / (Z K)` when `Q Z = C`, `Z ≠ 0`. -/
theorem cdiv (Q K Z C : F) (h : Q * Z = C) (hz : Z ≠ 0) : Q * finv K = C * finv (Z * K) := by
  by_cases hk : K = 0
  · rw [hk, EF.finv_zero, mul_zero', mul_zero', EF.finv_zero, mul_zero']
  · exact qdiv_step Z K _ C (by rw [cdiv_c, mul_finv hk, one_mul', h]) (mul_ne_zero' hz hk)

theorem cdivE (Q K Z C : EF) (h : Q.mul Z = C) (hz : Z ≠ EF.zero) : Q.mul K.inv = C.mul (Z.mul K).inv := by
  by_cases hk : K = EF.zero
  · rw [hk, EF.inv_zero, EF.mul_zero, EF.mul_zero, EF.inv_zero, EF.mul_zero]
  · refine div_stepE Z K _ C ?_ (mulE_ne_zero hz hk)
    rw [← EF.mul_assoc K, EF.mul_comm K, EF.mul_assoc Q, EF.mul_inv hk, EF.mul_one,
      EF.mul_comm Z, h]

/-- **The targets from the constraint polynomial**: on every domain
    `C / Z_H`, and off every domain `C / (Z_H κ ∏_j v_j)`. -/
def ctg (cs : List Chunk) (Hl : List F) (cl : F) (qs : List (List F)) (ql : List F) (κ : F) (ZH Cp : List F) (x : F) : F :=
  if x ∈ Hl ∨ inSome x cs = true then fval x Cp * finv (fval x ZH)
  else fval x Cp * finv (fval x ZH * (κ * fval x (rpoly.ppoly (allL cs Hl cl qs ql))))

def ctgE (ζ : EF) (cs : List Chunk) (Hl : List F) (cl : F) (qs : List (List F)) (ql : List F) (κ : F) (ZH Cp : List F) : EF :=
  (fvalE ζ Cp).mul ((fvalE ζ ZH).mul ((EF.ofF κ).mul (fvalE ζ (rpoly.ppoly (allL cs Hl cl qs ql))))).inv

/-- **The quotient's targets are the constraints'**: when `Qp Z_H = C`,
    `qtg` is `ctg` wherever `Z_H` does not vanish, and `qtgE` is `ctgE`
    when `Z_H(ζ) ≠ 0`. -/
theorem qtg_ctg {cs : List Chunk} {Hl : List F} {cl : F} {qs : List (List F)} {ql : List F} {κ : F}
    {Qp ZH Cp : List F} (h : FZero (fcdiff (fmul Qp ZH) Cp)) (x : F) (hz : fval x ZH ≠ 0) :
    qtg cs Hl cl qs ql κ Qp x = ctg cs Hl cl qs ql κ ZH Cp x := by
  have hq : fval x Qp * fval x ZH = fval x Cp := by
    rw [← fval_fmul]; exact sub_eq_zero (by rw [← fval_fcdiff]; exact fval_fzero x _ h)
  unfold qtg ctg
  split
  · rw [← hq, mul_assoc', mul_finv hz, mul_one']
  · exact cdiv _ _ _ _ hq hz

theorem qtgE_ctgE {ζ : EF} {cs : List Chunk} {Hl : List F} {cl : F} {qs : List (List F)} {ql : List F} {κ : F}
    {Qp ZH Cp : List F} (h : FZero (fcdiff (fmul Qp ZH) Cp)) (hz : fvalE ζ ZH ≠ EF.zero) :
    qtgE ζ cs Hl cl qs ql κ Qp = ctgE ζ cs Hl cl qs ql κ ZH Cp := by
  have hq : (fvalE ζ Qp).mul (fvalE ζ ZH) = fvalE ζ Cp := by
    rw [← fvalE_fmul]; exact (sub_eq_zero_iff _ _).1 (by rw [← fvalE_fcdiff]; exact fvalE_fzero ζ _ h)
  exact cdivE _ _ _ _ hq hz

-- ---------------------------------------------------------------------------
-- The honest chunks: the quotient interpolated on each domain
-- ---------------------------------------------------------------------------

/-- **The honest chunk** on `H`: `Qp`'s values on `H`, interpolated. -/
def chunkOf (H Qp : List F) : List F := finterp (H.map fun x => (x, fval x Qp))

theorem chunkOf_length (H Qp : List F) : (chunkOf H Qp).length ≤ H.length := by
  have := finterp_length (H.map fun x => (x, fval x Qp)); rw [List.length_map] at this; exact this

theorem chunkOf_eval {H : List F} (Qp : List F) (hnd : H.Nodup) {x : F} (hx : x ∈ H) :
    fval x (chunkOf H Qp) = fval x Qp := by
  have hfst : ((H.map fun x => (x, fval x Qp)).map Prod.fst) = H := by
    rw [List.map_map]; exact List.map_id' H
  exact finterp_eval _ (by rw [hfst]; exact hnd) (x, fval x Qp) (List.mem_map.2 ⟨x, hx, rfl⟩)

/-- The honest data: every chunk the quotient's interpolant on its domain. -/
theorem mem_honestL {Qp : List F} {p : List F × F × F × List F} : ∀ {cs : List Chunk},
    p ∈ List.zipWith (fun (ch : Chunk) q => (ch.H, ch.c, ch.m, q)) cs (cs.map fun ch => chunkOf ch.H Qp) →
    p.2.2.2 = chunkOf p.1 Qp
  | [], hp => nomatch hp
  | ch :: cs, hp => by
    rcases List.mem_cons.1 hp with rfl | hp
    · rfl
    · exact mem_honestL hp

theorem mem_allL_honest {cs : List Chunk} {Hl : List F} {cl : F} {Qp : List F} {p : List F × F × F × List F}
    (hp : p ∈ allL cs Hl cl (cs.map fun ch => chunkOf ch.H Qp) (chunkOf Hl Qp)) : p.2.2.2 = chunkOf p.1 Qp := by
  rcases List.mem_append.1 hp with hp | hp
  · exact mem_honestL hp
  · rcases List.mem_singleton.1 hp with rfl; rfl

/-- Domains without repeats, together, are disjoint and each without repeats. -/
theorem dis_of_nodup (L : List (List F × F × F × List F)) (hnd : (L.map (·.1)).flatten.Nodup) :
    (∀ p ∈ L, p.1.Nodup) ∧
    ∀ k j (hk : k < L.length) (hj : j < L.length), j ≠ k → ∀ x ∈ (L[k]'hk).1, x ∉ (L[j]'hj).1 := by
  obtain ⟨h1, h2⟩ := List.pairwise_flatten.1 hnd
  refine ⟨fun p hp => h1 p.1 (List.mem_map.2 ⟨p, hp, rfl⟩), fun k j hk hj hjk x hxk hxj => ?_⟩
  have hp := List.pairwise_iff_getElem.1 h2
  rcases Nat.lt_or_gt_of_ne hjk with h | h
  · have := hp j k (by rw [List.length_map]; exact hj) (by rw [List.length_map]; exact hk) h
    rw [List.getElem_map, List.getElem_map] at this
    exact this x hxj x hxk rfl
  · have := hp k j (by rw [List.length_map]; exact hk) (by rw [List.length_map]; exact hj) h
    rw [List.getElem_map, List.getElem_map] at this
    exact this x hxk x hxj rfl

/-- **The honest chunks meet `QuotOK`**: with each chunk the quotient
    interpolated on its domain, `QuotOK` asks only that the domains be
    cosets of `⟨g⟩` of size `n`, `gⁿ = 1`, without repeats together, the
    quotient below `(|cs| + 1) n` coefficients, and the selectors
    normalized at each first point. -/
theorem quotOK_honest {cs : List Chunk} {Hl : List F} {cl : F} {κ : F} {Qp : List F} (hκ : κ ≠ 0) (g : F) (n : Nat)
    (hg : fpow g n = 1)
    (hcos : ∀ p ∈ allL cs Hl cl (cs.map fun ch => chunkOf ch.H Qp) (chunkOf Hl Qp), ∃ s, p.1 = cosetL s g n)
    (hlen : ∀ p ∈ allL cs Hl cl (cs.map fun ch => chunkOf ch.H Qp) (chunkOf Hl Qp), p.1.length = n)
    (hQ : Qp.length ≤ (allL cs Hl cl (cs.map fun ch => chunkOf ch.H Qp) (chunkOf Hl Qp)).length * n)
    (hnd : ((allL cs Hl cl (cs.map fun ch => chunkOf ch.H Qp) (chunkOf Hl Qp)).map (·.1)).flatten.Nodup)
    (hfirst : ∀ k (hk : k < (allL cs Hl cl (cs.map fun ch => chunkOf ch.H Qp) (chunkOf Hl Qp)).length), ∀ s,
      ((allL cs Hl cl (cs.map fun ch => chunkOf ch.H Qp) (chunkOf Hl Qp))[k]'hk).1 = cosetL s g n →
      κ * ((allL cs Hl cl (cs.map fun ch => chunkOf ch.H Qp) (chunkOf Hl Qp))[k]'hk).2.2.1 *
        opv s (allL cs Hl cl (cs.map fun ch => chunkOf ch.H Qp) (chunkOf Hl Qp)) k = 1) :
    QuotOK cs Hl cl (cs.map fun ch => chunkOf ch.H Qp) (chunkOf Hl Qp) κ Qp := by
  obtain ⟨hnd1, hdis⟩ := dis_of_nodup _ hnd
  refine quotOK_of_coset hκ g n hg hcos (fun p hp => ⟨hlen p hp, ?_⟩) hQ hnd hdis
    (fun p hp x hx => by rw [mem_allL_honest hp]; exact chunkOf_eval Qp (hnd1 p hp) hx) hfirst
  rw [mem_allL_honest hp, ← hlen p hp]; exact chunkOf_length _ _

end Circuit
