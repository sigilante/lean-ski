import Ski.ZK.MaskCom

/-!
# The honest chunks show the quotient

`pcsCloseN_chunks` and its successors assume `RecOK`: every column's
chunks show the verifier the targets `JS` and `Jζ`.  This file derives
`RecOK` from what Plonky3's prover does.  It splits the quotient `Qp`
into chunks `q_i`, each equal to `Qp` on its own domain `H_i`, and the
verifier recombines them with the selectors `get_zp_cis` computes.

`rpoly_quot` proves the recombination `κ Σ_i μ_i q_i ∏_{j ≠ i} v_j` is
`Qp` itself.  It needs disjoint domains of size `n`, chunks of fewer
than `n` coefficients, `Qp` of fewer than `|L| n`, and normalized
selectors (`κ μ_k ∏_{j ≠ k} v_j = 1` on `H_k`).  The recombination is
the product `∏_j v_j` times the normalized sum, at a query point
(`rpoly_val`) and at `ζ` (`rpoly_valE`), so off every domain the sum is
`Qp / (κ ∏_j v_j)` (`shows_of_quot`).  `shows_of_honest` gives `Shows`
from `QuotOK`, with the targets `qtg` and `qtgE`.  `recOK_of_honest`
lifts the result to every column.

Plonky3's split meets `QuotOK` with `κ = cis_l` and `m_i = cis_i / cis_l`
(`get_zp_cis`, `mul_coeffs`).  Its domains are cosets of one subgroup of
order `n`, so each `v_j` is constant on another chunk's domain and the
normalization holds there.

Scope.  `recOK_of_honest` takes `QuotOK` for each column, normalization
included; it does not derive the normalization from the cosets'
structure.  It also takes the verifier's targets equal to `qtg` on the
query points and `qtgE` at `ζ`: the quotient's values at the opened
points are functions of the openings.  At `ζ` this is the constraint
check `Qp(ζ) = C(ζ) / Z_H(ζ)`.
-/

namespace Circuit

open ZKF

/-- A chunk's vanishing polynomial `c · ∏_{a ∈ H} (X - a)`. -/
def vpoly (H : List F) (c : F) : List F := fcscale c (fvan H)

/-- **The recombination before its scale**, `Σ_i μ_i q_i ∏_{j ≠ i} v_j`,
    and the product `∏_j v_j`, over the chunks `(H, c, μ, q)`. -/
def rpoly : List (List F × F × F × List F) → List F
  | [] => []
  | (H, c, μ, q) :: L => fcadd (fcscale μ (fmul q (ppoly L))) (fmul (rpoly L) (vpoly H c))
where
  ppoly : List (List F × F × F × List F) → List F
    | [] => [1]
    | (H, c, _, _) :: L => fmul (vpoly H c) (ppoly L)

/-- The normalized sum `Σ_i μ_i q_i(x) / v_i(x)`. -/
def nsum (x : F) : List (List F × F × F × List F) → F
  | [] => 0
  | (H, c, μ, q) :: L => μ * (fval x q * finv (c * fval x (fvan H))) + nsum x L

theorem fval_vpoly (x : F) (H : List F) (c : F) : fval x (vpoly H c) = c * fval x (fvan H) := fval_fcscale x c _

theorem rstep_val (μ q P V S fi : F) (hV : V * fi = 1) :
    μ * (q * P) + V * (P * S) = (V * P) * (μ * (q * fi) + S) := by
  have e : (V * P) * (μ * (q * fi) + S) = μ * (q * P) * (V * fi) + V * (P * S) :=
    fid (e := (v 0 * v 1) * (v 2 * (v 3 * v 4) + v 5)) (e' := v 2 * (v 3 * v 1) * (v 0 * v 4) + v 0 * (v 1 * v 5))
      (by decide) [V, P, μ, q, fi, S]
  rw [e, hV, mul_one']

/-- **Off every domain, the recombination is the product times the
    normalized sum**. -/
theorem rpoly_val (x : F) : ∀ L : List (List F × F × F × List F), (∀ p ∈ L, p.2.1 * fval x (fvan p.1) ≠ 0) →
    fval x (rpoly L) = fval x (rpoly.ppoly L) * nsum x L
  | [], _ => by show (0 : F) = fval x [1] * 0; rw [mul_zero']
  | (H, c, μ, q) :: L, h => by
    have hV : c * fval x (fvan H) ≠ 0 := h (H, c, μ, q) List.mem_cons_self
    show fval x (fcadd (fcscale μ (fmul q (rpoly.ppoly L))) (fmul (rpoly L) (vpoly H c))) =
      fval x (fmul (vpoly H c) (rpoly.ppoly L)) * (μ * (fval x q * finv (c * fval x (fvan H))) + nsum x L)
    rw [fval_fcadd, fval_fcscale, fval_fmul, fval_fmul, fval_fmul, fval_vpoly,
      rpoly_val x L (fun p hp => h p (List.mem_cons_of_mem _ hp)), mul_comm' _ (c * fval x (fvan H))]
    exact rstep_val _ _ _ _ _ _ (mul_finv hV)

/-- `∏_{j ≠ k} v_j(x)`. -/
def opv (x : F) : List (List F × F × F × List F) → Nat → F
  | [], _ => 1
  | _ :: L, 0 => fval x (rpoly.ppoly L)
  | (H, c, _, _) :: L, k + 1 => c * fval x (fvan H) * opv x L k

theorem ppoly_zero (x : F) : ∀ (L : List (List F × F × F × List F)) (k : Nat) (hk : k < L.length),
    x ∈ (L[k]'hk).1 → fval x (rpoly.ppoly L) = 0
  | (H, c, μ, q) :: L, 0, _, hx => by
    show fval x (fmul (vpoly H c) (rpoly.ppoly L)) = 0
    rw [fval_fmul, fval_vpoly, fvan_root x H hx, mul_zero', zero_mul']
  | (H, c, μ, q) :: L, k + 1, hk, hx => by
    show fval x (fmul (vpoly H c) (rpoly.ppoly L)) = 0
    rw [fval_fmul, ppoly_zero x L k (Nat.lt_of_succ_lt_succ hk) hx, mul_zero']
  | [], _, hk, _ => absurd hk (Nat.not_lt_zero _)

theorem on_step0 (μ q P V R : F) (hV : V = 0) : μ * (q * P) + V * R = μ * (q * P) := by
  rw [hV, zero_mul', add_zero']

theorem on_step1 (μ q V R μk qk o : F) (hR : R = μk * (qk * o)) :
    μ * (q * 0) + V * R = μk * (qk * (V * o)) := by
  rw [hR, mul_zero', mul_zero', zero_add']
  exact fid (e := v 0 * (v 1 * (v 2 * v 3))) (e' := v 1 * (v 2 * (v 0 * v 3))) (by decide) [V, μk, qk, o]

/-- **On chunk `k`'s domain only chunk `k`'s term survives**. -/
theorem rpoly_on (x : F) : ∀ (L : List (List F × F × F × List F)) (k : Nat) (hk : k < L.length),
    x ∈ (L[k]'hk).1 → (∀ j (hj : j < L.length), j ≠ k → x ∉ (L[j]'hj).1) →
    fval x (rpoly L) = (L[k]'hk).2.2.1 * (fval x (L[k]'hk).2.2.2 * opv x L k)
  | (H, c, μ, q) :: L, 0, _, hx, _ => by
    show fval x (fcadd (fcscale μ (fmul q (rpoly.ppoly L))) (fmul (rpoly L) (vpoly H c))) = μ * (fval x q * fval x (rpoly.ppoly L))
    rw [fval_fcadd, fval_fcscale, fval_fmul, fval_fmul, fval_vpoly, mul_comm' (fval x (rpoly L))]
    exact on_step0 _ _ _ _ _ (by rw [fvan_root x H hx, mul_zero'])
  | (H, c, μ, q) :: L, k + 1, hk, hx, hdis => by
    show fval x (fcadd (fcscale μ (fmul q (rpoly.ppoly L))) (fmul (rpoly L) (vpoly H c))) =
      (L[k]'(Nat.lt_of_succ_lt_succ hk)).2.2.1 * (fval x (L[k]'(Nat.lt_of_succ_lt_succ hk)).2.2.2 *
        (c * fval x (fvan H) * opv x L k))
    rw [fval_fcadd, fval_fcscale, fval_fmul, fval_fmul, fval_vpoly, ppoly_zero x L k (Nat.lt_of_succ_lt_succ hk) hx,
      mul_comm' (fval x (rpoly L))]
    exact on_step1 _ _ _ _ _ _ _ (rpoly_on x L k (Nat.lt_of_succ_lt_succ hk) hx
      (fun j hj hjk => hdis (j + 1) (Nat.succ_lt_succ hj) (fun e => hjk (Nat.succ.inj e))))
  | [], _, hk, _, _ => absurd hk (Nat.not_lt_zero _)

theorem vpoly_ne (H : List F) (c : F) : vpoly H c ≠ [] := by
  unfold vpoly fcscale; rw [Ne, List.map_eq_nil_iff]; exact fvan_ne_nil H

theorem ppoly_ne : ∀ L : List (List F × F × F × List F), rpoly.ppoly L ≠ []
  | [] => List.cons_ne_nil _ _
  | (H, c, _, _) :: _ => fmul_ne_nil _ _ (vpoly_ne H c)

/-- **The recombination's degree**: fewer than `|L| h` coefficients. -/
theorem rpoly_len (h : Nat) : ∀ L : List (List F × F × F × List F), (∀ p ∈ L, p.1.length = h ∧ p.2.2.2.length ≤ h) →
    (rpoly L).length ≤ L.length * h ∧ (rpoly.ppoly L).length ≤ L.length * h + 1
  | [], _ => ⟨Nat.zero_le _, by show 1 ≤ 0 * h + 1; omega⟩
  | (H, c, μ, q) :: L, hl => by
    obtain ⟨hH, hq0⟩ := hl (H, c, μ, q) List.mem_cons_self
    have hq : q.length ≤ h := hq0
    have hH' : H.length = h := hH
    obtain ⟨ih1, ih2⟩ := rpoly_len h L (fun p hp => hl p (List.mem_cons_of_mem _ hp))
    have hv : (vpoly H c).length ≤ h + 1 := by
      unfold vpoly; rw [fcscale_length]; have := fvan_length H; rw [hH'] at this; exact this
    refine ⟨?_, ?_⟩
    · show (fcadd (fcscale μ (fmul q (rpoly.ppoly L))) (fmul (rpoly L) (vpoly H c))).length ≤ (L.length + 1) * h
      have a1 := fcadd_length (fcscale μ (fmul q (rpoly.ppoly L))) (fmul (rpoly L) (vpoly H c))
      have a2 := fmul_length q (rpoly.ppoly L) (ppoly_ne L)
      have a3 := fmul_length (rpoly L) (vpoly H c) (vpoly_ne H c)
      rw [fcscale_length] at a1
      rw [Nat.succ_mul]
      refine Nat.le_trans a1 (Nat.max_le.2 ⟨by omega, by omega⟩)
    · show (fmul (vpoly H c) (rpoly.ppoly L)).length ≤ (L.length + 1) * h + 1
      have := fmul_length (vpoly H c) (rpoly.ppoly L) (ppoly_ne L)
      rw [Nat.succ_mul]; omega

theorem flat_len (h : Nat) : ∀ L : List (List F × F × F × List F), (∀ p ∈ L, p.1.length = h) →
    ((L.map (·.1)).flatten).length = L.length * h
  | [], _ => (Nat.zero_mul h).symm
  | p :: L, hl => by
    rw [List.map_cons, List.flatten_cons, List.length_append, flat_len h L (fun q hq => hl q (List.mem_cons_of_mem _ hq)),
      hl p List.mem_cons_self, List.length_cons, Nat.succ_mul, Nat.add_comm]

theorem sel_step (κ μ qx o Qx : F) (hsel : κ * μ * o = 1) (hq : qx = Qx) : κ * (μ * (qx * o)) = Qx := by
  have e : κ * (μ * (qx * o)) = (κ * μ * o) * qx :=
    fid (e := v 0 * (v 1 * (v 2 * v 3))) (e' := (v 0 * v 1 * v 3) * v 2) (by decide) [κ, μ, qx, o]
  rw [e, hsel, one_mul', hq]

/-- **The recombination is the quotient**: when each chunk agrees with the
    quotient `Qp` on its own domain, the selectors are normalized
    (`κ μ_k ∏_{j ≠ k} v_j = 1` on chunk `k`'s domain, Plonky3's
    `get_zp_cis`), the domains are disjoint, each chunk has fewer than `n`
    coefficients and `Qp` fewer than `|L| n`, `κ · Σ_i μ_i q_i ∏_{j ≠ i} v_j`
    is `Qp`. -/
theorem rpoly_quot {h : Nat} (κ : F) (L : List (List F × F × F × List F)) (Qp : List F)
    (hsz : ∀ p ∈ L, p.1.length = h ∧ p.2.2.2.length ≤ h) (hQ : Qp.length ≤ L.length * h)
    (hnd : (L.map (·.1)).flatten.Nodup)
    (hdis : ∀ k j (hk : k < L.length) (hj : j < L.length), j ≠ k → ∀ x ∈ (L[k]'hk).1, x ∉ (L[j]'hj).1)
    (hint : ∀ p ∈ L, ∀ x ∈ p.1, fval x p.2.2.2 = fval x Qp)
    (hsel : ∀ k (hk : k < L.length), ∀ x ∈ (L[k]'hk).1, κ * (L[k]'hk).2.2.1 * opv x L k = 1) :
    FZero (fcdiff (fcscale κ (rpoly L)) Qp) := by
  have hpl : (fcscale κ (rpoly L)).length ≤ L.length * h := by rw [fcscale_length]; exact (rpoly_len h L hsz).1
  have hlen : ((L.map (·.1)).flatten).length = L.length * h := flat_len h L (fun p hp => (hsz p hp).1)
  refine fagree_zero hpl hQ _ hnd hlen (fun x hx => ?_)
  obtain ⟨l, hl, hxl⟩ := List.mem_flatten.1 hx
  obtain ⟨pp, hpp, rfl⟩ := List.mem_map.1 hl
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hpp
  rw [fval_fcscale, rpoly_on x L k hk hxl (fun j hj hjk => hdis k j hk hj hjk x hxl)]
  exact sel_step _ _ _ _ _ (hsel k hk x hxl) (hint _ (List.getElem_mem hk) x hxl)

/-- The normalized sum at a point of the extension. -/
def nsumE (z : EF) : List (List F × F × F × List F) → EF
  | [] => EF.zero
  | (H, c, μ, q) :: L => ((EF.ofF μ).mul ((fvalE z q).mul ((EF.ofF c).mul (fvalE z (fvan H))).inv)).add (nsumE z L)

theorem rE1 (V P μ Y : EF) : (V.mul P).mul (μ.mul Y) = (μ.mul (Y.mul P)).mul V :=
  Q.eq_of_norm (p := ((Q.var 0).mul (Q.var 1)).mul ((Q.var 2).mul (Q.var 3)))
    (q := ((Q.var 2).mul ((Q.var 3).mul (Q.var 1))).mul (Q.var 0)) (by decide) (env4 V P μ Y)

theorem rE2 (q fi P : EF) : (q.mul fi).mul P = (q.mul P).mul fi :=
  Q.eq_of_norm (p := ((Q.var 0).mul (Q.var 1)).mul (Q.var 2)) (q := ((Q.var 0).mul (Q.var 2)).mul (Q.var 1)) (by decide)
    (env3 q fi P)

theorem rE3 (μ B fi V : EF) : (μ.mul (B.mul fi)).mul V = (μ.mul B).mul (V.mul fi) :=
  Q.eq_of_norm (p := ((Q.var 0).mul ((Q.var 1).mul (Q.var 2))).mul (Q.var 3))
    (q := ((Q.var 0).mul (Q.var 1)).mul ((Q.var 3).mul (Q.var 2))) (by decide) (env4 μ B fi V)

theorem rstepE_c (V P S : EF) : (V.mul P).mul S = (P.mul S).mul V :=
  Q.eq_of_norm (p := ((Q.var 0).mul (Q.var 1)).mul (Q.var 2)) (q := ((Q.var 1).mul (Q.var 2)).mul (Q.var 0)) (by decide)
    (env3 V P S)

theorem rstepE (μ q P V S fi : EF) (hV : V.mul fi = EF.one) :
    (μ.mul (q.mul P)).add ((P.mul S).mul V) = (V.mul P).mul ((μ.mul (q.mul fi)).add S) := by
  rw [EF.mul_add, rE1 V P μ (q.mul fi), rE2 q fi P, rE3 μ (q.mul P) fi V, hV, EF.mul_one, rstepE_c V P S]

theorem fvalE_vpoly (z : EF) (H : List F) (c : F) : fvalE z (vpoly H c) = (EF.ofF c).mul (fvalE z (fvan H)) :=
  fvalE_fcscale z c _

theorem rpoly_valE (z : EF) : ∀ L : List (List F × F × F × List F),
    (∀ p ∈ L, (EF.ofF p.2.1).mul (fvalE z (fvan p.1)) ≠ EF.zero) →
    fvalE z (rpoly L) = (fvalE z (rpoly.ppoly L)).mul (nsumE z L)
  | [], _ => by show EF.zero = (fvalE z [1]).mul EF.zero; rw [EF.mul_zero]
  | (H, c, μ, q) :: L, h => by
    have hV : (EF.ofF c).mul (fvalE z (fvan H)) ≠ EF.zero := h (H, c, μ, q) List.mem_cons_self
    show fvalE z (fcadd (fcscale μ (fmul q (rpoly.ppoly L))) (fmul (rpoly L) (vpoly H c))) =
      (fvalE z (fmul (vpoly H c) (rpoly.ppoly L))).mul
        (((EF.ofF μ).mul ((fvalE z q).mul ((EF.ofF c).mul (fvalE z (fvan H))).inv)).add (nsumE z L))
    rw [fvalE_fcadd, fvalE_fcscale, fvalE_fmul, fvalE_fmul, fvalE_fmul, fvalE_vpoly,
      rpoly_valE z L (fun p hp => h p (List.mem_cons_of_mem _ hp))]
    exact rstepE _ _ _ _ _ _ (EF.mul_inv hV)

/-- The chunks as `(H, c, μ, q)`, the last with weight one. -/
def allL (cs : List Chunk) (Hl : List F) (cl : F) (qs : List (List F)) (ql : List F) : List (List F × F × F × List F) :=
  List.zipWith (fun (ch : Chunk) q => (ch.H, ch.c, ch.m, q)) cs qs ++ [(Hl, cl, 1, ql)]

theorem nsum_append (x : F) : ∀ (A B : List (List F × F × F × List F)), nsum x (A ++ B) = nsum x A + nsum x B
  | [], B => by show nsum x B = 0 + nsum x B; rw [zero_add']
  | (H, c, μ, q) :: A, B => by
    show μ * (fval x q * finv (c * fval x (fvan H))) + nsum x (A ++ B) =
      (μ * (fval x q * finv (c * fval x (fvan H))) + nsum x A) + nsum x B
    rw [nsum_append x A B, add_assoc']

theorem nsum_chunks (x : F) : ∀ (cs : List Chunk) (qs : List (List F)),
    nsum x (List.zipWith (fun (ch : Chunk) q => (ch.H, ch.c, ch.m, q)) cs qs) = jsumF x cs qs
  | [], _ => rfl
  | _ :: _, [] => rfl
  | ch :: cs, q :: qs => by
    show ch.m * (fval x q * finv (ch.c * fval x (fvan ch.H))) + nsum x (List.zipWith _ cs qs) = _
    rw [nsum_chunks x cs qs]; rfl

/-- **The normalized sum is `chunkJ`**. -/
theorem nsum_allL (x : F) (cs : List Chunk) (Hl : List F) (cl : F) (qs : List (List F)) (ql : List F) :
    nsum x (allL cs Hl cl qs ql) = chunkJ x cs Hl cl qs ql := by
  unfold allL chunkJ
  rw [nsum_append, nsum_chunks]
  show jsumF x cs qs + (1 * (fval x ql * finv (cl * fval x (fvan Hl))) + 0) = _
  rw [one_mul', add_zero', add_comm']

theorem nsumE_append (z : EF) : ∀ (A B : List (List F × F × F × List F)), nsumE z (A ++ B) = (nsumE z A).add (nsumE z B)
  | [], B => by show nsumE z B = EF.zero.add (nsumE z B); rw [EF.zero_add]
  | (H, c, μ, q) :: A, B => by
    show (_ : EF).add (nsumE z (A ++ B)) = ((_ : EF).add (nsumE z A)).add (nsumE z B)
    rw [nsumE_append z A B, EF.add_assoc]

theorem nsumE_chunks (z : EF) : ∀ (cs : List Chunk) (qs : List (List F)),
    nsumE z (List.zipWith (fun (ch : Chunk) q => (ch.H, ch.c, ch.m, q)) cs qs) = jsumE z cs qs
  | [], _ => rfl
  | _ :: _, [] => rfl
  | ch :: cs, q :: qs => by
    show (_ : EF).add (nsumE z (List.zipWith _ cs qs)) = _
    rw [nsumE_chunks z cs qs]; rfl

theorem nsumE_allL (z : EF) (cs : List Chunk) (Hl : List F) (cl : F) (qs : List (List F)) (ql : List F) :
    nsumE z (allL cs Hl cl qs ql) = chunkJE z cs Hl cl qs ql := by
  unfold allL chunkJE
  rw [nsumE_append, nsumE_chunks]
  show (jsumE z cs qs).add (((EF.ofF 1).mul ((fvalE z ql).mul ((EF.ofF cl).mul (fvalE z (fvan Hl))).inv)).add EF.zero) = _
  rw [show EF.ofF 1 = EF.one from rfl, EF.one_mul, EF.add_zero, EF.add_comm]

theorem qdiv_c (κ P N fi : F) : κ * (P * N) * fi = (κ * P * fi) * N :=
  fid (e := v 0 * (v 1 * v 2) * v 3) (e' := (v 0 * v 1 * v 3) * v 2) (by decide) [κ, P, N, fi]

theorem qdiv_step (κ P N Q : F) (h : κ * (P * N) = Q) (hne : κ * P ≠ 0) : N = Q * finv (κ * P) := by
  rw [← h, qdiv_c, mul_finv hne, one_mul']

theorem div_stepE (κ P N Q : EF) (h : κ.mul (P.mul N) = Q) (hne : κ.mul P ≠ EF.zero) : N = Q.mul (κ.mul P).inv := by
  rw [← h, ← EF.mul_assoc, EF.mul_assoc, EF.mul_comm N, ← EF.mul_assoc, EF.mul_inv hne, EF.one_mul]

theorem ppoly_val_ne (x : F) : ∀ L : List (List F × F × F × List F), (∀ p ∈ L, p.2.1 * fval x (fvan p.1) ≠ 0) →
    fval x (rpoly.ppoly L) ≠ 0
  | [], _ => by show (1 : F) * 1 + x * 0 ≠ 0; rw [mul_zero', add_zero', mul_one']; decide
  | (H, c, μ, q) :: L, h => by
    show fval x (fmul (vpoly H c) (rpoly.ppoly L)) ≠ 0
    rw [fval_fmul, fval_vpoly]
    exact mul_ne_zero' (h _ List.mem_cons_self) (ppoly_val_ne x L (fun p hp => h p (List.mem_cons_of_mem _ hp)))

theorem ppoly_valE_ne (z : EF) : ∀ L : List (List F × F × F × List F),
    (∀ p ∈ L, (EF.ofF p.2.1).mul (fvalE z (fvan p.1)) ≠ EF.zero) → fvalE z (rpoly.ppoly L) ≠ EF.zero
  | [], _ => by
    show (EF.ofF 1).add (z.mul EF.zero) ≠ EF.zero
    rw [EF.mul_zero, EF.add_zero]; exact EF.one_ne_zero
  | (H, c, μ, q) :: L, h => by
    show fvalE z (fmul (vpoly H c) (rpoly.ppoly L)) ≠ EF.zero
    rw [fvalE_fmul, fvalE_vpoly]
    exact mulE_ne_zero (h _ List.mem_cons_self) (ppoly_valE_ne z L (fun p hp => h p (List.mem_cons_of_mem _ hp)))

theorem mem_chunksL {p : List F × F × F × List F} : ∀ {cs : List Chunk} {qs : List (List F)},
    p ∈ List.zipWith (fun (ch : Chunk) q => (ch.H, ch.c, ch.m, q)) cs qs → ∃ ch ∈ cs, p.1 = ch.H ∧ p.2.1 = ch.c
  | [], _, hp => nomatch hp
  | _ :: _, [], hp => nomatch hp
  | ch :: cs, q :: qs, hp => by
    rcases List.mem_cons.1 hp with rfl | hp
    · exact ⟨ch, List.mem_cons_self, rfl, rfl⟩
    · obtain ⟨ch', hch, e⟩ := mem_chunksL hp
      exact ⟨ch', List.mem_cons_of_mem _ hch, e⟩

theorem mem_allL {p : List F × F × F × List F} {cs : List Chunk} {Hl : List F} {cl : F} {qs : List (List F)}
    {ql : List F} (hp : p ∈ allL cs Hl cl qs ql) : (∃ ch ∈ cs, p.1 = ch.H ∧ p.2.1 = ch.c) ∨ (p.1 = Hl ∧ p.2.1 = cl) := by
  rcases List.mem_append.1 hp with hp | hp
  · exact Or.inl (mem_chunksL hp)
  · rcases List.mem_singleton.1 hp with rfl
    exact Or.inr ⟨rfl, rfl⟩

theorem inSome_true {x : F} {cs : List Chunk} {ch : Chunk} (hch : ch ∈ cs) (hx : x ∈ ch.H) : inSome x cs = true :=
  List.any_eq_true.2 ⟨ch, hch, decide_eq_true hx⟩

/-- **The targets the honest chunks show**: the quotient's value on every
    domain, and off every domain the quotient over `κ ∏_j v_j`. -/
def qtg (cs : List Chunk) (Hl : List F) (cl : F) (qs : List (List F)) (ql : List F) (κ : F) (Qp : List F) (x : F) : F :=
  if x ∈ Hl ∨ inSome x cs = true then fval x Qp else fval x Qp * finv (κ * fval x (rpoly.ppoly (allL cs Hl cl qs ql)))

def qtgE (ζ : EF) (cs : List Chunk) (Hl : List F) (cl : F) (qs : List (List F)) (ql : List F) (κ : F) (Qp : List F) : EF :=
  (fvalE ζ Qp).mul ((EF.ofF κ).mul (fvalE ζ (rpoly.ppoly (allL cs Hl cl qs ql)))).inv

theorem showsH_of (x : F) (tg : F → F) (Qp : List F) : ∀ (cs : List Chunk) (qs : List (List F)),
    (∀ ch ∈ cs, x ∈ ch.H → tg x = fval x Qp) →
    (∀ p ∈ List.zipWith (fun (ch : Chunk) q => (ch.H, ch.c, ch.m, q)) cs qs, x ∈ p.1 → fval x p.2.2.2 = fval x Qp) →
    ShowsH x tg cs qs
  | [], _, _, _ => trivial
  | _ :: _, [], _, _ => trivial
  | ch :: cs, _ :: qs, ht, hq =>
    ⟨fun hx => (hq _ List.mem_cons_self hx).trans (ht ch List.mem_cons_self hx).symm,
      showsH_of x tg Qp cs qs (fun c hc => ht c (List.mem_cons_of_mem _ hc))
        (fun p hp => hq p (List.mem_cons_of_mem _ hp))⟩

/-- **The honest chunks show the quotient**: when `κ` times the chunks'
    recombination is the quotient `Qp` and each chunk agrees with `Qp` on
    its own domain, the chunks show `qtg` on the query points and `qtgE`
    at `ζ`. -/
theorem shows_of_quot {S : List F} {ζ : EF} (hζ : ∀ x : F, EF.ofF x ≠ ζ) {cs : List Chunk} {Hl : List F} {cl : F}
    {qs : List (List F)} {ql : List F} {κ : F} {Qp : List F} (hc : ∀ ch ∈ cs, ch.c ≠ 0) (hcl : cl ≠ 0) (hκ : κ ≠ 0)
    (hrec : FZero (fcdiff (fcscale κ (rpoly (allL cs Hl cl qs ql))) Qp))
    (hint : ∀ p ∈ allL cs Hl cl qs ql, ∀ x ∈ p.1, fval x p.2.2.2 = fval x Qp) :
    Shows S ζ cs Hl cl qs ql (qtg cs Hl cl qs ql κ Qp) (qtgE ζ cs Hl cl qs ql κ Qp) := by
  have hcne : ∀ p ∈ allL cs Hl cl qs ql, p.2.1 ≠ 0 := fun p hp => by
    rcases mem_allL hp with ⟨ch, hch, _, e⟩ | ⟨_, e⟩
    · rw [e]; exact hc ch hch
    · rw [e]; exact hcl
  refine ⟨fun x _ => ?_, fun x _ hx => ?_, fun x _ hl hs => ?_, ?_⟩
  · refine showsH_of x _ Qp cs qs (fun ch hch hx => if_pos (Or.inr (inSome_true hch hx)))
      (fun p hp hx => hint p (List.mem_append_left _ hp) x hx)
  · rw [qtg, if_pos (Or.inl hx)]
    exact hint (Hl, cl, 1, ql) (List.mem_append_right _ List.mem_cons_self) x hx
  · have hoff : ∀ p ∈ allL cs Hl cl qs ql, p.2.1 * fval x (fvan p.1) ≠ 0 := fun p hp => by
      refine mul_ne_zero' (hcne p hp) (fvan_ne x _ ?_)
      rcases mem_allL hp with ⟨ch, hch, e, _⟩ | ⟨e, _⟩
      · rw [e]; exact inSome_false hs ch hch
      · rw [e]; exact hl
    have hnot : ¬(x ∈ Hl ∨ inSome x cs = true) := fun h => h.elim hl (fun h' => by rw [hs] at h'; nomatch h')
    rw [qtg, if_neg hnot, ← nsum_allL]
    refine qdiv_step _ _ _ _ ?_ (mul_ne_zero' hκ (ppoly_val_ne x _ hoff))
    rw [← rpoly_val x _ hoff, ← fval_fcscale]
    exact sub_eq_zero (by rw [← fval_fcdiff]; exact fval_fzero x _ hrec)
  · have hoff : ∀ p ∈ allL cs Hl cl qs ql, (EF.ofF p.2.1).mul (fvalE ζ (fvan p.1)) ≠ EF.zero := fun p hp =>
      mulE_ne_zero (ofF_ne_zero (hcne p hp)) (fvalE_fvan_ne ζ hζ _)
    rw [qtgE, ← nsumE_allL]
    refine div_stepE _ _ _ _ ?_ (mulE_ne_zero (ofF_ne_zero hκ) (ppoly_valE_ne ζ _ hoff))
    rw [← rpoly_valE ζ _ hoff, ← fvalE_fcscale]
    exact (sub_eq_zero_iff _ _).1 (by rw [← fvalE_fcdiff]; exact fvalE_fzero ζ _ hrec)

/-- **What honest chunks meet**, with the quotient `Qp` and the scale `κ`:
    domains of size `n`, disjoint and without repeats; chunks and `Qp`
    below the degree bound; each chunk equal to `Qp` on its own domain;
    and the selectors normalized (Plonky3's `get_zp_cis`). -/
def QuotOK (cs : List Chunk) (Hl : List F) (cl : F) (qs : List (List F)) (ql : List F) (κ : F) (Qp : List F) : Prop :=
  κ ≠ 0 ∧ ∃ n, (∀ p ∈ allL cs Hl cl qs ql, p.1.length = n ∧ p.2.2.2.length ≤ n) ∧
    Qp.length ≤ (allL cs Hl cl qs ql).length * n ∧ ((allL cs Hl cl qs ql).map (·.1)).flatten.Nodup ∧
    (∀ k j (hk : k < (allL cs Hl cl qs ql).length) (hj : j < (allL cs Hl cl qs ql).length), j ≠ k →
      ∀ x ∈ ((allL cs Hl cl qs ql)[k]'hk).1, x ∉ ((allL cs Hl cl qs ql)[j]'hj).1) ∧
    (∀ p ∈ allL cs Hl cl qs ql, ∀ x ∈ p.1, fval x p.2.2.2 = fval x Qp) ∧
    (∀ k (hk : k < (allL cs Hl cl qs ql).length), ∀ x ∈ ((allL cs Hl cl qs ql)[k]'hk).1,
      κ * ((allL cs Hl cl qs ql)[k]'hk).2.2.1 * opv x (allL cs Hl cl qs ql) k = 1)

/-- **Honest chunks show the quotient**, from `QuotOK`. -/
theorem shows_of_honest {S : List F} {ζ : EF} (hζ : ∀ x : F, EF.ofF x ≠ ζ) {cs : List Chunk} {Hl : List F} {cl : F}
    {qs : List (List F)} {ql : List F} {κ : F} {Qp : List F} (hc : ∀ ch ∈ cs, ch.c ≠ 0) (hcl : cl ≠ 0)
    (h : QuotOK cs Hl cl qs ql κ Qp) :
    Shows S ζ cs Hl cl qs ql (qtg cs Hl cl qs ql κ Qp) (qtgE ζ cs Hl cl qs ql κ Qp) := by
  obtain ⟨hκ, n, hsz, hQ, hnd, hdis, hint, hsel⟩ := h
  exact shows_of_quot hζ hc hcl hκ (rpoly_quot (h := n) κ _ Qp hsz hQ hnd hdis hint hsel) hint

theorem showsH_congr (x : F) {tg tg' : F → F} (e : tg x = tg' x) : ∀ (cs : List Chunk) (qs : List (List F)),
    ShowsH x tg cs qs → ShowsH x tg' cs qs
  | [], _, h => h
  | _ :: _, [], h => h
  | _ :: cs, _ :: qs, ⟨a, b⟩ => ⟨fun hx => (a hx).trans e, showsH_congr x e cs qs b⟩

/-- `Shows` reads the targets only on the query points. -/
theorem shows_congr {S : List F} {ζ : EF} {cs : List Chunk} {Hl : List F} {cl : F} {qs : List (List F)} {ql : List F}
    {tg tg' : F → F} {tζ tζ' : EF} (h : Shows S ζ cs Hl cl qs ql tg tζ) (e : ∀ x ∈ S, tg x = tg' x) (eζ : tζ = tζ') :
    Shows S ζ cs Hl cl qs ql tg' tζ' :=
  ⟨fun x hx => showsH_congr x (e x hx) cs qs (h.1 x hx), fun x hx hl => (h.2.1 x hx hl).trans (e x hx),
    fun x hx hl hs => (h.2.2.1 x hx hl hs).trans (e x hx), h.2.2.2.trans eζ⟩

/-- **`RecOK` from honest chunks**: when every column's chunks are honest
    for some quotient and the targets are that quotient's (`qtg` on the
    query points, `qtgE` at `ζ`), the chunk data meet `RecOK`. -/
theorem recOK_of_honest (JS : CSet → F → F) (JE : CSet → EF) :
    ∀ (csets : List CSet) (ds : List (List (List F) × List F)), csets.length = ds.length → (∀ c ∈ csets, c.OK) →
    (∀ p ∈ csets.zip ds, p.2.1.length = p.1.cs.length ∧ ∃ κ Qp, QuotOK p.1.cs p.1.Hl p.1.cl p.2.1 p.2.2 κ Qp ∧
      (∀ x ∈ p.1.S, qtg p.1.cs p.1.Hl p.1.cl p.2.1 p.2.2 κ Qp x = JS p.1 x) ∧
      qtgE p.1.ζ p.1.cs p.1.Hl p.1.cl p.2.1 p.2.2 κ Qp = JE p.1) →
    RecOK csets ds JS JE
  | [], [], _, _, _ => trivial
  | c :: cs, d :: ds, hl, hok, h => by
    obtain ⟨hlen, κ, Qp, hq, eS, eζ⟩ := h (c, d) List.mem_cons_self
    obtain ⟨hζ, _, _, hc, hcl⟩ := hok c List.mem_cons_self
    exact ⟨⟨hlen, shows_congr (shows_of_honest hζ (fun ch hch => (hc ch hch).1) hcl hq) eS eζ⟩,
      recOK_of_honest JS JE cs ds (Nat.succ.inj hl) (fun c' hc' => hok c' (List.mem_cons_of_mem _ hc'))
        (fun p hp => h p (List.mem_cons_of_mem _ hp))⟩
  | [], _ :: _, hl, _, _ => nomatch hl
  | _ :: _, [], hl, _, _ => nomatch hl

end Circuit
