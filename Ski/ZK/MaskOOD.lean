import Ski.ZK.Mask

/-!
# Random rows hide the out-of-domain openings too

The verifier also opens each committed column at out-of-domain points of
the extension, `ζ` and its next-row companion: a value in `EF`, four
coordinates over `F`.  **`mask_hides_ood`** extends `mask_hides` to them:
the values at `S` (in `F`) and at `Z` (in `EF`, none in `F`) have one
distribution for every trace when `|S| + 4 |Z| ≤ n`.

The shift `D` must now vanish at each `ζ ∈ Z` with coefficients in `F`, so
it carries a degree-4 `F`-polynomial `mF ζ` that vanishes at `ζ`.  With
`u = w^2`, `ζ · conj ζ` lies in `F(u)` (`EF.mul_conj`), so
`(X - ζ)(X - conj ζ) = X^2 - A X + B` has coefficients in `F(u)`, and its
product with its conjugate under `u ↦ -u` has coefficients in `F`
(`mF_factor`).  At `x ∈ F` the product is zero only if a factor is, since
`EF` is a field (`EF.mul_eq_zero`).  There the second factor is the
first's image under `u ↦ -u`, so either vanishing makes the first vanish,
and the first is `(x - ζ)(x - conj ζ)`, zero only if `ζ` or `conj ζ` is
`x` (`mF_ne`).  Neither lies in `F` when `ζ` does not.
-/

namespace Circuit

open ZKF

-- ---------------------------------------------------------------------------
-- Polynomials over `F` at points of `EF`
-- ---------------------------------------------------------------------------

/-- A polynomial over `F` at a point of `EF`. -/
def fvalE (z : EF) (cs : List F) : EF := cval z (cs.map EF.ofF)

theorem map_fcadd : ∀ p q : List F, (fcadd p q).map EF.ofF = cadd (p.map EF.ofF) (q.map EF.ofF)
  | [], q => rfl
  | a :: p, [] => rfl
  | a :: p, b :: q => by
    show EF.ofF (a + b) :: (fcadd p q).map EF.ofF = (EF.ofF a).add (EF.ofF b) :: cadd (p.map EF.ofF) (q.map EF.ofF)
    rw [EF.ofF_add, map_fcadd p q]

theorem fvalE_fcadd (z : EF) (p q : List F) : fvalE z (fcadd p q) = (fvalE z p).add (fvalE z q) := by
  unfold fvalE; rw [map_fcadd, cval_cadd]

theorem fvalE_fcscale (z : EF) (c : F) (p : List F) : fvalE z (fcscale c p) = (EF.ofF c).mul (fvalE z p) := by
  unfold fvalE fcscale
  rw [List.map_map, show (EF.ofF ∘ (c * ·)) = fun a => (EF.ofF c).mul (EF.ofF a) from
    funext fun a => (EF.ofF_mul c a).symm, ← cval_cscale]
  unfold cscale
  rw [List.map_map]
  rfl

theorem fvalE_cons (z : EF) (c : F) (cs : List F) : fvalE z (c :: cs) = (EF.ofF c).add (z.mul (fvalE z cs)) := rfl

theorem fvalE_fzero (z : EF) (cs : List F) (h : FZero cs) : fvalE z cs = EF.zero :=
  cval_allZero z _ (fun c hc => by
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hc
    rw [h a ha]; rfl)

theorem fvalE_fcdiff (z : EF) (p q : List F) : fvalE z (fcdiff p q) = (fvalE z p).sub (fvalE z q) := by
  unfold fcdiff
  rw [fvalE_fcadd, fvalE_fcscale]
  exact Q.eq_of_norm (p := (Q.var 0).add ((⟨.neg (k 1), k 0, k 0, k 0⟩ : Q).mul (Q.var 1)))
    (q := (Q.var 0).sub (Q.var 1)) (by decide) (env3 (fvalE z p) (fvalE z q) EF.zero)

/-- `ofF` carries values at points of `F`. -/
theorem ofF_fval (x : F) : ∀ cs : List F, EF.ofF (fval x cs) = fvalE (EF.ofF x) cs
  | [] => rfl
  | c :: cs => by
    show EF.ofF (c + x * fval x cs) = (EF.ofF c).add ((EF.ofF x).mul (fvalE (EF.ofF x) cs))
    rw [← ofF_fval x cs, EF.ofF_mul, EF.ofF_add]

/-- The product of two polynomials. -/
def fmul : List F → List F → List F
  | [], _ => []
  | a :: p, q => fcadd (fcscale a q) (0 :: fmul p q)

theorem fval_fmul (x : F) : ∀ p q : List F, fval x (fmul p q) = fval x p * fval x q
  | [], q => by show (0 : F) = 0 * fval x q; rw [zero_mul']
  | a :: p, q => by
    show fval x (fcadd (fcscale a q) (0 :: fmul p q)) = (a + x * fval x p) * fval x q
    rw [fval_fcadd, fval_fcscale]
    show a * fval x q + (0 + x * fval x (fmul p q)) = _
    rw [fval_fmul x p q]
    exact fid (e := v 0 * v 1 + (k 0 + v 2 * (v 3 * v 1))) (e' := (v 0 + v 2 * v 3) * v 1) (by decide)
      [a, fval x q, x, fval x p]

theorem fvalE_fmul (z : EF) : ∀ p q : List F, fvalE z (fmul p q) = (fvalE z p).mul (fvalE z q)
  | [], q => by show EF.zero = EF.zero.mul (fvalE z q); rw [EF.zero_mul]
  | a :: p, q => by
    show fvalE z (fcadd (fcscale a q) (0 :: fmul p q)) = ((EF.ofF a).add (z.mul (fvalE z p))).mul (fvalE z q)
    rw [fvalE_fcadd, fvalE_fcscale, fvalE_cons, fvalE_fmul z p q]
    exact Q.eq_of_norm
      (p := ((Q.var 0).mul (Q.var 1)).add ((⟨k 0, k 0, k 0, k 0⟩ : Q).add ((Q.var 2).mul ((Q.var 3).mul (Q.var 1)))))
      (q := ((Q.var 0).add ((Q.var 2).mul (Q.var 3))).mul (Q.var 1))
      (by decide) (env4 (EF.ofF a) (fvalE z q) z (fvalE z p))

theorem fmul_length : ∀ (p q : List F), q ≠ [] → (fmul p q).length ≤ p.length + q.length - 1
  | [], _, _ => Nat.zero_le _
  | a :: p, q, hq => by
    have h1 := fcadd_length (fcscale a q) (0 :: fmul p q)
    rw [fcscale_length] at h1
    have h2 := fmul_length p q hq
    have h3 : 0 < q.length := List.length_pos_iff.2 hq
    show (fcadd _ _).length ≤ p.length + 1 + q.length - 1
    refine Nat.le_trans h1 (Nat.max_le.2 ⟨by omega, ?_⟩)
    simp only [List.length_cons]
    omega

theorem fcadd_ne_nil (p : List F) {q : List F} (hq : q ≠ []) : fcadd p q ≠ [] := by
  rcases p with _ | ⟨a, p⟩ <;> rcases q with _ | ⟨b, q⟩
  · exact absurd rfl hq
  · exact List.cons_ne_nil _ _
  · exact absurd rfl hq
  · exact List.cons_ne_nil _ _

theorem fcadd_ne_nil_left {p : List F} (hp : p ≠ []) (q : List F) : fcadd p q ≠ [] := by
  rcases p with _ | ⟨a, p⟩ <;> rcases q with _ | ⟨b, q⟩
  · exact absurd rfl hp
  · exact List.cons_ne_nil _ _
  · exact List.cons_ne_nil _ _
  · exact List.cons_ne_nil _ _

theorem fmul_ne_nil : ∀ (p q : List F), p ≠ [] → fmul p q ≠ []
  | [], _, h => absurd rfl h
  | _ :: _, _, _ => fcadd_ne_nil _ (List.cons_ne_nil _ _)

theorem fvan_ne_nil : ∀ xs : List F, fvan xs ≠ []
  | [] => List.cons_ne_nil _ _
  | _ :: _ => fcadd_ne_nil_left (List.cons_ne_nil _ _) _

-- ---------------------------------------------------------------------------
-- A polynomial over `F` vanishing at a point of `EF`
-- ---------------------------------------------------------------------------

theorem mul_d2 (p q r s : F) :
    (⟨p, 0, q, 0⟩ : EF).mul ⟨r, 0, s, 0⟩ = ⟨p * r + W11 * (q * s), 0, p * s + q * r, 0⟩ :=
  Q.eq_of_norm (p := Q.mul ⟨v 0, k 0, v 1, k 0⟩ ⟨v 2, k 0, v 3, k 0⟩)
    (q := ⟨v 0 * v 2 + k W11 * (v 1 * v 3), k 0, v 0 * v 3 + v 1 * v 2, k 0⟩) (by decide) (env3 ⟨p, q, r, s⟩ EF.zero EF.zero)

/-- A degree-4 polynomial over `F` vanishing at `ζ`, coefficients lowest
    first; `ζ`'s minimal polynomial when `[F(ζ):F] = 4`, its square when
    `ζ ∈ F(u)`:
    `(X^2 - A X + B)(X^2 - Ā X + B̄)` with `A = ζ + conj ζ = a + b u`,
    `B = ζ conj ζ = c0 + c1 u`, and `Ā`, `B̄` their images under `u ↦ -u`. -/
def mF (z : EF) : List F :=
  [z.c0 * z.c0 + W11 * (z.c1 * -z.c1),
   -(((z.x0 + z.x0) * z.c0 + W11 * ((z.x2 + z.x2) * -z.c1)) + ((z.x0 + z.x0) * z.c0 + W11 * (-(z.x2 + z.x2) * z.c1))),
   ((z.x0 + z.x0) * (z.x0 + z.x0) + W11 * ((z.x2 + z.x2) * -(z.x2 + z.x2))) + (z.c0 + z.c0),
   -((z.x0 + z.x0) + (z.x0 + z.x0)),
   1]

theorem mF_length (z : EF) : (mF z).length = 5 := rfl

section
variable (z : EF)

/-- `A = ζ + conj ζ`. -/
def mA : EF := ⟨z.x0 + z.x0, 0, z.x2 + z.x2, 0⟩
def mAb : EF := ⟨z.x0 + z.x0, 0, -(z.x2 + z.x2), 0⟩
def mB : EF := ⟨z.c0, 0, z.c1, 0⟩
def mBb : EF := ⟨z.c0, 0, -z.c1, 0⟩

theorem mA_eq : mA z = z.add (EF.conj z) := by
  apply EF.ext
  · rfl
  · show (0 : F) = z.x1 + -z.x1
    exact fid (e := k 0) (e' := v 0 + -(v 0)) (by decide) [z.x1]
  · rfl
  · show (0 : F) = z.x3 + -z.x3
    exact fid (e := k 0) (e' := v 0 + -(v 0)) (by decide) [z.x3]

theorem mB_eq : mB z = z.mul (EF.conj z) := (EF.mul_conj z).symm

/-- The product of two polynomials over `EF`. -/
def emul : List EF → List EF → List EF
  | [], _ => []
  | a :: p, q => cadd (cscale a q) (EF.zero :: emul p q)

theorem cval_emul (x : EF) : ∀ p q : List EF, cval x (emul p q) = (cval x p).mul (cval x q)
  | [], q => by show EF.zero = EF.zero.mul (cval x q); rw [EF.zero_mul]
  | a :: p, q => by
    show cval x (cadd (cscale a q) (EF.zero :: emul p q)) = (a.add (x.mul (cval x p))).mul (cval x q)
    rw [cval_cadd, cval_cscale]
    show (a.mul (cval x q)).add (EF.zero.add (x.mul (cval x (emul p q)))) = _
    rw [cval_emul x p q]
    exact Q.eq_of_norm
      (p := ((Q.var 0).mul (Q.var 1)).add ((⟨k 0, k 0, k 0, k 0⟩ : Q).add ((Q.var 2).mul ((Q.var 3).mul (Q.var 1)))))
      (q := ((Q.var 0).add ((Q.var 2).mul (Q.var 3))).mul (Q.var 1))
      (by decide) (env4 a (cval x q) x (cval x p))

/-- The coefficients: the product of the two quadratics. -/
theorem mF_map : (mF z).map EF.ofF = emul [mB z, (mA z).neg, EF.one] [mBb z, (mAb z).neg, EF.one] := by
  unfold mF
  simp only [emul, cscale, List.map, cadd, List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact Q.eq_of_norm (p := ⟨v 2 * v 2 + k W11 * (v 3 * .neg (v 3)), k 0, k 0, k 0⟩)
      (q := ((Q.mk (v 2) (k 0) (v 3) (k 0)).mul ⟨v 2, k 0, .neg (v 3), k 0⟩).add ⟨k 0, k 0, k 0, k 0⟩) (by decide)
      (env3 ⟨z.x0 + z.x0, z.x2 + z.x2, z.c0, z.c1⟩ EF.zero EF.zero)
  · exact Q.eq_of_norm (p := ⟨.neg ((v 0 * v 2 + k W11 * (v 1 * .neg (v 3))) + (v 0 * v 2 + k W11 * (.neg (v 1) * v 3))),
        k 0, k 0, k 0⟩)
      (q := ((Q.mk (v 2) (k 0) (v 3) (k 0)).mul (Q.neg ⟨v 0, k 0, .neg (v 1), k 0⟩)).add
        (((Q.neg ⟨v 0, k 0, v 1, k 0⟩).mul ⟨v 2, k 0, .neg (v 3), k 0⟩).add ⟨k 0, k 0, k 0, k 0⟩)) (by decide)
      (env3 ⟨z.x0 + z.x0, z.x2 + z.x2, z.c0, z.c1⟩ EF.zero EF.zero)
  · exact Q.eq_of_norm (p := ⟨(v 0 * v 0 + k W11 * (v 1 * .neg (v 1))) + (v 2 + v 2), k 0, k 0, k 0⟩)
      (q := ((Q.mk (v 2) (k 0) (v 3) (k 0)).mul ⟨k 1, k 0, k 0, k 0⟩).add
        (((Q.neg ⟨v 0, k 0, v 1, k 0⟩).mul (Q.neg ⟨v 0, k 0, .neg (v 1), k 0⟩)).add
          (((Q.mk (k 1) (k 0) (k 0) (k 0)).mul ⟨v 2, k 0, .neg (v 3), k 0⟩).add ⟨k 0, k 0, k 0, k 0⟩))) (by decide)
      (env3 ⟨z.x0 + z.x0, z.x2 + z.x2, z.c0, z.c1⟩ EF.zero EF.zero)
  · exact Q.eq_of_norm (p := ⟨.neg (v 0 + v 0), k 0, k 0, k 0⟩)
      (q := ((Q.neg ⟨v 0, k 0, v 1, k 0⟩).mul ⟨k 1, k 0, k 0, k 0⟩).add
        ((Q.mk (k 1) (k 0) (k 0) (k 0)).mul (Q.neg ⟨v 0, k 0, .neg (v 1), k 0⟩))) (by decide)
      (env3 ⟨z.x0 + z.x0, z.x2 + z.x2, z.c0, z.c1⟩ EF.zero EF.zero)
  · exact Q.eq_of_norm (p := ⟨k 1, k 0, k 0, k 0⟩)
      (q := (Q.mk (k 1) (k 0) (k 0) (k 0)).mul ⟨k 1, k 0, k 0, k 0⟩) (by decide) (env3 EF.zero EF.zero EF.zero)

/-- The value: the product of the two quadratics' values. -/
theorem mF_factor (x : EF) : cval x ((mF z).map EF.ofF) =
    (cval x [mB z, (mA z).neg, EF.one]).mul (cval x [mBb z, (mAb z).neg, EF.one]) := by
  rw [mF_map, cval_emul]

/-- The first quadratic is `(x - ζ)(x - conj ζ)`. -/
theorem mF_quad (x : EF) : cval x [mB z, (mA z).neg, EF.one] = (x.sub z).mul (x.sub (EF.conj z)) := by
  rw [mA_eq, mB_eq]
  show (z.mul (EF.conj z)).add (x.mul (((z.add (EF.conj z)).neg).add (x.mul (EF.one.add (x.mul EF.zero))))) = _
  exact Q.eq_of_norm
    (p := ((Q.var 1).mul (Q.var 2)).add ((Q.var 0).mul ((((Q.var 1).add (Q.var 2)).neg).add
      ((Q.var 0).mul ((⟨k 1, k 0, k 0, k 0⟩ : Q).add ((Q.var 0).mul ⟨k 0, k 0, k 0, k 0⟩))))))
    (q := ((Q.var 0).sub (Q.var 1)).mul ((Q.var 0).sub (Q.var 2))) (by decide) (env3 x z (EF.conj z))

/-- **`ζ` is a root of `mF ζ`.** -/
theorem mF_root : fvalE z (mF z) = EF.zero := by
  unfold fvalE
  rw [mF_factor, mF_quad, EF.sub_self, EF.zero_mul, EF.zero_mul]

/-- The two quadratics at `x ∈ F`, in coordinates. -/
theorem mF_first (x : F) : cval (EF.ofF x) [mB z, (mA z).neg, EF.one] =
    ⟨x * x - (z.x0 + z.x0) * x + z.c0, 0, z.c1 - (z.x2 + z.x2) * x, 0⟩ :=
  Q.eq_of_norm
    (p := (Q.mk (v 3) (k 0) (v 4) (k 0)).add ((Q.mk (v 0) (k 0) (k 0) (k 0)).mul
      ((Q.neg ⟨v 1, k 0, v 2, k 0⟩).add ((Q.mk (v 0) (k 0) (k 0) (k 0)).mul ((⟨k 1, k 0, k 0, k 0⟩ : Q).add
        ((Q.mk (v 0) (k 0) (k 0) (k 0)).mul ⟨k 0, k 0, k 0, k 0⟩))))))
    (q := ⟨v 0 * v 0 - v 1 * v 0 + v 3, k 0, v 4 - v 2 * v 0, k 0⟩) (by decide)
    (env3 ⟨x, z.x0 + z.x0, z.x2 + z.x2, z.c0⟩ ⟨z.c1, 0, 0, 0⟩ EF.zero)

theorem mF_second (x : F) : cval (EF.ofF x) [mBb z, (mAb z).neg, EF.one] =
    ⟨x * x - (z.x0 + z.x0) * x + z.c0, 0, -(z.c1 - (z.x2 + z.x2) * x), 0⟩ :=
  Q.eq_of_norm
    (p := (Q.mk (v 3) (k 0) (.neg (v 4)) (k 0)).add ((Q.mk (v 0) (k 0) (k 0) (k 0)).mul
      ((Q.neg ⟨v 1, k 0, .neg (v 2), k 0⟩).add ((Q.mk (v 0) (k 0) (k 0) (k 0)).mul ((⟨k 1, k 0, k 0, k 0⟩ : Q).add
        ((Q.mk (v 0) (k 0) (k 0) (k 0)).mul ⟨k 0, k 0, k 0, k 0⟩))))))
    (q := ⟨v 0 * v 0 - v 1 * v 0 + v 3, k 0, .neg (v 4 - v 2 * v 0), k 0⟩) (by decide)
    (env3 ⟨x, z.x0 + z.x0, z.x2 + z.x2, z.c0⟩ ⟨z.c1, 0, 0, 0⟩ EF.zero)

theorem conj_ofF (x : F) : EF.conj (EF.ofF x) = EF.ofF x :=
  EF.ext rfl (fid (e := -(k 0)) (e' := k 0) (by decide) []) rfl (fid (e := -(k 0)) (e' := k 0) (by decide) [])

theorem conj_conj (x : EF) : EF.conj (EF.conj x) = x :=
  EF.ext rfl (fid (e := -(-(v 0))) (e' := v 0) (by decide) [x.x1]) rfl (fid (e := -(-(v 0))) (e' := v 0) (by decide) [x.x3])

/-- **`mF ζ` has no root in `F`**, `ζ` outside `F`. -/
theorem mF_ne (hz : ∀ x : F, EF.ofF x ≠ z) (x : F) : fval x (mF z) ≠ 0 := by
  intro h0
  have e := ofF_fval x (mF z)
  rw [h0] at e
  unfold fvalE at e
  rw [mF_factor] at e
  -- the first quadratic vanishes
  have hfirst : cval (EF.ofF x) [mB z, (mA z).neg, EF.one] = EF.zero := by
    rcases EF.mul_eq_zero e.symm with h | h
    · exact h
    · rw [mF_second] at h
      have h0 := congrArg EF.x0 h
      have h2 := congrArg EF.x2 h
      rw [mF_first]
      refine EF.ext h0 rfl ?_ rfl
      show z.c1 - (z.x2 + z.x2) * x = 0
      have : -(z.c1 - (z.x2 + z.x2) * x) = 0 := h2
      have e2 : z.c1 - (z.x2 + z.x2) * x = -(-(z.c1 - (z.x2 + z.x2) * x)) :=
        fid (e := v 0) (e' := -(-(v 0))) (by decide) [z.c1 - (z.x2 + z.x2) * x]
      rw [e2, this]
      decide
  rw [mF_quad] at hfirst
  rcases EF.mul_eq_zero hfirst with h | h
  · exact hz x ((sub_eq_zero_iff _ _).1 h)
  · have := (sub_eq_zero_iff _ _).1 h
    apply hz x
    rw [← conj_conj z, ← this, conj_ofF]

end

/-- The product of the points' `mF`. -/
def mZ : List EF → List F
  | [] => [1]
  | z :: Z => fmul (mF z) (mZ Z)

theorem mZ_ne_nil : ∀ Z : List EF, mZ Z ≠ []
  | [] => List.cons_ne_nil _ _
  | _ :: _ => fmul_ne_nil _ _ (List.cons_ne_nil _ _)

theorem mZ_length : ∀ Z : List EF, (mZ Z).length ≤ 4 * Z.length + 1
  | [] => Nat.le_refl 1
  | z :: Z => by
    have := fmul_length (mF z) (mZ Z) (mZ_ne_nil Z)
    have := mZ_length Z
    rw [mF_length] at *
    show (fmul (mF z) (mZ Z)).length ≤ 4 * (Z.length + 1) + 1
    omega

theorem mZ_root (z : EF) : ∀ Z : List EF, z ∈ Z → fvalE z (mZ Z) = EF.zero
  | [], h => nomatch h
  | z' :: Z, h => by
    show fvalE z (fmul (mF z') (mZ Z)) = EF.zero
    rw [fvalE_fmul]
    rcases List.mem_cons.1 h with rfl | h
    · rw [mF_root, EF.zero_mul]
    · rw [mZ_root z Z h, EF.mul_zero]

theorem mZ_ne (x : F) : ∀ Z : List EF, (∀ z ∈ Z, ∀ y : F, EF.ofF y ≠ z) → fval x (mZ Z) ≠ 0
  | [], _ => by rw [show mZ [] = [1] from rfl, fval_one]; decide
  | z :: Z, h => by
    show fval x (fmul (mF z) (mZ Z)) ≠ 0
    rw [fval_fmul]
    intro e
    rcases mul_eq_zero e with e | e
    · exact mF_ne z (h z List.mem_cons_self) x e
    · exact mZ_ne x Z (fun z' hz' => h z' (List.mem_cons_of_mem _ hz')) e

theorem finterp_ne_nil : ∀ pts : List (F × F), pts ≠ [] → finterp pts ≠ []
  | [], h => absurd rfl h
  | (x, y) :: r, _ => fcadd_ne_nil _ (by unfold fcscale; rw [Ne, List.map_eq_nil_iff]; exact fvan_ne_nil _)

-- ---------------------------------------------------------------------------
-- The theorem
-- ---------------------------------------------------------------------------

section
variable {T R S : List F} {Z : List EF} {n : Nat} (hT : T.length = n) (hR : R.length = n) (hTR : (T ++ R).Nodup)
  (hTS : ∀ x ∈ T, x ∉ S) (hZ : ∀ z ∈ Z, ∀ x : F, EF.ofF x ≠ z) (hn : S.length + 4 * Z.length ≤ n)
include hT hR hTR hTS hZ hn

/-- **Random rows hide a column's openings, out of domain too**: the values
    at the opened points `S` of `F` and `Z` of `EF` (none in `F`) take every
    value pair equally often over the random rows, whatever the trace, when
    `|S| + 4 |Z| ≤ n`. -/
theorem mask_hides_ood (t t' : List F) (ht : t.length = n) (ht' : t'.length = n) (E : List F → List EF → Bool) :
    vsum n (fun r => if E (mopen T R S t r) (Z.map (fun z => fvalE z (mcol T R t r))) then 1 else 0) =
      vsum n (fun r => if E (mopen T R S t' r) (Z.map (fun z => fvalE z (mcol T R t' r))) then 1 else 0) := by
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · rw [List.length_eq_zero_iff.1 ht, List.length_eq_zero_iff.1 ht']
  have hTnd : T.Nodup := (List.nodup_append.1 hTR).1
  -- the factor vanishing at `S` and `Z`
  obtain ⟨M, hM⟩ : ∃ M, M = fmul (fvan S) (mZ Z) := ⟨_, rfl⟩
  have hMl : M.length ≤ S.length + 4 * Z.length + 1 := by
    have h1 := fmul_length (fvan S) (mZ Z) (mZ_ne_nil Z)
    have h2 := fvan_length S
    have h3 := mZ_length Z
    rw [hM]; omega
  have hMT : ∀ x ∈ T, fval x M ≠ 0 := by
    intro x hx
    rw [hM, fval_fmul]
    intro e
    rcases mul_eq_zero e with e | e
    · exact fvan_ne x S (hTS x hx) e
    · exact mZ_ne x Z hZ e
  have hMS : ∀ s ∈ S, fval s M = 0 := fun s hs => by rw [hM, fval_fmul, fvan_root s S hs, zero_mul']
  have hMZ : ∀ z ∈ Z, fvalE z M = EF.zero := fun z hz => by rw [hM, fvalE_fmul, mZ_root z Z hz, EF.mul_zero]
  -- the shift: `M` times the interpolant of `(t' - t) / M` on `T`
  have hvl : (vsub t' t).length = n := by rw [vsub_length, ht, ht', Nat.min_self]
  obtain ⟨Qp, hQp⟩ : ∃ Qp : List (F × F), Qp = (T.zip (vsub t' t)).map (fun p => (p.1, p.2 * finv (fval p.1 M))) :=
    ⟨_, rfl⟩
  have hQnd : (Qp.map Prod.fst).Nodup := by
    rw [hQp, List.map_map, show (Prod.fst ∘ fun p : F × F => (p.1, p.2 * finv (fval p.1 M))) = Prod.fst from rfl,
      map_fst_zip' (by rw [hT, hvl])]
    exact hTnd
  obtain ⟨Qc, hQc⟩ : ∃ Qc, Qc = finterp Qp := ⟨_, rfl⟩
  have hQpl : Qp.length = n := by rw [hQp, List.length_map, List.length_zip, hT, hvl, Nat.min_self]
  have hQl : Qc.length ≤ n := by
    have := finterp_length Qp
    rw [hQc]; omega
  have hQne : Qc ≠ [] := by
    rw [hQc]
    refine finterp_ne_nil _ ?_
    rw [hQp, Ne, List.map_eq_nil_iff, ← List.length_eq_zero_iff, List.length_zip, hT, hvl, Nat.min_self]
    omega
  obtain ⟨D, hD⟩ : ∃ D, D = fmul M Qc := ⟨_, rfl⟩
  have hDl : D.length ≤ n + n := by
    have := fmul_length M Qc hQne
    rw [hD]; omega
  have hDT : ∀ i (hiT : i < T.length) (hit : i < t.length) (hit' : i < t'.length),
      fval (T[i]'hiT) D = t'[i]'hit' - t[i]'hit := by
    intro i hiT hit hit'
    have hiv : i < (vsub t' t).length := by rw [hvl]; rw [hT] at hiT; exact hiT
    have hmem0 : (T[i]'hiT, (t'[i]'hit' - t[i]'hit) * finv (fval (T[i]'hiT) M)) ∈
        (T.zip (vsub t' t)).map (fun p => (p.1, p.2 * finv (fval p.1 M))) := by
      refine List.mem_map.2 ⟨(T[i]'hiT, (vsub t' t)[i]'hiv), zip_mem hiT (by rw [hT, hvl]), ?_⟩
      show (_, (vsub t' t)[i] * _) = _
      unfold vsub; rw [List.getElem_zipWith]
    have hmem : (T[i]'hiT, (t'[i]'hit' - t[i]'hit) * finv (fval (T[i]'hiT) M)) ∈ Qp := by
      rw [hQp]; exact hmem0
    rw [hD, fval_fmul, hQc, finterp_eval _ hQnd _ hmem]
    show fval T[i] M * ((t'[i] - t[i]) * finv (fval T[i] M)) = _
    rw [mul_comm' (t'[i] - t[i]), ← mul_assoc', mul_finv (hMT _ (List.getElem_mem _)), one_mul']
  have hDS : ∀ s ∈ S, fval s D = 0 := fun s hs => by rw [hD, fval_fmul, hMS s hs, zero_mul']
  have hDZ : ∀ z ∈ Z, fvalE z D = EF.zero := fun z hz => by rw [hD, fvalE_fmul, hMZ z hz, EF.zero_mul]
  obtain ⟨c, hcD⟩ : ∃ c, c = R.map (fun x => fval x D) := ⟨_, rfl⟩
  have hc : c.length = n := by rw [hcD, List.length_map, hR]
  -- the shifted randomness opens as the original
  have key : ∀ r : List F, r.length = n →
      FZero (fcdiff (mcol T R t' (vadd r c)) (fcadd (mcol T R t r) D)) := by
    intro r hr
    have hrc : (vadd r c).length = n := by rw [vadd_length, hr, hc, Nat.min_self]
    have hnd : ((T.zip t' ++ R.zip (vadd r c)).map Prod.fst).Nodup := by
      rw [List.map_append, map_fst_zip' (by rw [hT, ht']), map_fst_zip' (by rw [hR, hrc])]; exact hTR
    have hnd0 : ((T.zip t ++ R.zip r).map Prod.fst).Nodup := by
      rw [List.map_append, map_fst_zip' (by rw [hT, ht]), map_fst_zip' (by rw [hR, hr])]; exact hTR
    have hpl : (mcol T R t' (vadd r c)).length ≤ n + n := by
      have := finterp_length (T.zip t' ++ R.zip (vadd r c))
      simp only [List.length_append, List.length_zip, hT, ht', hR, hrc, Nat.min_self] at this
      exact this
    have hql : (fcadd (mcol T R t r) D).length ≤ n + n := by
      have h1 := fcadd_length (mcol T R t r) D
      have h2 := finterp_length (T.zip t ++ R.zip r)
      simp only [List.length_append, List.length_zip, hT, ht, hR, hr, Nat.min_self] at h2
      exact Nat.le_trans h1 (Nat.max_le.2 ⟨h2, hDl⟩)
    refine fagree_zero hpl hql (T ++ R) hTR (by rw [List.length_append, hT, hR]) (fun x hx => ?_)
    rw [fval_fcadd]
    rcases List.mem_append.1 hx with hx | hx
    · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
      have hi' : i < n := by omega
      unfold mcol
      rw [finterp_eval _ hnd _ (List.mem_append_left _ (zip_mem (V := t') hi (by rw [hT, ht']))),
        finterp_eval _ hnd0 _ (List.mem_append_left _ (zip_mem (V := t) hi (by rw [hT, ht]))),
        hDT i hi (by omega) (by omega)]
      exact fid (e := v 0) (e' := v 1 + (v 0 - v 1)) (by decide) [t'[i]'(by omega), t[i]'(by omega)]
    · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
      unfold mcol
      rw [finterp_eval _ hnd _ (List.mem_append_right _ (zip_mem (V := vadd r c) hi (by rw [hR, hrc]))),
        finterp_eval _ hnd0 _ (List.mem_append_right _ (zip_mem (V := r) hi (by rw [hR, hr])))]
      show (vadd r c)[i] = _
      unfold vadd
      rw [List.getElem_zipWith]
      show _ + c[i] = _
      simp only [hcD, List.getElem_map]
  have keyS : ∀ r : List F, r.length = n → mopen T R S t' (vadd r c) = mopen T R S t r := by
    intro r hr
    unfold mopen
    refine List.map_congr_left (fun s hs => ?_)
    have := fval_fzero s _ (key r hr)
    rw [fval_fcdiff, fval_fcadd, hDS s hs, add_zero'] at this
    exact sub_eq_zero this
  have keyZ : ∀ r : List F, r.length = n →
      Z.map (fun z => fvalE z (mcol T R t' (vadd r c))) = Z.map (fun z => fvalE z (mcol T R t r)) := by
    intro r hr
    refine List.map_congr_left (fun z hz => ?_)
    have := fvalE_fzero z _ (key r hr)
    rw [fvalE_fcdiff, fvalE_fcadd, hDZ z hz, EF.add_zero] at this
    exact (sub_eq_zero_iff _ _).1 this
  -- count
  rw [← vsum_shift n c hc (fun r => if E (mopen T R S t' r) (Z.map (fun z => fvalE z (mcol T R t' r))) then 1 else 0)]
  exact vsum_congr n (fun r hr => by
    show (if E (mopen T R S t r) (Z.map (fun z => fvalE z (mcol T R t r))) = true then 1 else 0) =
      (if E (mopen T R S t' (vadd r c)) (Z.map (fun z => fvalE z (mcol T R t' (vadd r c)))) = true then 1 else 0)
    rw [keyS r hr, keyZ r hr])

/-- The openings of several columns, each with its own `n` random values,
    the randomness concatenated. -/
def openAll (T R S : List F) (Z : List EF) (n : Nat) : List (List F) → List F → List (List F × List EF)
  | [], _ => []
  | t :: ts, rs => (mopen T R S t (rs.take n), Z.map (fun z => fvalE z (mcol T R t (rs.take n)))) ::
      openAll T R S Z n ts (rs.drop n)

include hT hR hTR hTS hZ hn in
/-- **Random rows hide many columns' openings at once**: columns with fixed
    contents and independent random rows -- a trace's, and LogUp's
    permutation trace, which Plonky3 computes from the unrandomized trace --
    open with one joint distribution whatever their contents. -/
theorem masks_hide : ∀ (ts ts' : List (List F)), ts.length = ts'.length → (∀ t ∈ ts, t.length = n) →
    (∀ t ∈ ts', t.length = n) → ∀ E : List (List F × List EF) → Bool,
    vsum (ts.length * n) (fun rs => if E (openAll T R S Z n ts rs) then 1 else 0) =
      vsum (ts.length * n) (fun rs => if E (openAll T R S Z n ts' rs) then 1 else 0)
  | [], [], _, _, _, _ => rfl
  | [], _ :: _, h, _, _, _ => nomatch h
  | _ :: _, [], h, _, _, _ => nomatch h
  | t :: ts, t' :: ts', hl, h1, h2, E => by
    have hl' : ts.length = ts'.length := by simp only [List.length_cons] at hl; omega
    have hm : (ts.length + 1) * n = n + ts.length * n := by rw [Nat.succ_mul, Nat.add_comm]
    have hm' : (ts.length + 1) * n = n + ts'.length * n := by rw [hm, hl']
    have ht : t.length = n := h1 t List.mem_cons_self
    have ht' : t'.length = n := h2 t' List.mem_cons_self
    let o : List F → List F → List F × List EF := fun t x => (mopen T R S t x, Z.map (fun z => fvalE z (mcol T R t x)))
    have split : ∀ (u : List F) (us : List (List F)) (x y : List F), x.length = n →
        openAll T R S Z n (u :: us) (x ++ y) = o u x :: openAll T R S Z n us y := by
      intro u us x y hx
      show (mopen T R S u ((x ++ y).take n), Z.map (fun z => fvalE z (mcol T R u ((x ++ y).take n)))) ::
        openAll T R S Z n us ((x ++ y).drop n) = _
      rw [List.take_left' hx, List.drop_left' hx]
    show vsum ((ts.length + 1) * n) _ = vsum ((ts.length + 1) * n) _
    rw [hm, vsum_append, show n + ts.length * n = n + ts'.length * n by rw [hl'], vsum_append]
    calc vsum n (fun x => vsum (ts.length * n) (fun y => if E (openAll T R S Z n (t :: ts) (x ++ y)) then 1 else 0))
        = vsum n (fun x => vsum (ts.length * n) (fun y => if E (o t x :: openAll T R S Z n ts y) then 1 else 0)) :=
          vsum_congr n (fun x hx => vsum_congr _ (fun y _ => by rw [split t ts x y hx]))
      _ = vsum n (fun x => vsum (ts.length * n) (fun y => if E (o t x :: openAll T R S Z n ts' y) then 1 else 0)) :=
          vsum_congr n (fun x _ => masks_hide ts ts' hl' (fun u hu => h1 u (List.mem_cons_of_mem _ hu))
            (fun u hu => h2 u (List.mem_cons_of_mem _ hu)) (fun L => E (o t x :: L)))
      _ = vsum (ts.length * n) (fun y => vsum n (fun x => if E (o t x :: openAll T R S Z n ts' y) then 1 else 0)) :=
          vsum_comm _ n _
      _ = vsum (ts.length * n) (fun y => vsum n (fun x => if E (o t' x :: openAll T R S Z n ts' y) then 1 else 0)) :=
          vsum_congr _ (fun y _ => mask_hides_ood hT hR hTR hTS hZ hn t t' ht ht'
            (fun a b => E ((a, b) :: openAll T R S Z n ts' y)))
      _ = vsum n (fun x => vsum (ts.length * n) (fun y => if E (o t' x :: openAll T R S Z n ts' y) then 1 else 0)) :=
          (vsum_comm _ n _).symm
      _ = vsum n (fun x => vsum (ts'.length * n) (fun y => if E (openAll T R S Z n (t' :: ts') (x ++ y)) then 1 else 0)) := by
          rw [← hl']
          exact vsum_congr n (fun x hx => vsum_congr _ (fun y _ => by rw [split t' ts' x y hx]))

end

end Circuit
