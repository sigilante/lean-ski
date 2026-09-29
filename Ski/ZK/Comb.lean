import Ski.ZK.Ext

/-!
# The LogUp combiner is a bijection, for a generic challenge

Plonky3 fingerprints a 4-tuple `a` as `a0 β^3 + a1 β^2 + a2 β + a3`
(`p3_lookup`'s Horner combiner).  That is `F`-linear in `a`, through the
4 × 4 matrix of the coordinates of `β^3, β^2, β, 1` (`combMat`).  When its
determinant is not zero (`Generic β`), the combiner is a bijection from
`F^4` onto the extension, with the adjugate as inverse (`comb_inv`,
`inv_comb`).  The adjugate identities are polynomial identities, decided on
normal forms.
-/

namespace Circuit

open ZKF


/-- The determinant of a 4 × 4 matrix of variables, row `i` column `j` at `4 i + j`. -/
def det4E : E := ((((((((((((((((((((((((v 0 * v 5 * v 10 * v 15) - (v 0 * v 5 * v 11 * v 14)) - (v 0 * v 6 * v 9 * v 15)) + (v 0 * v 6 * v 11 * v 13)) + (v 0 * v 7 * v 9 * v 14)) - (v 0 * v 7 * v 10 * v 13)) - (v 1 * v 4 * v 10 * v 15)) + (v 1 * v 4 * v 11 * v 14)) + (v 1 * v 6 * v 8 * v 15)) - (v 1 * v 6 * v 11 * v 12)) - (v 1 * v 7 * v 8 * v 14)) + (v 1 * v 7 * v 10 * v 12)) + (v 2 * v 4 * v 9 * v 15)) - (v 2 * v 4 * v 11 * v 13)) - (v 2 * v 5 * v 8 * v 15)) + (v 2 * v 5 * v 11 * v 12)) + (v 2 * v 7 * v 8 * v 13)) - (v 2 * v 7 * v 9 * v 12)) - (v 3 * v 4 * v 9 * v 14)) + (v 3 * v 4 * v 10 * v 13)) + (v 3 * v 5 * v 8 * v 14)) - (v 3 * v 5 * v 10 * v 12)) - (v 3 * v 6 * v 8 * v 13)) + (v 3 * v 6 * v 9 * v 12))

/-- The adjugate: `adj i j` is the `(j, i)` cofactor. -/
def adj4E : Nat → Nat → E
  | 0, 0 => ((((((v 5 * v 10 * v 15) - (v 5 * v 11 * v 14)) - (v 6 * v 9 * v 15)) + (v 6 * v 11 * v 13)) + (v 7 * v 9 * v 14)) - (v 7 * v 10 * v 13))
  | 0, 1 => (- ((((((v 1 * v 10 * v 15) - (v 1 * v 11 * v 14)) - (v 2 * v 9 * v 15)) + (v 2 * v 11 * v 13)) + (v 3 * v 9 * v 14)) - (v 3 * v 10 * v 13)))
  | 0, 2 => ((((((v 1 * v 6 * v 15) - (v 1 * v 7 * v 14)) - (v 2 * v 5 * v 15)) + (v 2 * v 7 * v 13)) + (v 3 * v 5 * v 14)) - (v 3 * v 6 * v 13))
  | 0, 3 => (- ((((((v 1 * v 6 * v 11) - (v 1 * v 7 * v 10)) - (v 2 * v 5 * v 11)) + (v 2 * v 7 * v 9)) + (v 3 * v 5 * v 10)) - (v 3 * v 6 * v 9)))
  | 1, 0 => (- ((((((v 4 * v 10 * v 15) - (v 4 * v 11 * v 14)) - (v 6 * v 8 * v 15)) + (v 6 * v 11 * v 12)) + (v 7 * v 8 * v 14)) - (v 7 * v 10 * v 12)))
  | 1, 1 => ((((((v 0 * v 10 * v 15) - (v 0 * v 11 * v 14)) - (v 2 * v 8 * v 15)) + (v 2 * v 11 * v 12)) + (v 3 * v 8 * v 14)) - (v 3 * v 10 * v 12))
  | 1, 2 => (- ((((((v 0 * v 6 * v 15) - (v 0 * v 7 * v 14)) - (v 2 * v 4 * v 15)) + (v 2 * v 7 * v 12)) + (v 3 * v 4 * v 14)) - (v 3 * v 6 * v 12)))
  | 1, 3 => ((((((v 0 * v 6 * v 11) - (v 0 * v 7 * v 10)) - (v 2 * v 4 * v 11)) + (v 2 * v 7 * v 8)) + (v 3 * v 4 * v 10)) - (v 3 * v 6 * v 8))
  | 2, 0 => ((((((v 4 * v 9 * v 15) - (v 4 * v 11 * v 13)) - (v 5 * v 8 * v 15)) + (v 5 * v 11 * v 12)) + (v 7 * v 8 * v 13)) - (v 7 * v 9 * v 12))
  | 2, 1 => (- ((((((v 0 * v 9 * v 15) - (v 0 * v 11 * v 13)) - (v 1 * v 8 * v 15)) + (v 1 * v 11 * v 12)) + (v 3 * v 8 * v 13)) - (v 3 * v 9 * v 12)))
  | 2, 2 => ((((((v 0 * v 5 * v 15) - (v 0 * v 7 * v 13)) - (v 1 * v 4 * v 15)) + (v 1 * v 7 * v 12)) + (v 3 * v 4 * v 13)) - (v 3 * v 5 * v 12))
  | 2, 3 => (- ((((((v 0 * v 5 * v 11) - (v 0 * v 7 * v 9)) - (v 1 * v 4 * v 11)) + (v 1 * v 7 * v 8)) + (v 3 * v 4 * v 9)) - (v 3 * v 5 * v 8)))
  | 3, 0 => (- ((((((v 4 * v 9 * v 14) - (v 4 * v 10 * v 13)) - (v 5 * v 8 * v 14)) + (v 5 * v 10 * v 12)) + (v 6 * v 8 * v 13)) - (v 6 * v 9 * v 12)))
  | 3, 1 => ((((((v 0 * v 9 * v 14) - (v 0 * v 10 * v 13)) - (v 1 * v 8 * v 14)) + (v 1 * v 10 * v 12)) + (v 2 * v 8 * v 13)) - (v 2 * v 9 * v 12))
  | 3, 2 => (- ((((((v 0 * v 5 * v 14) - (v 0 * v 6 * v 13)) - (v 1 * v 4 * v 14)) + (v 1 * v 6 * v 12)) + (v 2 * v 4 * v 13)) - (v 2 * v 5 * v 12)))
  | 3, 3 => ((((((v 0 * v 5 * v 10) - (v 0 * v 6 * v 9)) - (v 1 * v 4 * v 10)) + (v 1 * v 6 * v 8)) + (v 2 * v 4 * v 9)) - (v 2 * v 5 * v 8))
  | _, _ => k 0

theorem adj_right0 (l : List F) : (((((v 0 * (v 20 * ((((adj4E 0 0 * v 16) + (adj4E 0 1 * v 17)) + (adj4E 0 2 * v 18)) + (adj4E 0 3 * v 19)))) + (v 1 * (v 20 * ((((adj4E 1 0 * v 16) + (adj4E 1 1 * v 17)) + (adj4E 1 2 * v 18)) + (adj4E 1 3 * v 19))))) + (v 2 * (v 20 * ((((adj4E 2 0 * v 16) + (adj4E 2 1 * v 17)) + (adj4E 2 2 * v 18)) + (adj4E 2 3 * v 19))))) + (v 3 * (v 20 * ((((adj4E 3 0 * v 16) + (adj4E 3 1 * v 17)) + (adj4E 3 2 * v 18)) + (adj4E 3 3 * v 19)))))).eval (atL l) = ((v 20 * det4E * v 16)).eval (atL l) :=
  fid (by decide) l

theorem adj_left0 (l : List F) : ((v 20 * ((((adj4E 0 0 * ((((v 0 * v 16) + (v 1 * v 17)) + (v 2 * v 18)) + (v 3 * v 19))) + (adj4E 0 1 * ((((v 4 * v 16) + (v 5 * v 17)) + (v 6 * v 18)) + (v 7 * v 19)))) + (adj4E 0 2 * ((((v 8 * v 16) + (v 9 * v 17)) + (v 10 * v 18)) + (v 11 * v 19)))) + (adj4E 0 3 * ((((v 12 * v 16) + (v 13 * v 17)) + (v 14 * v 18)) + (v 15 * v 19)))))).eval (atL l) = ((v 20 * det4E * v 16)).eval (atL l) :=
  fid (by decide) l

theorem adj_right1 (l : List F) : (((((v 4 * (v 20 * ((((adj4E 0 0 * v 16) + (adj4E 0 1 * v 17)) + (adj4E 0 2 * v 18)) + (adj4E 0 3 * v 19)))) + (v 5 * (v 20 * ((((adj4E 1 0 * v 16) + (adj4E 1 1 * v 17)) + (adj4E 1 2 * v 18)) + (adj4E 1 3 * v 19))))) + (v 6 * (v 20 * ((((adj4E 2 0 * v 16) + (adj4E 2 1 * v 17)) + (adj4E 2 2 * v 18)) + (adj4E 2 3 * v 19))))) + (v 7 * (v 20 * ((((adj4E 3 0 * v 16) + (adj4E 3 1 * v 17)) + (adj4E 3 2 * v 18)) + (adj4E 3 3 * v 19)))))).eval (atL l) = ((v 20 * det4E * v 17)).eval (atL l) :=
  fid (by decide) l

theorem adj_left1 (l : List F) : ((v 20 * ((((adj4E 1 0 * ((((v 0 * v 16) + (v 1 * v 17)) + (v 2 * v 18)) + (v 3 * v 19))) + (adj4E 1 1 * ((((v 4 * v 16) + (v 5 * v 17)) + (v 6 * v 18)) + (v 7 * v 19)))) + (adj4E 1 2 * ((((v 8 * v 16) + (v 9 * v 17)) + (v 10 * v 18)) + (v 11 * v 19)))) + (adj4E 1 3 * ((((v 12 * v 16) + (v 13 * v 17)) + (v 14 * v 18)) + (v 15 * v 19)))))).eval (atL l) = ((v 20 * det4E * v 17)).eval (atL l) :=
  fid (by decide) l

theorem adj_right2 (l : List F) : (((((v 8 * (v 20 * ((((adj4E 0 0 * v 16) + (adj4E 0 1 * v 17)) + (adj4E 0 2 * v 18)) + (adj4E 0 3 * v 19)))) + (v 9 * (v 20 * ((((adj4E 1 0 * v 16) + (adj4E 1 1 * v 17)) + (adj4E 1 2 * v 18)) + (adj4E 1 3 * v 19))))) + (v 10 * (v 20 * ((((adj4E 2 0 * v 16) + (adj4E 2 1 * v 17)) + (adj4E 2 2 * v 18)) + (adj4E 2 3 * v 19))))) + (v 11 * (v 20 * ((((adj4E 3 0 * v 16) + (adj4E 3 1 * v 17)) + (adj4E 3 2 * v 18)) + (adj4E 3 3 * v 19)))))).eval (atL l) = ((v 20 * det4E * v 18)).eval (atL l) :=
  fid (by decide) l

theorem adj_left2 (l : List F) : ((v 20 * ((((adj4E 2 0 * ((((v 0 * v 16) + (v 1 * v 17)) + (v 2 * v 18)) + (v 3 * v 19))) + (adj4E 2 1 * ((((v 4 * v 16) + (v 5 * v 17)) + (v 6 * v 18)) + (v 7 * v 19)))) + (adj4E 2 2 * ((((v 8 * v 16) + (v 9 * v 17)) + (v 10 * v 18)) + (v 11 * v 19)))) + (adj4E 2 3 * ((((v 12 * v 16) + (v 13 * v 17)) + (v 14 * v 18)) + (v 15 * v 19)))))).eval (atL l) = ((v 20 * det4E * v 18)).eval (atL l) :=
  fid (by decide) l

theorem adj_right3 (l : List F) : (((((v 12 * (v 20 * ((((adj4E 0 0 * v 16) + (adj4E 0 1 * v 17)) + (adj4E 0 2 * v 18)) + (adj4E 0 3 * v 19)))) + (v 13 * (v 20 * ((((adj4E 1 0 * v 16) + (adj4E 1 1 * v 17)) + (adj4E 1 2 * v 18)) + (adj4E 1 3 * v 19))))) + (v 14 * (v 20 * ((((adj4E 2 0 * v 16) + (adj4E 2 1 * v 17)) + (adj4E 2 2 * v 18)) + (adj4E 2 3 * v 19))))) + (v 15 * (v 20 * ((((adj4E 3 0 * v 16) + (adj4E 3 1 * v 17)) + (adj4E 3 2 * v 18)) + (adj4E 3 3 * v 19)))))).eval (atL l) = ((v 20 * det4E * v 19)).eval (atL l) :=
  fid (by decide) l

theorem adj_left3 (l : List F) : ((v 20 * ((((adj4E 3 0 * ((((v 0 * v 16) + (v 1 * v 17)) + (v 2 * v 18)) + (v 3 * v 19))) + (adj4E 3 1 * ((((v 4 * v 16) + (v 5 * v 17)) + (v 6 * v 18)) + (v 7 * v 19)))) + (adj4E 3 2 * ((((v 8 * v 16) + (v 9 * v 17)) + (v 10 * v 18)) + (v 11 * v 19)))) + (adj4E 3 3 * ((((v 12 * v 16) + (v 13 * v 17)) + (v 14 * v 18)) + (v 15 * v 19)))))).eval (atL l) = ((v 20 * det4E * v 19)).eval (atL l) :=
  fid (by decide) l

/-- A tuple of four field elements: a blinding message's payload. -/
structure Tup where
  t0 : F
  t1 : F
  t2 : F
  t3 : F
  deriving DecidableEq

theorem Tup.ext {a b : Tup} (h0 : a.t0 = b.t0) (h1 : a.t1 = b.t1) (h2 : a.t2 = b.t2) (h3 : a.t3 = b.t3) : a = b := by
  cases a; cases b; simp only at h0 h1 h2 h3; subst h0 h1 h2 h3; rfl

/-- A 4 × 4 matrix over `F`, by rows. -/
structure Mat4 where
  a00 : F
  a01 : F
  a02 : F
  a03 : F
  a10 : F
  a11 : F
  a12 : F
  a13 : F
  a20 : F
  a21 : F
  a22 : F
  a23 : F
  a30 : F
  a31 : F
  a32 : F
  a33 : F

namespace Mat4

/-- The entries, a vector and a scalar, as leaves `0 … 20`. -/
def l (M : Mat4) (t : EF) (f : F) : List F := [M.a00, M.a01, M.a02, M.a03, M.a10, M.a11, M.a12, M.a13, M.a20, M.a21, M.a22, M.a23, M.a30, M.a31, M.a32, M.a33, t.x0, t.x1, t.x2, t.x3, f]

def det (M : Mat4) : F := det4E.eval (atL (M.l EF.zero 0))

def adj (M : Mat4) (i j : Nat) : F := (adj4E i j).eval (atL (M.l EF.zero 0))

/-- `M a`, into the extension's coordinates. -/
def mulT (M : Mat4) (a : Tup) : EF :=
  ⟨M.a00 * a.t0 + M.a01 * a.t1 + M.a02 * a.t2 + M.a03 * a.t3,
   M.a10 * a.t0 + M.a11 * a.t1 + M.a12 * a.t2 + M.a13 * a.t3,
   M.a20 * a.t0 + M.a21 * a.t1 + M.a22 * a.t2 + M.a23 * a.t3,
   M.a30 * a.t0 + M.a31 * a.t1 + M.a32 * a.t2 + M.a33 * a.t3⟩

/-- `f · adj(M) t`. -/
def inv (M : Mat4) (f : F) (t : EF) : Tup :=
  ⟨f * (M.adj 0 0 * t.x0 + M.adj 0 1 * t.x1 + M.adj 0 2 * t.x2 + M.adj 0 3 * t.x3),
   f * (M.adj 1 0 * t.x0 + M.adj 1 1 * t.x1 + M.adj 1 2 * t.x2 + M.adj 1 3 * t.x3),
   f * (M.adj 2 0 * t.x0 + M.adj 2 1 * t.x1 + M.adj 2 2 * t.x2 + M.adj 2 3 * t.x3),
   f * (M.adj 3 0 * t.x0 + M.adj 3 1 * t.x1 + M.adj 3 2 * t.x2 + M.adj 3 3 * t.x3)⟩

theorem mulT_inv (M : Mat4) (f : F) (t : EF) :
    M.mulT (M.inv f t) = ⟨f * M.det * t.x0, f * M.det * t.x1, f * M.det * t.x2, f * M.det * t.x3⟩ := by
  apply EF.ext
  · exact adj_right0 (M.l t f)
  · exact adj_right1 (M.l t f)
  · exact adj_right2 (M.l t f)
  · exact adj_right3 (M.l t f)

theorem inv_mulT (M : Mat4) (f : F) (a : Tup) :
    M.inv f (M.mulT a) = ⟨f * M.det * a.t0, f * M.det * a.t1, f * M.det * a.t2, f * M.det * a.t3⟩ := by
  apply Tup.ext
  · exact adj_left0 (M.l ⟨a.t0, a.t1, a.t2, a.t3⟩ f)
  · exact adj_left1 (M.l ⟨a.t0, a.t1, a.t2, a.t3⟩ f)
  · exact adj_left2 (M.l ⟨a.t0, a.t1, a.t2, a.t3⟩ f)
  · exact adj_left3 (M.l ⟨a.t0, a.t1, a.t2, a.t3⟩ f)

end Mat4

end Circuit

namespace Circuit

open ZKF

/-- `β^k`, for the combiner's powers. -/
def bpow (β : EF) : Nat → EF
  | 0 => EF.one
  | k + 1 => (bpow β k).mul β

/-- **The combiner's matrix**: column `j` is the coordinates of `β^(3 - j)`. -/
def combMat (β : EF) : Mat4 :=
  ⟨(bpow β 3).x0, (bpow β 2).x0, (bpow β 1).x0, (bpow β 0).x0,
   (bpow β 3).x1, (bpow β 2).x1, (bpow β 1).x1, (bpow β 0).x1,
   (bpow β 3).x2, (bpow β 2).x2, (bpow β 1).x2, (bpow β 0).x2,
   (bpow β 3).x3, (bpow β 2).x3, (bpow β 1).x3, (bpow β 0).x3⟩

/-- **Plonky3's fingerprint of a 4-tuple**, by Horner's rule:
    `((a0 β + a1) β + a2) β + a3`. -/
def horner (β : EF) (a : Tup) : EF :=
  (((((EF.ofF a.t0).mul β).add (EF.ofF a.t1)).mul β).add (EF.ofF a.t2)).mul β |>.add (EF.ofF a.t3)

/-- A symbolic base-field element. -/
def Q.base (e : E) : Q := ⟨e, k 0, k 0, k 0⟩

theorem horner_eq (β : EF) (a : Tup) : horner β a = (combMat β).mulT a := by
  let b : Q := Q.var 0
  let P0 : Q := ⟨k 1, k 0, k 0, k 0⟩
  let P1 : Q := P0.mul b
  let P2 : Q := P1.mul b
  let P3 : Q := P2.mul b
  let x : Nat → E := fun j => .atom (.main 0 (4 + j))
  exact Q.eq_of_norm
    (p := (((((Q.base (x 0)).mul b).add (Q.base (x 1))).mul b).add (Q.base (x 2))).mul b |>.add (Q.base (x 3)))
    (q := ⟨P3.q0 * x 0 + P2.q0 * x 1 + P1.q0 * x 2 + P0.q0 * x 3,
           P3.q1 * x 0 + P2.q1 * x 1 + P1.q1 * x 2 + P0.q1 * x 3,
           P3.q2 * x 0 + P2.q2 * x 1 + P1.q2 * x 2 + P0.q2 * x 3,
           P3.q3 * x 0 + P2.q3 * x 1 + P1.q3 * x 2 + P0.q3 * x 3⟩)
    (by decide) (env3 β ⟨a.t0, a.t1, a.t2, a.t3⟩ EF.zero)

/-- **A generic combiner challenge**: its matrix is invertible.  Exactly
    the `β` outside the quadratic subfield are (`generic_iff`,
    `Ski/ZK/Generic.lean`): all but `P^2` of the `P^4`. -/
def Generic (β : EF) : Prop := (combMat β).det ≠ 0

/-- The combiner's inverse. -/
def combInv (β : EF) (t : EF) : Tup := (combMat β).inv (finv (combMat β).det) t

theorem f_one_mul (a : F) : 1 * a = a := fid (e := k 1 * v 0) (e' := v 0) (by decide) [a]

theorem horner_combInv {β : EF} (hg : Generic β) (t : EF) : horner β (combInv β t) = t := by
  rw [horner_eq]
  unfold combInv
  rw [Mat4.mulT_inv, finv_mul hg]
  apply EF.ext <;> exact f_one_mul _

theorem combInv_horner {β : EF} (hg : Generic β) (a : Tup) : combInv β (horner β a) = a := by
  rw [horner_eq]
  unfold combInv
  rw [Mat4.inv_mulT, finv_mul hg]
  apply Tup.ext <;> exact f_one_mul _

-- ---------------------------------------------------------------------------
-- A blinding message's LogUp term
-- ---------------------------------------------------------------------------

/-- **A blinding message's term**: `1 / (prefix - fingerprint(a))`, with the
    inverse zero at zero. -/
def blindTerm (β pre : EF) (a : Tup) : EF := (pre.sub (horner β a)).inv

/-- The tuple that gives a term. -/
def blindPre (β pre : EF) (u : EF) : Tup := combInv β (pre.sub u.inv)

theorem sub_sub_cancel (p t : EF) : p.sub (p.sub t) = t :=
  Q.eq_of_norm (p := (Q.var 0).sub ((Q.var 0).sub (Q.var 1))) (q := Q.var 1) (by decide) (env3 p t EF.zero)

/-- **For a generic `β`, a blinding tuple's term is a bijection** from
    tuples onto the extension: every term comes from exactly one tuple. -/
theorem blindTerm_pre {β : EF} (hg : Generic β) (pre u : EF) : blindTerm β pre (blindPre β pre u) = u := by
  unfold blindTerm blindPre
  rw [horner_combInv hg, sub_sub_cancel, EF.inv_inv]

theorem blindPre_term {β : EF} (hg : Generic β) (pre : EF) (a : Tup) : blindPre β pre (blindTerm β pre a) = a := by
  unfold blindTerm blindPre
  rw [EF.inv_inv, sub_sub_cancel, combInv_horner hg]

end Circuit
