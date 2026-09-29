import Ski.ZK.Fermat

/-!
# BabyBear's quartic extension

Plonky3 draws its LogUp challenges from `BinomialExtensionField<BabyBear, 4>`:
`F[x] / (x^4 - 11)`, an element `x0 + x1 x + x2 x^2 + x3 x^3` (`EF`).  Its
ring laws hold because each component is a polynomial identity over `F`,
decided on normal forms (`Q.eq_of_norm`).  It is a field: a nonzero element
has a nonzero norm to `F` (`EF.norm_ne_zero`), because `11` is not a
square (`nonsquare_11`), so it has an inverse (`EF.mul_inv`).
-/

namespace Circuit

/-- An element of the quartic extension, by its coordinates. -/
structure EF where
  x0 : F
  x1 : F
  x2 : F
  x3 : F
  deriving DecidableEq

/-- The extension's `W`: `x^4 = 11`. -/
def W11 : F := ofN 11

namespace EF

def zero : EF := ⟨0, 0, 0, 0⟩
def one : EF := ⟨1, 0, 0, 0⟩
def ofF (a : F) : EF := ⟨a, 0, 0, 0⟩
def add (x y : EF) : EF := ⟨x.x0 + y.x0, x.x1 + y.x1, x.x2 + y.x2, x.x3 + y.x3⟩
def neg (x : EF) : EF := ⟨-x.x0, -x.x1, -x.x2, -x.x3⟩
def sub (x y : EF) : EF := ⟨x.x0 - y.x0, x.x1 - y.x1, x.x2 - y.x2, x.x3 - y.x3⟩
def mul (x y : EF) : EF :=
  ⟨x.x0 * y.x0 + W11 * (x.x1 * y.x3 + x.x2 * y.x2 + x.x3 * y.x1),
   x.x0 * y.x1 + x.x1 * y.x0 + W11 * (x.x2 * y.x3 + x.x3 * y.x2),
   x.x0 * y.x2 + x.x1 * y.x1 + x.x2 * y.x0 + W11 * (x.x3 * y.x3),
   x.x0 * y.x3 + x.x1 * y.x2 + x.x2 * y.x1 + x.x3 * y.x0⟩

theorem ext {x y : EF} (h0 : x.x0 = y.x0) (h1 : x.x1 = y.x1) (h2 : x.x2 = y.x2) (h3 : x.x3 = y.x3) : x = y := by
  cases x; cases y; simp only at h0 h1 h2 h3; subst h0 h1 h2 h3; rfl

end EF

-- ---------------------------------------------------------------------------
-- Identities by normal forms
-- ---------------------------------------------------------------------------

/-- An extension element as four expressions. -/
structure Q where
  q0 : E
  q1 : E
  q2 : E
  q3 : E

namespace Q

def eval (ρ : Atom → F) (p : Q) : EF := ⟨p.q0.eval ρ, p.q1.eval ρ, p.q2.eval ρ, p.q3.eval ρ⟩

def add (p q : Q) : Q := ⟨.add p.q0 q.q0, .add p.q1 q.q1, .add p.q2 q.q2, .add p.q3 q.q3⟩
def sub (p q : Q) : Q := ⟨.sub p.q0 q.q0, .sub p.q1 q.q1, .sub p.q2 q.q2, .sub p.q3 q.q3⟩
def neg (p : Q) : Q := ⟨.neg p.q0, .neg p.q1, .neg p.q2, .neg p.q3⟩
def mul (p q : Q) : Q :=
  let w := E.const W11
  ⟨.add (.mul p.q0 q.q0) (.mul w (.add (.add (.mul p.q1 q.q3) (.mul p.q2 q.q2)) (.mul p.q3 q.q1))),
   .add (.add (.mul p.q0 q.q1) (.mul p.q1 q.q0)) (.mul w (.add (.mul p.q2 q.q3) (.mul p.q3 q.q2))),
   .add (.add (.add (.mul p.q0 q.q2) (.mul p.q1 q.q1)) (.mul p.q2 q.q0)) (.mul w (.mul p.q3 q.q3)),
   .add (.add (.add (.mul p.q0 q.q3) (.mul p.q1 q.q2)) (.mul p.q2 q.q1)) (.mul p.q3 q.q0)⟩

theorem eval_add (ρ : Atom → F) (p q : Q) : (p.add q).eval ρ = (p.eval ρ).add (q.eval ρ) := rfl
theorem eval_sub (ρ : Atom → F) (p q : Q) : (p.sub q).eval ρ = (p.eval ρ).sub (q.eval ρ) := rfl
theorem eval_neg (ρ : Atom → F) (p : Q) : p.neg.eval ρ = (p.eval ρ).neg := rfl
theorem eval_mul (ρ : Atom → F) (p q : Q) : (p.mul q).eval ρ = (p.eval ρ).mul (q.eval ρ) := rfl

/-- Two symbolic elements with the same normal forms mean the same. -/
theorem eq_of_norm {p q : Q}
    (h : p.q0.norm = q.q0.norm ∧ p.q1.norm = q.q1.norm ∧ p.q2.norm = q.q2.norm ∧ p.q3.norm = q.q3.norm)
    (ρ : Atom → F) : p.eval ρ = q.eval ρ :=
  EF.ext (E.eval_eq_of_norm h.1 ρ) (E.eval_eq_of_norm h.2.1 ρ) (E.eval_eq_of_norm h.2.2.1 ρ)
    (E.eval_eq_of_norm h.2.2.2 ρ)

/-- The `j`-th variable element. -/
def var (j : Nat) : Q :=
  ⟨.atom (.main 0 (4 * j)), .atom (.main 0 (4 * j + 1)), .atom (.main 0 (4 * j + 2)), .atom (.main 0 (4 * j + 3))⟩

end Q

/-- Three extension elements as leaf values. -/
def env3 (x y z : EF) : Atom → F
  | .main 0 0 => x.x0 | .main 0 1 => x.x1 | .main 0 2 => x.x2 | .main 0 3 => x.x3
  | .main 0 4 => y.x0 | .main 0 5 => y.x1 | .main 0 6 => y.x2 | .main 0 7 => y.x3
  | .main 0 8 => z.x0 | .main 0 9 => z.x1 | .main 0 10 => z.x2 | .main 0 11 => z.x3
  | _ => 0

theorem var0 (x y z : EF) : (Q.var 0).eval (env3 x y z) = x := rfl
theorem var1 (x y z : EF) : (Q.var 1).eval (env3 x y z) = y := rfl
theorem var2 (x y z : EF) : (Q.var 2).eval (env3 x y z) = z := rfl

namespace EF

theorem mul_comm (x y : EF) : x.mul y = y.mul x :=
  Q.eq_of_norm (p := (Q.var 0).mul (Q.var 1)) (q := (Q.var 1).mul (Q.var 0)) (by decide) (env3 x y zero)

theorem mul_assoc (x y z : EF) : (x.mul y).mul z = x.mul (y.mul z) :=
  Q.eq_of_norm (p := ((Q.var 0).mul (Q.var 1)).mul (Q.var 2)) (q := (Q.var 0).mul ((Q.var 1).mul (Q.var 2)))
    (by decide) (env3 x y z)

theorem add_comm (x y : EF) : x.add y = y.add x :=
  Q.eq_of_norm (p := (Q.var 0).add (Q.var 1)) (q := (Q.var 1).add (Q.var 0)) (by decide) (env3 x y zero)

theorem add_assoc (x y z : EF) : (x.add y).add z = x.add (y.add z) :=
  Q.eq_of_norm (p := ((Q.var 0).add (Q.var 1)).add (Q.var 2)) (q := (Q.var 0).add ((Q.var 1).add (Q.var 2)))
    (by decide) (env3 x y z)

theorem mul_add (x y z : EF) : x.mul (y.add z) = (x.mul y).add (x.mul z) :=
  Q.eq_of_norm (p := (Q.var 0).mul ((Q.var 1).add (Q.var 2)))
    (q := ((Q.var 0).mul (Q.var 1)).add ((Q.var 0).mul (Q.var 2))) (by decide) (env3 x y z)

theorem sub_eq_add_neg (x y : EF) : x.sub y = x.add y.neg :=
  Q.eq_of_norm (p := (Q.var 0).sub (Q.var 1)) (q := (Q.var 0).add (Q.var 1).neg) (by decide) (env3 x y zero)

theorem add_neg_cancel (x y : EF) : (x.add y).sub y = x :=
  Q.eq_of_norm (p := ((Q.var 0).add (Q.var 1)).sub (Q.var 1)) (q := Q.var 0) (by decide) (env3 x y zero)

theorem sub_add_cancel (x y : EF) : (x.sub y).add y = x :=
  Q.eq_of_norm (p := ((Q.var 0).sub (Q.var 1)).add (Q.var 1)) (q := Q.var 0) (by decide) (env3 x y zero)

theorem add_zero (x : EF) : x.add zero = x := by
  apply ext <;> exact add_zero' _

theorem zero_add (x : EF) : zero.add x = x := by
  apply ext <;> exact zero_add' _

theorem mul_one (x : EF) : x.mul one = x :=
  Q.eq_of_norm (p := (Q.var 0).mul ⟨.const 1, .const 0, .const 0, .const 0⟩) (q := Q.var 0) (by decide)
    (env3 x zero zero)

theorem mul_zero (x : EF) : x.mul zero = zero :=
  Q.eq_of_norm (p := (Q.var 0).mul ⟨.const 0, .const 0, .const 0, .const 0⟩)
    (q := ⟨.const 0, .const 0, .const 0, .const 0⟩) (by decide) (env3 x zero zero)

theorem zero_mul (x : EF) : zero.mul x = zero := by rw [mul_comm, mul_zero]

theorem sub_self (x : EF) : x.sub x = zero := by
  apply ext <;> exact sub_self' _

end EF

-- ---------------------------------------------------------------------------
-- Identities in F, by normal forms
-- ---------------------------------------------------------------------------

namespace ZKF

instance : Add E := ⟨E.add⟩
instance : Sub E := ⟨E.sub⟩
instance : Mul E := ⟨E.mul⟩
instance : Neg E := ⟨E.neg⟩

/-- Variable `i`. -/
def v (i : Nat) : E := .atom (.main 0 i)
def k (c : F) : E := .const c

/-- A list of values, as leaves. -/
def atL (l : List F) : Atom → F
  | .main 0 i => l.getD i 0
  | _ => 0

theorem fid {e e' : E} (h : e.norm = e'.norm) (l : List F) : e.eval (atL l) = e'.eval (atL l) :=
  E.eval_eq_of_norm h _

end ZKF

open ZKF in
/-- Inverses in BabyBear, by Fermat. -/
def finv (x : F) : F := fpow x (P - 2)

theorem finv_mul {x : F} (hx : x ≠ 0) : finv x * x = 1 := by
  have h := fermat_unit hx
  rw [show P - 1 = (P - 2) + 1 by decide, fpow] at h
  exact h

theorem fmul_comm (a b : F) : a * b = b * a :=
  ZKF.fid (e := ZKF.v 0 * ZKF.v 1) (e' := ZKF.v 1 * ZKF.v 0) (by decide) [a, b]

theorem mul_finv {x : F} (hx : x ≠ 0) : x * finv x = 1 := by
  rw [fmul_comm]; exact finv_mul hx

open ZKF in
theorem sq_scale (u a w : F) :
    u * a * (u * a) = (u * u - W11 * (w * w)) * (a * a) + W11 * ((w * a) * (w * a)) :=
  fid (e := v 0 * v 1 * (v 0 * v 1)) (e' := (v 0 * v 0 - k W11 * (v 2 * v 2)) * (v 1 * v 1) + k W11 * ((v 2 * v 1) * (v 2 * v 1)))
    (by decide) [u, a, w]

open ZKF in
theorem sqn_scale (u a w : F) :
    u * a * (u * a) = (u * u + W11 * (w * w)) * (a * a) - W11 * ((w * a) * (w * a)) :=
  fid (e := v 0 * v 1 * (v 0 * v 1)) (e' := (v 0 * v 0 + k W11 * (v 2 * v 2)) * (v 1 * v 1) - k W11 * ((v 2 * v 1) * (v 2 * v 1)))
    (by decide) [u, a, w]

open ZKF in
theorem zmul_w (a : F) : 0 * a + W11 * (1 * 1) = ofN 11 :=
  fid (e := k 0 * v 0 + k W11 * (k 1 * k 1)) (e' := k W11) (by decide) [a]

open ZKF in
theorem zmul_nw (a : F) : 0 * a - W11 * (1 * 1) = -W11 :=
  fid (e := k 0 * v 0 - k W11 * (k 1 * k 1)) (e' := - k W11) (by decide) [a]

open ZKF in
/-- `u² - 11 v² = 0` only at zero. -/
theorem sq11_zero {u w : F} (h : u * u - W11 * (w * w) = 0) : u = 0 ∧ w = 0 := by
  rcases (inferInstance : Decidable (w = 0)) with hw | hw
  · -- `(u / w)² = 11`
    exfalso
    apply nonsquare_11 (u * finv w)
    have e := sq_scale u (finv w) w
    rw [e, h, mul_finv hw]
    exact zmul_w _
  · subst hw
    have h' : u * u = 0 := by
      have e : u * u - W11 * (0 * 0) = u * u := fid (e := v 0 * v 0 - k W11 * (k 0 * k 0)) (e' := v 0 * v 0) (by decide) [u]
      rw [← e]; exact h
    rcases mul_eq_zero h' with e | e <;> exact ⟨e, rfl⟩

/-- `-11` is not a square: `i` turns a root of it into one of `11`. -/
theorem nonsquare_neg11 (z : F) : z * z ≠ -W11 := by
  intro h
  apply nonsquare_11 (z * iRoot)
  have e : z * iRoot * (z * iRoot) = (z * z) * (iRoot * iRoot) :=
    ZKF.fid (e := ZKF.v 0 * ZKF.v 1 * (ZKF.v 0 * ZKF.v 1)) (e' := ZKF.v 0 * ZKF.v 0 * (ZKF.v 1 * ZKF.v 1)) (by decide) [z, iRoot]
  rw [e, h, iRoot_sq]
  decide

open ZKF in
/-- `u² + 11 v² = 0` only at zero. -/
theorem sqn11_zero {u w : F} (h : u * u + W11 * (w * w) = 0) : u = 0 ∧ w = 0 := by
  rcases (inferInstance : Decidable (w = 0)) with hw | hw
  · exfalso
    apply nonsquare_neg11 (u * finv w)
    have e := sqn_scale u (finv w) w
    rw [e, h, mul_finv hw]
    exact zmul_nw _
  · subst hw
    have h' : u * u = 0 := by
      have e : u * u + W11 * (0 * 0) = u * u := fid (e := v 0 * v 0 + k W11 * (k 0 * k 0)) (e' := v 0 * v 0) (by decide) [u]
      rw [← e]; exact h
    rcases mul_eq_zero h' with e | e <;> exact ⟨e, rfl⟩

-- ---------------------------------------------------------------------------
-- The norm, and inverses
-- ---------------------------------------------------------------------------

namespace EF

/-- `x(-t)`: the conjugate under `t ↦ -t`. -/
def conj (x : EF) : EF := ⟨x.x0, -x.x1, x.x2, -x.x3⟩

/-- `x · conj x = c0 + c1 t²`. -/
def c0 (x : EF) : F := x.x0 * x.x0 + W11 * (x.x2 * x.x2) - (W11 + W11) * (x.x1 * x.x3)
def c1 (x : EF) : F := (x.x0 * x.x2 + x.x0 * x.x2) - x.x1 * x.x1 - W11 * (x.x3 * x.x3)

/-- **The norm to `F`**: `c0² - 11 c1²`. -/
def nrm (x : EF) : F := x.c0 * x.c0 - W11 * (x.c1 * x.c1)

def smul (a : F) (y : EF) : EF := (ofF a).mul y

/-- **The inverse**, zero at zero. -/
def inv (x : EF) : EF := smul (finv x.nrm) ((conj x).mul ⟨x.c0, 0, -x.c1, 0⟩)

open ZKF in
theorem mul_conj (x : EF) : x.mul (conj x) = ⟨x.c0, 0, x.c1, 0⟩ :=
  Q.eq_of_norm (p := (Q.var 0).mul ⟨v 0, .neg (v 1), v 2, .neg (v 3)⟩)
    (q := ⟨v 0 * v 0 + k W11 * (v 2 * v 2) - (k W11 + k W11) * (v 1 * v 3), k 0,
      (v 0 * v 2 + v 0 * v 2) - v 1 * v 1 - k W11 * (v 3 * v 3), k 0⟩) (by decide) (env3 x zero zero)

open ZKF in
theorem mul_d (a b : F) : (⟨a, 0, b, 0⟩ : EF).mul ⟨a, 0, -b, 0⟩ = ofF (a * a - W11 * (b * b)) :=
  Q.eq_of_norm (p := (Q.mul ⟨v 0, k 0, v 1, k 0⟩ ⟨v 0, k 0, .neg (v 1), k 0⟩))
    (q := ⟨v 0 * v 0 - k W11 * (v 1 * v 1), k 0, k 0, k 0⟩) (by decide) (env3 ⟨a, b, 0, 0⟩ zero zero)

theorem ofF_mul (a b : F) : (ofF a).mul (ofF b) = ofF (a * b) := by
  apply ext
  · show a * b + W11 * (0 * 0 + 0 * 0 + 0 * 0) = a * b
    exact ZKF.fid (e := ZKF.v 0 * ZKF.v 1 + ZKF.k W11 * (ZKF.k 0 * ZKF.k 0 + ZKF.k 0 * ZKF.k 0 + ZKF.k 0 * ZKF.k 0))
      (e' := ZKF.v 0 * ZKF.v 1) (by decide) [a, b]
  · show a * 0 + 0 * b + W11 * (0 * 0 + 0 * 0) = 0
    exact ZKF.fid (e := ZKF.v 0 * ZKF.k 0 + ZKF.k 0 * ZKF.v 1 + ZKF.k W11 * (ZKF.k 0 * ZKF.k 0 + ZKF.k 0 * ZKF.k 0))
      (e' := ZKF.k 0) (by decide) [a, b]
  · show a * 0 + 0 * 0 + 0 * b + W11 * (0 * 0) = 0
    exact ZKF.fid (e := ZKF.v 0 * ZKF.k 0 + ZKF.k 0 * ZKF.k 0 + ZKF.k 0 * ZKF.v 1 + ZKF.k W11 * (ZKF.k 0 * ZKF.k 0))
      (e' := ZKF.k 0) (by decide) [a, b]
  · show a * 0 + 0 * 0 + 0 * 0 + 0 * b = 0
    exact ZKF.fid (e := ZKF.v 0 * ZKF.k 0 + ZKF.k 0 * ZKF.k 0 + ZKF.k 0 * ZKF.k 0 + ZKF.k 0 * ZKF.v 1)
      (e' := ZKF.k 0) (by decide) [a, b]

theorem ofF_one : ofF 1 = one := rfl

/-- `x · inv x = 1` when the norm is not zero. -/
theorem mul_inv_of {x : EF} (h : x.nrm ≠ 0) : x.mul x.inv = one := by
  unfold inv smul
  rw [← mul_assoc, mul_comm _ (ofF _), mul_assoc, ← mul_assoc x, mul_conj, mul_d, ofF_mul]
  show ofF (finv (nrm x) * nrm x) = one
  rw [finv_mul h]; rfl

-- The polynomial identities behind the norm's nonvanishing.
open ZKF in
theorem id_AB (a0 a1 a2 a3 : F) :
    let A := a0 * a1 - W11 * (a2 * a3)
    let B := a1 * a2 - a0 * a3
    let no := a1 * a1 - W11 * (a3 * a3)
    let c0 := a0 * a0 + W11 * (a2 * a2) - (W11 + W11) * (a1 * a3)
    let c1 := (a0 * a2 + a0 * a2) - a1 * a1 - W11 * (a3 * a3)
    A * A + W11 * (B * B) = c0 * (a1 * a1 + W11 * (a3 * a3)) - (W11 + W11) * (c1 * (a1 * a3)) ∧
    (A + A) * B = no * no + c1 * (a1 * a1 + W11 * (a3 * a3)) - (c0 + c0) * (a1 * a3) := by
  intro A B no c0 c1
  refine ⟨?_, ?_⟩
  · exact fid (e := (v 0 * v 1 - k W11 * (v 2 * v 3)) * (v 0 * v 1 - k W11 * (v 2 * v 3)) +
        k W11 * ((v 1 * v 2 - v 0 * v 3) * (v 1 * v 2 - v 0 * v 3)))
      (e' := (v 0 * v 0 + k W11 * (v 2 * v 2) - (k W11 + k W11) * (v 1 * v 3)) * (v 1 * v 1 + k W11 * (v 3 * v 3)) -
        (k W11 + k W11) * (((v 0 * v 2 + v 0 * v 2) - v 1 * v 1 - k W11 * (v 3 * v 3)) * (v 1 * v 3)))
      (by decide) [a0, a1, a2, a3]
  · exact fid (e := ((v 0 * v 1 - k W11 * (v 2 * v 3)) + (v 0 * v 1 - k W11 * (v 2 * v 3))) * (v 1 * v 2 - v 0 * v 3))
      (e' := (v 1 * v 1 - k W11 * (v 3 * v 3)) * (v 1 * v 1 - k W11 * (v 3 * v 3)) +
        ((v 0 * v 2 + v 0 * v 2) - v 1 * v 1 - k W11 * (v 3 * v 3)) * (v 1 * v 1 + k W11 * (v 3 * v 3)) -
        ((v 0 * v 0 + k W11 * (v 2 * v 2) - (k W11 + k W11) * (v 1 * v 3)) +
          (v 0 * v 0 + k W11 * (v 2 * v 2) - (k W11 + k W11) * (v 1 * v 3))) * (v 1 * v 3))
      (by decide) [a0, a1, a2, a3]

end EF

open ZKF in
theorem zmul_sum (n s t : F) : n * n + 0 * s - (0 + 0) * t = n * n :=
  fid (e := v 0 * v 0 + k 0 * v 1 - (k 0 + k 0) * v 2) (e' := v 0 * v 0) (by decide) [n, s, t]

open ZKF in
theorem zmul_diff (s t : F) : 0 * s - (W11 + W11) * (0 * t) = 0 :=
  fid (e := k 0 * v 0 - (k W11 + k W11) * (k 0 * v 1)) (e' := k 0) (by decide) [s, t]

open ZKF in
theorem mul_zero_f (a : F) : a * 0 = 0 := fid (e := v 0 * k 0) (e' := k 0) (by decide) [a]

namespace EF

open ZKF in
theorem sq_ne_zero {a : F} (h : a ≠ 0) : a * a ≠ 0 := fun e => by
  rcases mul_eq_zero e with e | e <;> exact h e

open ZKF in
theorem c0_of (a0 a2 : F) : (⟨a0, 0, a2, 0⟩ : EF).c0 = a0 * a0 + W11 * (a2 * a2) :=
  fid (e := v 0 * v 0 + k W11 * (v 1 * v 1) - (k W11 + k W11) * (k 0 * k 0)) (e' := v 0 * v 0 + k W11 * (v 1 * v 1))
    (by decide) [a0, a2]

open ZKF in
theorem zero_sub_zero (a b : F) (ha : a = 0) (hb : b = 0) : a * a + W11 * (b * b) = 0 := by
  subst ha hb; decide

/-- **A nonzero element has a nonzero norm**, since `11` is no square. -/
theorem nrm_ne_zero {x : EF} (hx : x ≠ zero) : x.nrm ≠ 0 := by
  intro hn
  obtain ⟨hc0, hc1⟩ := sq11_zero hn
  obtain ⟨a0, a1, a2, a3⟩ := x
  obtain ⟨i1, i2⟩ := id_AB a0 a1 a2 a3
  have hc0' : a0 * a0 + W11 * (a2 * a2) - (W11 + W11) * (a1 * a3) = 0 := hc0
  have hc1' : (a0 * a2 + a0 * a2) - a1 * a1 - W11 * (a3 * a3) = 0 := hc1
  rw [hc0', hc1'] at i1 i2
  rcases (inferInstance : Decidable (a1 * a1 - W11 * (a3 * a3) = 0)) with hno | hno
  · -- the odd part is not zero: `(A / B)² = -11`
    have hB : (a0 * a1 - W11 * (a2 * a3) + (a0 * a1 - W11 * (a2 * a3))) * (a1 * a2 - a0 * a3) ≠ 0 := by
      rw [i2]
      have z1 := zmul_sum (a1 * a1 - W11 * (a3 * a3)) (a1 * a1 + W11 * (a3 * a3)) (a1 * a3)
      rw [z1]; exact sq_ne_zero hno
    have hA : (a0 * a1 - W11 * (a2 * a3)) * (a0 * a1 - W11 * (a2 * a3)) +
        W11 * ((a1 * a2 - a0 * a3) * (a1 * a2 - a0 * a3)) = 0 := by
      rw [i1]; exact zmul_diff (a1 * a1 + W11 * (a3 * a3)) (a1 * a3)
    obtain ⟨_, hb0⟩ := sqn11_zero hA
    apply hB; rw [hb0]; exact mul_zero_f _
  · -- the odd part is zero
    obtain ⟨h1, h3⟩ := sq11_zero hno
    subst h1 h3
    have hc : a0 * a0 + W11 * (a2 * a2) = 0 := by rw [← c0_of]; exact hc0
    obtain ⟨h0, h2⟩ := sqn11_zero hc
    subst h0 h2
    exact hx rfl

end EF

namespace EF

theorem mul_inv {x : EF} (hx : x ≠ zero) : x.mul x.inv = one := mul_inv_of (nrm_ne_zero hx)

theorem one_ne_zero : one ≠ zero := fun h => by
  have := congrArg EF.x0 h; exact absurd this (by decide)

theorem fpow_zero_succ : ∀ n, fpow 0 (n + 1) = 0
  | n => by rw [fpow, mul_zero_f]

theorem finv_zero : finv 0 = 0 := by
  unfold finv; rw [show P - 2 = (P - 3) + 1 by decide, fpow_zero_succ]

theorem nrm_zero : zero.nrm = 0 := by decide

theorem inv_zero : zero.inv = zero := by
  unfold inv smul
  rw [nrm_zero, finv_zero]
  show (ofF 0).mul _ = zero
  rw [mul_comm, show ofF 0 = zero from rfl, mul_zero]

theorem inv_ne_zero {x : EF} (hx : x ≠ zero) : x.inv ≠ zero := fun h => by
  have := mul_inv hx
  rw [h, mul_zero] at this
  exact one_ne_zero this.symm

theorem one_mul (x : EF) : one.mul x = x := by rw [mul_comm, mul_one]

/-- **The inverse is an involution**, zero included: so a bijection. -/
theorem inv_inv (x : EF) : x.inv.inv = x := by
  rcases (inferInstance : Decidable (x = zero)) with hx | hx
  · have hi := inv_ne_zero hx
    calc x.inv.inv = x.inv.inv.mul (x.inv.mul x) := by rw [mul_comm x.inv x, mul_inv hx, mul_one]
      _ = (x.inv.inv.mul x.inv).mul x := by rw [mul_assoc]
      _ = x := by rw [mul_comm x.inv.inv x.inv, mul_inv hi, one_mul]
  · subst hx; rw [inv_zero, inv_zero]

end EF

end Circuit
