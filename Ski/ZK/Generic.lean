import Ski.ZK.Chain

/-!
# Which combiner challenges are generic

`Generic β`, the combiner matrix invertible, holds exactly outside the
quadratic subfield `F(x^2)`: `β` is generic if and only if its `x` or `x^3`
coordinate is not zero (`generic_iff`).  So `P^2` of the `P^4` challenges
fail it (`nongeneric_count`).

The proof is Vandermonde's.  `x ↦ ζ x`, for `ζ` a primitive fourth root of
unity in `F`, generates the Galois group of the extension; the product of
the differences of `β`'s four conjugates is the combiner's determinant
times the constant `c x^2` (`vdm_eq`), and each difference is zero only if
both odd coordinates are.
-/

namespace Circuit

open ZKF

-- ---------------------------------------------------------------------------
-- Substitution
-- ---------------------------------------------------------------------------

/-- Replace atoms by expressions. -/
def E.substZ (σ : Atom → E) : E → E
  | .atom a => σ a
  | .const c => .const c
  | .add a b => .add (a.substZ σ) (b.substZ σ)
  | .sub a b => .sub (a.substZ σ) (b.substZ σ)
  | .mul a b => .mul (a.substZ σ) (b.substZ σ)
  | .neg a => .neg (a.substZ σ)

theorem E.eval_substZ (σ : Atom → E) (ρ : Atom → F) :
    ∀ e : E, (e.substZ σ).eval ρ = e.eval (fun a => (σ a).eval ρ)
  | .atom _ => rfl
  | .const _ => rfl
  | .add a b => by simp only [E.substZ, E.eval, E.eval_substZ σ ρ a, E.eval_substZ σ ρ b]
  | .sub a b => by simp only [E.substZ, E.eval, E.eval_substZ σ ρ a, E.eval_substZ σ ρ b]
  | .mul a b => by simp only [E.substZ, E.eval, E.eval_substZ σ ρ a, E.eval_substZ σ ρ b]
  | .neg a => by simp only [E.substZ, E.eval, E.eval_substZ σ ρ a]

-- ---------------------------------------------------------------------------
-- The determinant, symbolically
-- ---------------------------------------------------------------------------

/-- `β^n`, symbolically in `β = Q.var 0`. -/
def Pw : Nat → Q
  | 0 => ⟨k 1, k 0, k 0, k 0⟩
  | n + 1 => (Pw n).mul (Q.var 0)

theorem Pw_eval (β : EF) : ∀ n, (Pw n).eval (env3 β EF.zero EF.zero) = bpow β n
  | 0 => rfl
  | n + 1 => by
    show ((Pw n).eval (env3 β EF.zero EF.zero)).mul β = (bpow β n).mul β
    rw [Pw_eval β n]

/-- The combiner matrix's entries, symbolically. -/
def combσ : Atom → E
  | .main 0 0 => (Pw 3).q0 | .main 0 1 => (Pw 2).q0 | .main 0 2 => (Pw 1).q0 | .main 0 3 => (Pw 0).q0
  | .main 0 4 => (Pw 3).q1 | .main 0 5 => (Pw 2).q1 | .main 0 6 => (Pw 1).q1 | .main 0 7 => (Pw 0).q1
  | .main 0 8 => (Pw 3).q2 | .main 0 9 => (Pw 2).q2 | .main 0 10 => (Pw 1).q2 | .main 0 11 => (Pw 0).q2
  | .main 0 12 => (Pw 3).q3 | .main 0 13 => (Pw 2).q3 | .main 0 14 => (Pw 1).q3 | .main 0 15 => (Pw 0).q3
  | _ => k 0

/-- The combiner's determinant as a polynomial in `β`'s coordinates. -/
def detβ : E := det4E.substZ combσ

theorem det_eq (β : EF) : (combMat β).det = detβ.eval (env3 β EF.zero EF.zero) := by
  have hp := Pw_eval β
  have env : (fun a => (combσ a).eval (env3 β EF.zero EF.zero)) = atL ((combMat β).l EF.zero 0) := by
    funext a
    match a with
    | .main 0 0 => exact congrArg EF.x0 (hp 3)
    | .main 0 1 => exact congrArg EF.x0 (hp 2)
    | .main 0 2 => exact congrArg EF.x0 (hp 1)
    | .main 0 3 => exact congrArg EF.x0 (hp 0)
    | .main 0 4 => exact congrArg EF.x1 (hp 3)
    | .main 0 5 => exact congrArg EF.x1 (hp 2)
    | .main 0 6 => exact congrArg EF.x1 (hp 1)
    | .main 0 7 => exact congrArg EF.x1 (hp 0)
    | .main 0 8 => exact congrArg EF.x2 (hp 3)
    | .main 0 9 => exact congrArg EF.x2 (hp 2)
    | .main 0 10 => exact congrArg EF.x2 (hp 1)
    | .main 0 11 => exact congrArg EF.x2 (hp 0)
    | .main 0 12 => exact congrArg EF.x3 (hp 3)
    | .main 0 13 => exact congrArg EF.x3 (hp 2)
    | .main 0 14 => exact congrArg EF.x3 (hp 1)
    | .main 0 15 => exact congrArg EF.x3 (hp 0)
    | .main 0 16 => rfl
    | .main 0 17 => rfl
    | .main 0 18 => rfl
    | .main 0 19 => rfl
    | .main 0 20 => rfl
    | .main 0 (_ + 21) => rfl
    | .main (_ + 1) _ => rfl
    | .pre _ _ => rfl
    | .first => rfl
    | .last => rfl
    | .trans => rfl
  unfold detβ
  rw [E.eval_substZ, env]
  rfl

-- ---------------------------------------------------------------------------
-- The conjugates
-- ---------------------------------------------------------------------------

/-- `ζ`, a primitive fourth root of unity: `ζ^2 = -1`. -/
def ζ : F := iRoot
def ζ3 : F := ofN (P - 1728404513)

/-- `β`'s conjugates, `x ↦ ζ^j x`. -/
def conjE (β : EF) : Nat → EF
  | 0 => ⟨β.x0, 1 * β.x1, 1 * β.x2, 1 * β.x3⟩
  | 1 => ⟨β.x0, ζ * β.x1, ofN (P - 1) * β.x2, ζ3 * β.x3⟩
  | 2 => ⟨β.x0, ofN (P - 1) * β.x1, 1 * β.x2, ofN (P - 1) * β.x3⟩
  | _ => ⟨β.x0, ζ3 * β.x1, ofN (P - 1) * β.x2, ζ * β.x3⟩

def conjQ : Nat → Q
  | 0 => ⟨v 0, k 1 * v 1, k 1 * v 2, k 1 * v 3⟩
  | 1 => ⟨v 0, k ζ * v 1, k (ofN (P - 1)) * v 2, k ζ3 * v 3⟩
  | 2 => ⟨v 0, k (ofN (P - 1)) * v 1, k 1 * v 2, k (ofN (P - 1)) * v 3⟩
  | _ => ⟨v 0, k ζ3 * v 1, k (ofN (P - 1)) * v 2, k ζ * v 3⟩

def dif (β : EF) (j l : Nat) : EF := (conjE β l).sub (conjE β j)

/-- The product of the conjugates' differences. -/
def vdm (β : EF) : EF :=
  (((((dif β 0 1).mul (dif β 0 2)).mul (dif β 0 3)).mul (dif β 1 2)).mul (dif β 1 3)).mul (dif β 2 3)

def difQ (j l : Nat) : Q := (conjQ l).sub (conjQ j)

def vdmQ : Q :=
  (((((difQ 0 1).mul (difQ 0 2)).mul (difQ 0 3)).mul (difQ 1 2)).mul (difQ 1 3)).mul (difQ 2 3)

/-- The Vandermonde constant. -/
def cV : F := ofN 1817225704

theorem vdm_n0 : vdmQ.q0.norm = (k 0).norm := by decide +kernel
theorem vdm_n1 : vdmQ.q1.norm = (k 0).norm := by decide +kernel
theorem vdm_n2 : vdmQ.q2.norm = (k cV * detβ).norm := by decide +kernel
theorem vdm_n3 : vdmQ.q3.norm = (k 0).norm := by decide +kernel

theorem conjQ_eval (β : EF) : ∀ j, (conjQ j).eval (env3 β EF.zero EF.zero) = conjE β j
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | _ + 3 => rfl

theorem vdmQ_eval (β : EF) : vdmQ.eval (env3 β EF.zero EF.zero) = vdm β := by
  simp only [vdmQ, difQ, Q.eval_mul, Q.eval_sub, conjQ_eval]
  rfl

/-- **Vandermonde**: the conjugates' differences multiply to `c · det · x^2`. -/
theorem vdm_eq (β : EF) : vdm β = ⟨0, 0, cV * (combMat β).det, 0⟩ := by
  rw [det_eq, ← vdmQ_eval]
  exact Q.eq_of_norm (p := vdmQ) (q := ⟨k 0, k 0, k cV * detβ, k 0⟩) ⟨vdm_n0, vdm_n1, vdm_n2, vdm_n3⟩
    (env3 β EF.zero EF.zero)

-- ---------------------------------------------------------------------------
-- No zero divisors
-- ---------------------------------------------------------------------------

theorem fmul_assoc (a b c : F) : a * b * c = a * (b * c) :=
  fid (e := v 0 * v 1 * v 2) (e' := v 0 * (v 1 * v 2)) (by decide) [a, b, c]

theorem fsub_self (a : F) : a - a = 0 := fid (e := v 0 - v 0) (e' := k 0) (by decide) [a]

/-- `F` has no zero divisors. -/
theorem f_cancel {a b : F} (ha : a ≠ 0) (h : a * b = 0) : b = 0 := by
  rw [← f_one_mul b, ← finv_mul ha, fmul_assoc, h, mul_zero_f]

theorem odd_cancel {c d b : F} (hcd : c - d ≠ 0) (h : c * b - d * b = 0) : b = 0 := by
  have e : c * b - d * b = (c - d) * b :=
    fid (e := v 0 * v 2 - v 1 * v 2) (e' := (v 0 - v 1) * v 2) (by decide) [c, d, b]
  rw [e] at h
  exact f_cancel hcd h

/-- The extension has no zero divisors. -/
theorem EF.mul_eq_zero {x y : EF} (h : x.mul y = EF.zero) : x = EF.zero ∨ y = EF.zero :=
  if hx : x = EF.zero then .inl hx else .inr (by
    rw [← EF.one_mul y, ← EF.mul_inv hx, EF.mul_comm x, EF.mul_assoc, h, EF.mul_zero])

-- ---------------------------------------------------------------------------
-- Generic exactly outside `F(x^2)`
-- ---------------------------------------------------------------------------

/-- Two conjugates agree only if both odd coordinates are zero. -/
theorem odd_of {β : EF} {a1 a2 a3 b1 b2 b3 : F} (h1 : a1 - b1 ≠ 0) (h3 : a3 - b3 ≠ 0)
    (h : (⟨β.x0, a1 * β.x1, a2 * β.x2, a3 * β.x3⟩ : EF).sub ⟨β.x0, b1 * β.x1, b2 * β.x2, b3 * β.x3⟩ = EF.zero) :
    β.x1 = 0 ∧ β.x3 = 0 :=
  ⟨odd_cancel h1 (congrArg EF.x1 h), odd_cancel h3 (congrArg EF.x3 h)⟩

theorem vdm_zero {β : EF} (h : vdm β = EF.zero) : β.x1 = 0 ∧ β.x3 = 0 := by
  unfold vdm at h
  rcases EF.mul_eq_zero h with h | h
  · rcases EF.mul_eq_zero h with h | h
    · rcases EF.mul_eq_zero h with h | h
      · rcases EF.mul_eq_zero h with h | h
        · rcases EF.mul_eq_zero h with h | h
          · exact odd_of (by decide) (by decide) h
          · exact odd_of (by decide) (by decide) h
        · exact odd_of (by decide) (by decide) h
      · exact odd_of (by decide) (by decide) h
    · exact odd_of (by decide) (by decide) h
  · exact odd_of (by decide) (by decide) h

/-- **A challenge off the quadratic subfield is generic.** -/
theorem generic_of {β : EF} (h : β.x1 ≠ 0 ∨ β.x3 ≠ 0) : Generic β := fun hd => by
  have hv : vdm β = EF.zero := by
    rw [vdm_eq, hd]; exact EF.ext rfl rfl (mul_zero_f cV) rfl
  have key := vdm_zero hv
  rcases h with h | h
  · exact h key.1
  · exact h key.2

/-- **A challenge in the quadratic subfield is not.** -/
theorem not_generic_of {β : EF} (h1 : β.x1 = 0) (h3 : β.x3 = 0) : ¬Generic β := fun hg => by
  have hz : dif β 0 2 = EF.zero := by
    apply EF.ext
    · exact fsub_self β.x0
    · show ofN (P - 1) * β.x1 - 1 * β.x1 = 0; rw [h1]; decide
    · exact fsub_self _
    · show ofN (P - 1) * β.x3 - 1 * β.x3 = 0; rw [h3]; decide
  have hv : vdm β = EF.zero := by
    unfold vdm; rw [hz, EF.mul_zero, EF.zero_mul, EF.zero_mul, EF.zero_mul, EF.zero_mul]
  rw [vdm_eq] at hv
  exact hg (f_cancel (a := cV) (by decide) (congrArg EF.x2 hv))

/-- **`Generic β` exactly when `β` is outside `F(x^2)`.** -/
theorem generic_iff (β : EF) : Generic β ↔ (β.x1 ≠ 0 ∨ β.x3 ≠ 0) :=
  ⟨fun hg => if h1 : β.x1 = 0 then (if h3 : β.x3 = 0 then absurd hg (not_generic_of h1 h3) else .inr h3)
    else .inl h1, generic_of⟩

theorem det_zero_iff (β : EF) : (combMat β).det = 0 ↔ β.x1 = 0 ∧ β.x3 = 0 :=
  ⟨fun hd => if h1 : β.x1 = 0 then
      (if h3 : β.x3 = 0 then ⟨h1, h3⟩ else absurd hd (generic_of (.inr h3)))
    else absurd hd (generic_of (.inl h1)),
   fun ⟨h1, h3⟩ => if hd : (combMat β).det = 0 then hd else absurd hd (not_generic_of h1 h3)⟩

-- ---------------------------------------------------------------------------
-- Counting the non-generic challenges
-- ---------------------------------------------------------------------------

/-- A tuple as an extension element. -/
def Tup.toEF (a : Tup) : EF := ⟨a.t0, a.t1, a.t2, a.t3⟩

theorem sumTo_succ (f : Nat → Nat) (n : Nat) : sumTo (n + 1) f = sumTo n f + f n := rfl

theorem sumTo_app (f : Nat → Nat) (a : Nat) : ∀ b, sumTo (a + b) f = sumTo a f + sumTo b (fun r => f (a + r))
  | 0 => rfl
  | b + 1 => by
    show sumTo (a + b) f + f (a + b) = sumTo a f + (sumTo b (fun r => f (a + r)) + f (a + b))
    rw [sumTo_app f a b, Nat.add_assoc]

/-- A sum over `[0, P m)`, by the last base-`P` digit. -/
theorem sumTo_digits (f : Nat → Nat) : ∀ m, sumTo (P * m) f = sumTo m (fun q => sumTo P (fun r => f (r + P * q)))
  | 0 => by rw [Nat.mul_zero]; rfl
  | m + 1 => by
    rw [Nat.mul_succ, sumTo_app, sumTo_digits f m, sumTo_succ,
      sumTo_congr (f := fun r => f (P * m + r)) (g := fun r => f (r + P * m)) P
        (fun r _ => by show f (P * m + r) = f (r + P * m); rw [Nat.add_comm])]

theorem ofN_zero_iff {x : Nat} (hx : x < P) : ofN x = 0 ↔ x = 0 :=
  ⟨fun h => by have e := val_ofN hx; rw [h] at e; exact e.symm, fun h => by rw [h]; exact ofN_zero⟩

/-- `[x = 0]` over a digit sums to one. -/
theorem sumTo_zero_digit (c : Nat) : sumTo P (fun r => if ofN r = 0 then c else 0) = c := by
  have : ∀ n, n ≤ P → sumTo n (fun r => if ofN r = 0 then c else 0) = if n = 0 then 0 else c := by
    intro n
    induction n with
    | zero => intro _; rfl
    | succ n ih =>
      intro hn
      rw [sumTo_succ, ih (by omega), if_neg (Nat.succ_ne_zero n)]
      rcases Nat.decEq n 0 with h | h
      · rw [if_neg h, if_neg (fun e => h ((ofN_zero_iff (by omega)).1 e))]; exact Nat.add_zero c
      · rw [if_pos h, h, if_pos ofN_zero]; exact Nat.zero_add c
  rw [this P (Nat.le_refl P), if_neg (by have := P_pos; omega)]

/-- **`P^2` of the `P^4` challenges are not generic**: those in `F(x^2)`. -/
theorem nongeneric_count :
    sumTo Q4 (fun i => if (combMat (Tup.dec i).toEF).det = 0 then 1 else 0) = P * P := by
  have hP := P_pos
  have e0 : ∀ i, (if (combMat (Tup.dec i).toEF).det = 0 then 1 else 0) =
      (if ofN (i / P % P) = 0 then (if ofN (i / P / P / P) = 0 then 1 else 0) else 0) := by
    intro i
    have h := det_zero_iff (Tup.dec i).toEF
    by_cases ha : ofN (i / P % P) = 0
    · by_cases hb : ofN (i / P / P / P) = 0
      · rw [if_pos (h.2 ⟨ha, hb⟩), if_pos ha, if_pos hb]
      · rw [if_neg (fun e => hb (h.1 e).2), if_pos ha, if_neg hb]
    · rw [if_neg (fun e => ha (h.1 e).1), if_neg ha]
  rw [sumTo_congr Q4 (fun i _ => e0 i)]
  unfold Q4
  -- the lowest digit is free
  rw [sumTo_digits]
  have e1 : ∀ q, sumTo P (fun r => if ofN ((r + P * q) / P % P) = 0 then
      (if ofN ((r + P * q) / P / P / P) = 0 then 1 else 0) else 0) =
      P * (if ofN (q % P) = 0 then (if ofN (q / P / P) = 0 then 1 else 0) else 0) := by
    intro q
    rw [sumTo_congr P (fun r hr => by rw [(Tup.digit r q hr).2]), sumTo_const]
  rw [sumTo_congr _ (fun q _ => e1 q), ← sumTo_mul, sumTo_digits]
  -- the next digit is zero
  have e2 : ∀ q, sumTo P (fun r => if ofN ((r + P * q) % P) = 0 then
      (if ofN ((r + P * q) / P / P) = 0 then 1 else 0) else 0) = (if ofN (q / P) = 0 then 1 else 0) := by
    intro q
    rw [sumTo_congr P (fun r hr => by rw [(Tup.digit r q hr).1, (Tup.digit r q hr).2])]
    exact sumTo_zero_digit _
  rw [sumTo_congr _ (fun q _ => e2 q), sumTo_digits]
  -- the third is free, the last zero
  have e3 : ∀ q, sumTo P (fun r => if ofN ((r + P * q) / P) = 0 then 1 else 0) = P * (if ofN q = 0 then 1 else 0) := by
    intro q
    rw [sumTo_congr P (fun r hr => by rw [(Tup.digit r q hr).2]), sumTo_const, Nat.mul_comm]
  rw [sumTo_congr _ (fun q _ => e3 q), ← sumTo_mul P (fun q => if ofN q = 0 then 1 else 0), sumTo_zero_digit,
    Nat.mul_one]

end Circuit
