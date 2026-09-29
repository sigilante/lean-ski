import Ski.Circuit.Flow

/-!
# Fermat's little theorem for BabyBear, and 11 is not a square

`x ^ P = x` for every `x` in BabyBear (`fermat`), by the binomial theorem:
`P` divides every inner binomial coefficient of `(a + 1) ^ P`.  With it,
Euler's criterion refutes a square root of `11`: the kernel computes
`11 ^ ((P - 1) / 2) = -1` by repeated squaring (`nonsquare_11`).  That is
what makes Plonky3's quartic extension `F[x] / (x^4 - 11)` a field.
-/

namespace Circuit

-- ---------------------------------------------------------------------------
-- Binomial coefficients
-- ---------------------------------------------------------------------------

def choose : Nat → Nat → Nat
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => choose n k + choose n (k + 1)

theorem choose_zero_succ (k : Nat) : choose 0 (k + 1) = 0 := rfl

theorem choose_zero_right : ∀ n, choose n 0 = 1
  | 0 => rfl
  | _ + 1 => rfl

theorem choose_self : ∀ n, choose n n = 1
  | 0 => rfl
  | n + 1 => by
    show choose n n + choose n (n + 1) = 1
    rw [choose_self n, choose_gt n (n + 1) (Nat.lt_succ_self n)]
where
  choose_gt : ∀ n k, n < k → choose n k = 0
    | 0, 0, h => absurd h (Nat.lt_irrefl 0)
    | 0, _ + 1, _ => rfl
    | _ + 1, 0, h => absurd h (Nat.not_lt_zero _)
    | n + 1, k + 1, h => by
      show choose n k + choose n (k + 1) = 0
      rw [choose_gt n k (by omega), choose_gt n (k + 1) (by omega)]

theorem choose_gt' {n k : Nat} (h : n < k) : choose n k = 0 := choose_self.choose_gt n k h

/-- Absorption: `(k + 1) · C(n + 1, k + 1) = (n + 1) · C(n, k)`. -/
theorem choose_absorb : ∀ n k, (k + 1) * choose (n + 1) (k + 1) = (n + 1) * choose n k
  | 0, 0 => rfl
  | 0, k + 1 => by
    show (k + 2) * (choose 0 (k + 1) + choose 0 (k + 2)) = 1 * choose 0 (k + 1)
    rw [choose_zero_succ, choose_zero_succ, Nat.add_zero, Nat.mul_zero, Nat.mul_zero]
  | n + 1, 0 => by
    show 1 * (choose (n + 1) 0 + choose (n + 1) 1) = (n + 2) * 1
    have e : choose (n + 1) 1 = n + 1 := by
      have := choose_absorb n 0
      rw [Nat.one_mul, choose_zero_right, Nat.mul_one] at this
      exact this
    rw [e, choose_zero_right]; omega
  | n + 1, k + 1 => by
    show (k + 2) * (choose (n + 1) (k + 1) + choose (n + 1) (k + 2)) =
      (n + 2) * (choose n k + choose n (k + 1))
    have h1 := choose_absorb n k
    have h2 := choose_absorb n (k + 1)
    have e3 : choose (n + 1) (k + 1) = choose n k + choose n (k + 1) := rfl
    have e1 : (k + 2) * choose (n + 1) (k + 1) = (k + 1) * choose (n + 1) (k + 1) + choose (n + 1) (k + 1) := by
      rw [show k + 2 = (k + 1) + 1 from rfl, Nat.add_mul, Nat.one_mul]
    have h2' : (k + 2) * choose (n + 1) (k + 2) = (n + 1) * choose n (k + 1) := h2
    have e2 : ∀ x, (n + 2) * x = (n + 1) * x + x := fun x => by
      rw [show n + 2 = (n + 1) + 1 from rfl, Nat.add_mul, Nat.one_mul]
    rw [Nat.mul_add, Nat.mul_add, e1, h2', e2, e2]
    omega

-- ---------------------------------------------------------------------------
-- The binomial theorem, for `(a + 1) ^ n`
-- ---------------------------------------------------------------------------

theorem sumTo_shift' (g : Nat → Nat) : ∀ n, sumTo (n + 1) g = g 0 + sumTo n (fun j => g (j + 1))
  | 0 => by show 0 + g 0 = g 0 + 0; omega
  | n + 1 => by
    show sumTo (n + 1) g + g (n + 1) = g 0 + (sumTo n (fun j => g (j + 1)) + g (n + 1))
    rw [sumTo_shift' g n]; omega

theorem sumTo_mul (c : Nat) (f : Nat → Nat) : ∀ n, c * sumTo n f = sumTo n (fun j => c * f j)
  | 0 => rfl
  | n + 1 => by
    show c * (sumTo n f + f n) = sumTo n (fun j => c * f j) + c * f n
    rw [Nat.mul_add, sumTo_mul c f n]

theorem binom (a : Nat) : ∀ n, (a + 1) ^ n = sumTo (n + 1) (fun k => choose n k * a ^ k)
  | 0 => rfl
  | n + 1 => by
    rw [Nat.pow_succ, binom a n, Nat.mul_add, Nat.mul_one,
      Nat.mul_comm (sumTo (n + 1) (fun k => choose n k * a ^ k)) a, sumTo_mul a _ (n + 1)]
    rw [sumTo_shift' (fun k => choose (n + 1) k * a ^ k) (n + 1)]
    have e : ∀ j, choose (n + 1) (j + 1) * a ^ (j + 1) =
        a * (choose n j * a ^ j) + choose n (j + 1) * a ^ (j + 1) := by
      intro j
      show (choose n j + choose n (j + 1)) * a ^ (j + 1) = _
      rw [Nat.add_mul, Nat.pow_succ]
      rw [show choose n j * (a ^ j * a) = a * (choose n j * a ^ j) by
        rw [Nat.mul_comm (a ^ j) a, ← Nat.mul_assoc, Nat.mul_comm (choose n j) a, Nat.mul_assoc]]
    rw [sumTo_congr (n + 1) (fun j _ => e j), sumTo_add]
    have hz : sumTo (n + 1) (fun j => choose n (j + 1) * a ^ (j + 1)) =
        sumTo n (fun j => choose n (j + 1) * a ^ (j + 1)) := by
      show sumTo n _ + choose n (n + 1) * a ^ (n + 1) = _
      rw [choose_gt' (Nat.lt_succ_self n), Nat.zero_mul, Nat.add_zero]
    rw [sumTo_shift' (fun k => choose n k * a ^ k) n, hz, choose_zero_right, choose_zero_right]
    omega

-- ---------------------------------------------------------------------------
-- Fermat
-- ---------------------------------------------------------------------------

theorem P_dvd_choose {k : Nat} (h0 : 0 < k) (hk : k < P) : P ∣ choose P k := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hP : P = (P - 1) + 1 := by have := P_pos; omega
  have e := choose_absorb (P - 1) j
  rw [← hP] at e
  have hd : P ∣ (j + 1) * choose P (j + 1) := ⟨choose (P - 1) j, e⟩
  rcases euclid hd with h | h
  · exact absurd h (fun h' => by have := Nat.le_of_dvd (by omega) h'; omega)
  · exact h

/-- `(a + 1) ^ P ≡ a ^ P + 1`, modulo `P`. -/
theorem frob_succ (a : Nat) : (a + 1) ^ P % P = (a ^ P + 1) % P := by
  rw [binom a P]
  have hP : P = (P - 1) + 1 := by have := P_pos; omega
  -- split off the first and last terms
  rw [sumTo_shift' _ P]
  rw [hP, show sumTo (P - 1 + 1) (fun j => choose (P - 1 + 1) (j + 1) * a ^ (j + 1)) =
    sumTo (P - 1) (fun j => choose (P - 1 + 1) (j + 1) * a ^ (j + 1)) +
      choose (P - 1 + 1) (P - 1 + 1) * a ^ (P - 1 + 1) from rfl, ← hP, choose_self]
  have hm : P ∣ sumTo (P - 1) (fun j => choose P (j + 1) * a ^ (j + 1)) := by
    have : ∀ m, m ≤ P - 1 → P ∣ sumTo m (fun j => choose P (j + 1) * a ^ (j + 1)) := by
      intro m
      induction m with
      | zero => intro _; exact Nat.dvd_zero P
      | succ m ih =>
        intro hm
        exact Nat.dvd_add (ih (by omega)) (Nat.dvd_mul_right_of_dvd (P_dvd_choose (by omega) (by omega)) _)
    exact this (P - 1) (Nat.le_refl _)
  obtain ⟨q, hq⟩ := hm
  rw [hq, show choose P 0 * a ^ 0 = 1 from rfl, Nat.one_mul]
  rw [show 1 + (P * q + a ^ P) = (a ^ P + 1) + P * q by omega, Nat.add_mul_mod_self_left]

/-- **Fermat, over `Nat`**: `a ^ P ≡ a`, modulo `P`. -/
theorem fermat_nat : ∀ a, a ^ P % P = a % P
  | 0 => by rw [Nat.zero_pow P_pos]
  | a + 1 => by
    rw [frob_succ, Nat.add_mod, fermat_nat a, ← Nat.add_mod]

-- ---------------------------------------------------------------------------
-- In the field
-- ---------------------------------------------------------------------------

/-- Powers in BabyBear. -/
def fpow (x : F) : Nat → F
  | 0 => 1
  | n + 1 => fpow x n * x

theorem ofN_mod (n : Nat) : ofN (n % P) = ofN n := by
  apply Fin.ext; show n % P % P = n % P; exact Nat.mod_mod n P

theorem ofN_val (x : F) : ofN x.val = x := by
  apply Fin.ext; show x.val % P = x.val; exact Nat.mod_eq_of_lt x.isLt

theorem fpow_ofN (a : Nat) : ∀ n, fpow (ofN a) n = ofN (a ^ n)
  | 0 => rfl
  | n + 1 => by rw [fpow, fpow_ofN a n, Nat.pow_succ, ofN_mul]

/-- **Fermat**: `x ^ P = x`. -/
theorem fermat (x : F) : fpow x P = x := by
  rw [← ofN_val x, fpow_ofN, ← ofN_mod, fermat_nat, ofN_mod]

def at2 (a b : F) : Atom → F
  | .main 0 0 => a | .main 0 1 => b | _ => 0

theorem mul_sub_one (a b : F) : a * b - b = (a - 1) * b :=
  E.eval_eq_of_norm (e := .sub (.mul (.atom (.main 0 0)) (.atom (.main 0 1))) (.atom (.main 0 1)))
    (e' := .mul (.sub (.atom (.main 0 0)) (.const 1)) (.atom (.main 0 1))) (by decide) (at2 a b)

/-- **Fermat, for units**: `x ^ (P - 1) = 1` when `x ≠ 0`. -/
theorem fermat_unit {x : F} (hx : x ≠ 0) : fpow x (P - 1) = 1 := by
  have h := fermat x
  rw [show P = (P - 1) + 1 from by have := P_pos; omega, fpow] at h
  have h0 : (fpow x (P - 1) - 1) * x = 0 := by rw [← mul_sub_one, h, sub_self']
  rcases mul_eq_zero h0 with e | e
  · exact sub_eq_zero e
  · exact absurd e hx

theorem fpow_mul_self (x : F) : ∀ m, fpow x (2 * m) = fpow (x * x) m
  | 0 => rfl
  | m + 1 => by
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by omega, fpow, fpow, fpow_mul_self x m, fpow]
    exact E.eval_eq_of_norm (e := .mul (.mul (.atom (.main 0 0)) (.atom (.main 0 1))) (.atom (.main 0 1)))
      (e' := .mul (.atom (.main 0 0)) (.mul (.atom (.main 0 1)) (.atom (.main 0 1)))) (by decide)
      (at2 (fpow (x * x) m) x)

/-- Powers by repeated squaring, `fuel` bits of exponent: what the kernel
    can evaluate. -/
def fpowFast : Nat → F → Nat → F
  | 0, _, _ => 1
  | fuel + 1, x, n => if n = 0 then 1
    else if n % 2 = 0 then fpowFast fuel (x * x) (n / 2) else fpowFast fuel (x * x) (n / 2) * x

theorem fpowFast_eq : ∀ fuel x n, n < 2 ^ fuel → fpowFast fuel x n = fpow x n
  | 0, _, n, h => by rw [Nat.pow_zero] at h; rw [show n = 0 by omega]; rfl
  | fuel + 1, x, n, h => by
    unfold fpowFast
    split
    · next h0 => rw [h0]; rfl
    · rw [Nat.pow_succ] at h
      split
      · next he =>
        rw [fpowFast_eq fuel (x * x) (n / 2) (by omega), ← fpow_mul_self]
        congr 1; omega
      · next ho =>
        rw [fpowFast_eq fuel (x * x) (n / 2) (by omega), ← fpow_mul_self]
        conv => rhs; rw [show n = 2 * (n / 2) + 1 by omega]
        rfl

/-- Euler's criterion's computation: `11 ^ ((P - 1) / 2) = -1`. -/
theorem euler_11 : fpowFast 32 (ofN 11) ((P - 1) / 2) = ofN (P - 1) := by decide

/-- **11 is not a square in BabyBear.** -/
theorem nonsquare_11 (x : F) : x * x ≠ ofN 11 := by
  intro h
  have hx : x ≠ 0 := by
    intro e; rw [e] at h; exact absurd h (by decide)
  have h1 := fermat_unit hx
  rw [show P - 1 = 2 * ((P - 1) / 2) by decide, fpow_mul_self, h,
    ← fpowFast_eq 32 _ _ (by decide), euler_11] at h1
  exact absurd h1 (by decide)

/-- A square root of `-1`: Plonky3's `DTH_ROOT` for the quartic extension. -/
def iRoot : F := ofN 1728404513

theorem iRoot_sq : iRoot * iRoot = ofN (P - 1) := by decide

end Circuit
