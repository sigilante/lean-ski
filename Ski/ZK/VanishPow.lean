import Ski.ZK.QuotPoly

/-!
# A coset's vanishing polynomial is `Xⁿ - sⁿ`

Plonky3 evaluates a coset's vanishing polynomial, and the selectors
built from it, through the closed form `Z_H(x) = (x / s)ⁿ - 1`
(`commit/src/domain.rs`).  The model uses the product `∏_{a ∈ H} (x - a)`.
They agree up to the scale `sⁿ`: for the coset `H = s ⟨g⟩` of `n`
distinct points with `gⁿ = 1`, `∏_{a ∈ H} (x - a) = xⁿ - sⁿ` at every
`x` (`fvan_coset_pow`).

The product is monic of degree `|L|`: it is `low_L + X^{|L|}` with
`low_L` of at most `|L|` coefficients (`fval_lowv`).  On the coset,
`low_H + sⁿ` has at most `n` coefficients and `n` distinct roots, so it
is zero (`froots_lt`).
-/

namespace Circuit

open ZKF

/-- `c Xᵐ`. -/
def fmono (c : F) : Nat → List F
  | 0 => [c]
  | m + 1 => 0 :: fmono c m

theorem fval_fmono (x c : F) : ∀ m, fval x (fmono c m) = c * fpow x m
  | 0 => by rw [show fmono c 0 = [c] from rfl, fval_single]; show c = c * 1; rw [mul_one']
  | m + 1 => by
    show 0 + x * fval x (fmono c m) = c * (fpow x m * x)
    rw [fval_fmono x c m, zero_add']
    exact fid (e := v 0 * (v 1 * v 2)) (e' := v 1 * (v 2 * v 0)) (by decide) [x, c, fpow x m]

theorem fmono_length (c : F) : ∀ m, (fmono c m).length = m + 1
  | 0 => rfl
  | m + 1 => by show (fmono c m).length + 1 = m + 2; rw [fmono_length]

/-- **The product's lower part**: `∏_{a ∈ L} (X - a) - X^{|L|}`. -/
def lowv : List F → List F
  | [] => []
  | a :: L => fcadd (fclin a (lowv L)) (fmono (-a) L.length)

theorem lowv_length : ∀ L : List F, (lowv L).length ≤ L.length
  | [] => Nat.le_refl 0
  | a :: L => by
    have h1 := fcadd_length (fclin a (lowv L)) (fmono (-a) L.length)
    have h2 := fclin_length a (lowv L)
    have h3 := lowv_length L
    rw [fmono_length] at h1
    show (fcadd _ _).length ≤ L.length + 1
    omega

theorem low_step (x a lo p : F) : (x - a) * lo + -a * p + p * x = (x - a) * (lo + p) :=
  fid (e := (v 0 - v 1) * v 2 + (-v 1) * v 3 + v 3 * v 0) (e' := (v 0 - v 1) * (v 2 + v 3)) (by decide) [x, a, lo, p]

/-- **The product is monic**: `∏_{a ∈ L} (x - a) = low_L(x) + x^{|L|}`. -/
theorem fval_lowv (x : F) : ∀ L : List F, fval x (fvan L) = fval x (lowv L) + fpow x L.length
  | [] => by rw [show fvan [] = [1] from rfl, fval_one]; show (1 : F) = 0 + 1; rw [zero_add']
  | a :: L => by
    show fval x (fclin a (fvan L)) = fval x (fcadd (fclin a (lowv L)) (fmono (-a) L.length)) + fpow x L.length * x
    rw [fval_fclin, fval_fcadd, fval_fclin, fval_fmono, fval_lowv x L]
    exact (low_step x a _ _).symm

theorem fpow_mul_distrib (a b : F) : ∀ n, fpow (a * b) n = fpow a n * fpow b n
  | 0 => by show (1 : F) = 1 * 1; rw [one_mul']
  | n + 1 => by
    show fpow (a * b) n * (a * b) = fpow a n * a * (fpow b n * b)
    rw [fpow_mul_distrib a b n, mul4]

theorem low_fin (lo X S : F) (h : lo + S = 0) : lo + X = X - S := by
  have e : lo + X = (lo + S) + (X - S) :=
    fid (e := v 0 + v 1) (e' := (v 0 + v 2) + (v 1 - v 2)) (by decide) [lo, X, S]
  rw [e, h, zero_add']

/-- **A coset's vanishing polynomial is `xⁿ - sⁿ`**: for `n` distinct
    points `s gᵗ`, `gⁿ = 1`. -/
theorem fvan_coset_pow {s g : F} {n : Nat} (hn : 0 < n) (hg : fpow g n = 1) (hnd : (cosetL s g n).Nodup) (x : F) :
    fval x (fvan (cosetL s g n)) = fpow x n - fpow s n := by
  have hL : (cosetL s g n).length = n := cosetL_length s g n
  -- `low_H + sⁿ` vanishes on the coset
  have hroot : ∀ y ∈ cosetL s g n, fval y (fcadd (lowv (cosetL s g n)) [fpow s n]) = 0 := fun y hy => by
    have h0 := fvan_root y _ hy
    rw [fval_lowv, hL] at h0
    obtain ⟨t, _, rfl⟩ := mem_coset hy
    have hp : fpow (s * fpow g t) n = fpow s n := by
      rw [fpow_mul_distrib, ← fpow_mul' g t n, Nat.mul_comm t n, fpow_mul' g n t, hg, fpow_one', mul_one']
    rw [hp] at h0
    rw [fval_fcadd, fval_single]
    exact h0
  have hz : FZero (fcadd (lowv (cosetL s g n)) [fpow s n]) := by
    rcases (inferInstance : Decidable (FZero (fcadd (lowv (cosetL s g n)) [fpow s n]))) with hz | hz
    · have hlen : (fcadd (lowv (cosetL s g n)) [fpow s n]).length ≤ max n 1 := by
        have := fcadd_length (lowv (cosetL s g n)) [fpow s n]
        have := lowv_length (cosetL s g n)
        rw [hL] at this
        simp only [List.length_cons, List.length_nil] at *
        omega
      have := froots_lt _ _ hlen hz (cosetL s g n) hnd hroot
      rw [hL] at this
      have : max n 1 = n := Nat.max_eq_left hn
      omega
    · exact hz
  have := fval_fzero x _ hz
  rw [fval_fcadd, fval_single] at this
  rw [fval_lowv, hL]
  exact low_fin _ _ _ this

-- ---------------------------------------------------------------------------
-- Plonky3's selectors on the trace domain `⟨g⟩`
-- ---------------------------------------------------------------------------

theorem cosetL_snoc (s g : F) : ∀ m, cosetL s g (m + 1) = cosetL s g m ++ [s * fpow g m]
  | 0 => by show [s] = [s * 1]; rw [mul_one']
  | m + 1 => by
    show s :: cosetL (s * g) g (m + 1) = s :: (cosetL (s * g) g m ++ [s * fpow g (m + 1)])
    rw [cosetL_snoc (s * g) g m, mul_assoc', fpow_succ']

theorem fval_fvan_snoc (x b : F) : ∀ L : List F, fval x (fvan (L ++ [b])) = fval x (fvan L) * (x - b)
  | [] => by
    show fval x (fclin b (fvan [])) = fval x (fvan []) * (x - b)
    rw [fval_fclin, mul_comm']
  | a :: L => by
    show fval x (fclin a (fvan (L ++ [b]))) = fval x (fclin a (fvan L)) * (x - b)
    rw [fval_fclin, fval_fclin, fval_fvan_snoc x b L, mul_assoc']

/-- **Plonky3's first-row selector**: on the trace domain `⟨g⟩` of size
    `m + 1`, `∏_{a ∈ H, a ≠ 1} (x - a) · (x - 1) = xᵐ⁺¹ - 1`, so the
    product is `Z_H(x) / (x - 1)` (`is_first_row`). -/
theorem sel_first {g : F} {m : Nat} (hg : fpow g (m + 1) = 1) (hnd : (cosetL 1 g (m + 1)).Nodup) (x : F) :
    (x - 1) * fval x (fvan (cosetL (1 * g) g m)) = fpow x (m + 1) - 1 := by
  rw [← fval_fclin, show fclin 1 (fvan (cosetL (1 * g) g m)) = fvan (cosetL 1 g (m + 1)) from rfl,
    fvan_coset_pow (Nat.succ_pos m) hg hnd x, fpow_one']

/-- **Plonky3's last-row selector**: `∏_{a ∈ H, a ≠ gᵐ} (x - a) · (x - gᵐ)
    = xᵐ⁺¹ - 1`, and `gᵐ = g⁻¹` (`is_last_row`, `is_transition`). -/
theorem sel_last {g : F} {m : Nat} (hg : fpow g (m + 1) = 1) (hnd : (cosetL 1 g (m + 1)).Nodup) (x : F) :
    fval x (fvan (cosetL 1 g m)) * (x - fpow g m) = fpow x (m + 1) - 1 ∧ fpow g m * g = 1 := by
  refine ⟨?_, hg⟩
  rw [← one_mul' (fpow g m), ← fval_fvan_snoc, ← cosetL_snoc, fvan_coset_pow (Nat.succ_pos m) hg hnd x, fpow_one']

end Circuit
