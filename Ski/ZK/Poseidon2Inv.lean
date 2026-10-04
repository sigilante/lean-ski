import Ski.ZK.Poseidon2Generic

/-!
# Poseidon2's S-box and linear layers are invertible

On BabyBear (`p = 15 · 2^27 + 1`), for Plonky3's parameters
(`Generic.plonky3`):

- **The S-box `x ↦ x^7` is a bijection** (`sbox_bijective`):
  `gcd(7, p − 1) = 1`, and `x ↦ x^e` with `e = 1725656503`, where
  `7e = 1 + 6 (p − 1)`, inverts it on both sides, by Fermat's little
  theorem (`Circuit.fermat_nat`, which rests on `p` being prime).
- **The external layer `M_E` and the internal layer `M_I` are invertible**
  (`ext_inv`, `int_inv`): each has a two-sided inverse on the vectors of
  sixteen elements below `p`; so do the specification's layers
  `Poseidon2.extLinear` and `Poseidon2.intLinear` (`extLinear_inv`,
  `intLinear_inv`).  The inverse matrices are data computed
  outside Lean; the kernel checks both products against the identity, by
  substituting one matrix's row expressions into the other's and
  normalizing (`Lin.linRows`).
-/

namespace Poseidon2.Inv

open Poseidon2.Lin Poseidon2.Generic Poseidon2SKI

-- ---------------------------------------------------------------------------
-- The S-box
-- ---------------------------------------------------------------------------

theorem gcd_7 : Nat.gcd 7 (p - 1) = 1 := by decide +kernel

/-- The S-box's inverse exponent, `7⁻¹` modulo `p − 1`. -/
def e : Nat := 1725656503

theorem seven_e : 7 * e = 1 + 6 * (p - 1) := by decide +kernel

/-- The inverse S-box. -/
def sboxInv (x : Nat) : Nat := x ^ e % p

theorem p_eq : p = Circuit.P := rfl

/-- `x^(j + (p − 1)) ≡ x^j` for `j ≥ 1`. -/
theorem pow_cycle (x j : Nat) : x ^ (j + 1 + (p - 1)) % p = x ^ (j + 1) % p := by
  have h : j + 1 + (p - 1) = j + p := by
    rw [Nat.add_assoc, Nat.add_comm 1, Nat.sub_add_cancel (by decide : 1 ≤ p)]
  rw [h, Nat.pow_add, Nat.mul_mod, p_eq, Circuit.fermat_nat, ← Nat.mul_mod, ← Nat.pow_succ]

theorem pow_cycles (x : Nat) : ∀ k, x ^ (1 + k * (p - 1)) % p = x % p
  | 0 => by rw [Nat.zero_mul, Nat.add_zero, Nat.pow_one]
  | k + 1 => by
    rw [Nat.succ_mul, ← Nat.add_assoc, show 1 + k * (p - 1) = k * (p - 1) + 1 from Nat.add_comm _ _,
      pow_cycle, ← pow_cycles x k, Nat.add_comm 1]

theorem pow_7e (x : Nat) : x ^ (7 * e) % p = x % p := by
  rw [seven_e, pow_cycles]

/-- **The inverse S-box undoes the S-box**, below `p`. -/
theorem sboxInv_sbox (x : Nat) (hx : x < p) : sboxInv (sbox x) = x := by
  show (x ^ 7 % p) ^ e % p = x
  rw [← Nat.pow_mod, ← Nat.pow_mul, pow_7e, Nat.mod_eq_of_lt hx]

/-- **The S-box undoes the inverse S-box**, below `p`. -/
theorem sbox_sboxInv (x : Nat) (hx : x < p) : sbox (sboxInv x) = x := by
  show (x ^ e % p) ^ 7 % p = x
  rw [← Nat.pow_mod, ← Nat.pow_mul, Nat.mul_comm, pow_7e, Nat.mod_eq_of_lt hx]

/-- The S-box on BabyBear's elements. -/
def sboxF (x : Fin p) : Fin p := ⟨sbox x.val, Nat.mod_lt _ (by decide)⟩

/-- **`x ↦ x^7` is a bijection of BabyBear**: injective and surjective. -/
theorem sbox_bijective : (∀ a b : Fin p, sboxF a = sboxF b → a = b) ∧ ∀ y : Fin p, ∃ x, sboxF x = y := by
  constructor
  · intro a b h
    apply Fin.ext
    have h' : sbox a.val = sbox b.val := congrArg Fin.val h
    rw [← sboxInv_sbox a.val a.isLt, ← sboxInv_sbox b.val b.isLt, h']
  · intro y
    refine ⟨⟨sboxInv y.val, Nat.mod_lt _ (by decide)⟩, Fin.ext ?_⟩
    exact sbox_sboxInv y.val y.isLt

-- ---------------------------------------------------------------------------
-- The linear layers
-- ---------------------------------------------------------------------------

/-- `M_E⁻¹`, computed outside Lean; `ext_inv` checks it. -/
def extInv : List (List Nat) :=
  [[816810745, 897341382, 736280108, 1058402656, 299113794, 782297615, 1829195894, 1748665257, 299113794, 782297615, 1829195894, 1748665257, 299113794, 782297615, 1829195894, 1748665257],
    [1058402656, 816810745, 897341382, 736280108, 1748665257, 299113794, 782297615, 1829195894, 1748665257, 299113794, 782297615, 1829195894, 1748665257, 299113794, 782297615, 1829195894],
    [736280108, 1058402656, 816810745, 897341382, 1829195894, 1748665257, 299113794, 782297615, 1829195894, 1748665257, 299113794, 782297615, 1829195894, 1748665257, 299113794, 782297615],
    [897341382, 736280108, 1058402656, 816810745, 782297615, 1829195894, 1748665257, 299113794, 782297615, 1829195894, 1748665257, 299113794, 782297615, 1829195894, 1748665257, 299113794],
    [299113794, 782297615, 1829195894, 1748665257, 816810745, 897341382, 736280108, 1058402656, 299113794, 782297615, 1829195894, 1748665257, 299113794, 782297615, 1829195894, 1748665257],
    [1748665257, 299113794, 782297615, 1829195894, 1058402656, 816810745, 897341382, 736280108, 1748665257, 299113794, 782297615, 1829195894, 1748665257, 299113794, 782297615, 1829195894],
    [1829195894, 1748665257, 299113794, 782297615, 736280108, 1058402656, 816810745, 897341382, 1829195894, 1748665257, 299113794, 782297615, 1829195894, 1748665257, 299113794, 782297615],
    [782297615, 1829195894, 1748665257, 299113794, 897341382, 736280108, 1058402656, 816810745, 782297615, 1829195894, 1748665257, 299113794, 782297615, 1829195894, 1748665257, 299113794],
    [299113794, 782297615, 1829195894, 1748665257, 299113794, 782297615, 1829195894, 1748665257, 816810745, 897341382, 736280108, 1058402656, 299113794, 782297615, 1829195894, 1748665257],
    [1748665257, 299113794, 782297615, 1829195894, 1748665257, 299113794, 782297615, 1829195894, 1058402656, 816810745, 897341382, 736280108, 1748665257, 299113794, 782297615, 1829195894],
    [1829195894, 1748665257, 299113794, 782297615, 1829195894, 1748665257, 299113794, 782297615, 736280108, 1058402656, 816810745, 897341382, 1829195894, 1748665257, 299113794, 782297615],
    [782297615, 1829195894, 1748665257, 299113794, 782297615, 1829195894, 1748665257, 299113794, 897341382, 736280108, 1058402656, 816810745, 782297615, 1829195894, 1748665257, 299113794],
    [299113794, 782297615, 1829195894, 1748665257, 299113794, 782297615, 1829195894, 1748665257, 299113794, 782297615, 1829195894, 1748665257, 816810745, 897341382, 736280108, 1058402656],
    [1748665257, 299113794, 782297615, 1829195894, 1748665257, 299113794, 782297615, 1829195894, 1748665257, 299113794, 782297615, 1829195894, 1058402656, 816810745, 897341382, 736280108],
    [1829195894, 1748665257, 299113794, 782297615, 1829195894, 1748665257, 299113794, 782297615, 1829195894, 1748665257, 299113794, 782297615, 736280108, 1058402656, 816810745, 897341382],
    [782297615, 1829195894, 1748665257, 299113794, 782297615, 1829195894, 1748665257, 299113794, 782297615, 1829195894, 1748665257, 299113794, 897341382, 736280108, 1058402656, 816810745]]

/-- `M_I⁻¹`, computed outside Lean; `int_inv` checks it. -/
def intInv : List (List Nat) :=
  [[754974720, 503316480, 251658240, 1006632960, 167772160, 125829120, 1006632961, 1845493761, 1887436801, 2013265857, 2013265920, 2013265919, 1979711489, 64, 4, 33554432],
    [503316480, 1006632962, 1509949441, 1, 1677721601, 1761607681, 2013265920, 335544320, 251658240, 128, 2, 4, 67108864, 2013265793, 2013265913, 1946157057],
    [251658240, 1509949441, 754974721, 1006632961, 1845493761, 1887436801, 1006632960, 167772160, 125829120, 64, 1, 2, 33554432, 2013265857, 2013265917, 1979711489],
    [1006632960, 1, 1006632961, 4, 1342177281, 1509949441, 2013265919, 671088640, 503316480, 256, 4, 8, 134217728, 2013265665, 2013265905, 1879048193],
    [167772160, 1677721601, 1845493761, 1342177281, 559240534, 1929379841, 671088640, 782936747, 83886080, 671088683, 671088641, 1342177282, 1364546902, 1342177238, 1342177278, 648719019],
    [125829120, 1761607681, 1887436801, 1509949441, 1929379841, 1447034881, 503316480, 83886080, 62914560, 32, 1006632961, 1, 16777216, 2013265889, 2013265919, 1996488705],
    [1006632961, 2013265920, 1006632960, 2013265919, 671088640, 503316480, 0, 1342177281, 1509949441, 2013265665, 2013265917, 2013265913, 1879048193, 256, 16, 134217728],
    [1845493761, 335544320, 167772160, 671088640, 782936747, 83886080, 1342177281, 1901417814, 1929379841, 1342177238, 1342177280, 671088639, 648719019, 671088683, 671088643, 1364546902],
    [1887436801, 251658240, 125829120, 503316480, 83886080, 62914560, 1509949441, 1929379841, 440401920, 2013265889, 1006632960, 2013265920, 1996488705, 32, 2, 16777216],
    [2013265857, 128, 64, 256, 671088683, 32, 2013265665, 1342177238, 2013265889, 33024, 512, 1024, 1073741816, 2013233153, 2013263873, 939524105],
    [2013265920, 2, 1, 4, 671088641, 1006632961, 2013265917, 1342177280, 1006632960, 512, 12, 16, 268435456, 2013265409, 2013265889, 1744830465],
    [2013265919, 4, 2, 8, 1342177282, 1, 2013265913, 671088639, 2013265920, 1024, 16, 40, 536870912, 2013264897, 2013265857, 1476395009],
    [1979711489, 67108864, 33554432, 134217728, 1364546902, 16777216, 1879048193, 648719019, 1996488705, 1073741816, 268435456, 536870912, 666614716, 939524105, 939524097, 1480868933],
    [64, 2013265793, 2013265857, 2013265665, 1342177238, 2013265889, 256, 671088683, 32, 2013233153, 2013265409, 2013264897, 939524105, 32512, 2048, 1073741816],
    [4, 2013265913, 2013265917, 2013265905, 1342177278, 2013265919, 16, 671088643, 2, 2013263873, 2013265889, 2013265857, 939524097, 2048, 112, 1073741824],
    [33554432, 1946157057, 1979711489, 1879048193, 648719019, 1996488705, 134217728, 1364546902, 16777216, 939524105, 1744830465, 1476395009, 1480868933, 1073741816, 1073741824, 398179260]]

/-- The identity's rows. -/
def id16 : List (List Nat) := (List.range 16).map fun i => unitL i 0 16

theorem all_len16 (M : List (List Nat)) (hM : M.all (·.length == 16) = true) :
    ∀ r ∈ M, r.length = 16 :=
  fun r hr => beq_iff_eq.mp (List.all_eq_true.mp hM r hr)

/-- **A product checked to be the identity inverts**: if substituting
    `B`'s row expressions into `A`'s normalizes to the identity, `A`
    undoes `B` on every vector of sixteen elements below `p`. -/
theorem inv_of_rows (A B : List (List Nat)) (hA : A.all (·.length == 16) = true)
    (hB : B.all (·.length == 16) = true) (hBl : B.length = 16)
    (hAB : linRows ((A.map rowEx).map (P2Air.exSubst (B.map rowEx))) = some id16)
    (s : List Nat) (hs : s.length = 16) (hlt : ∀ x ∈ s, x < p) :
    matVec p A (matVec p B s) = s := by
  have hBs : (matVec p B s).length = 16 := by rw [matVec_len, hBl]
  have hrows : ∀ (M : List (List Nat)), M.all (·.length == 16) = true → ∀ (v : List Nat),
      v.length = 16 → ∀ r ∈ M, r.length ≤ v.length :=
    fun M hM v hv r hr => by rw [all_len16 M hM r hr, hv]; exact Nat.le_refl _
  rw [matVec_eval A _ (hrows A hA _ hBs), matVec_eval B s (hrows B hB s hs)]
  have hρ : env ((B.map rowEx).map (Ex.eval (env s))) =
      fun i => ((B.map rowEx).getD i (.lit 0)).eval (env s) :=
    funext fun i => getD_map_eval (env s) (B.map rowEx) i
  rw [hρ]
  have h := linRows_sound (env s) _ _ hAB
  rw [List.map_map] at h
  have h' : (A.map rowEx).map (Ex.eval fun i => ((B.map rowEx).getD i (.lit 0)).eval (env s)) =
      ((A.map rowEx).map (P2Air.exSubst (B.map rowEx))).map (Ex.eval (env s)) := by
    rw [List.map_map, List.map_map, List.map_map]
    apply List.map_congr_left
    intro x _
    exact (P2Air.eval_subst (env s) (B.map rowEx) (rowEx x)).symm
  rw [h', List.map_map, h]
  show ((List.range 16).map fun i => unitL i 0 16).map (fun c => dotF c 0 (env s) % p) = s
  rw [List.map_map]
  conv => rhs; rw [← range16_map 0 s hs]
  apply List.map_congr_left
  intro i hi
  show dotF (unitL i 0 16) 0 (env s) % p = s.getD i 0
  have hi' : i < 16 := List.mem_range.mp hi
  rw [dotF_unit i hi']
  show s.getD i 0 % p = s.getD i 0
  have hix : i < s.length := by rw [hs]; exact hi'
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hix, Option.getD_some]
  exact Nat.mod_eq_of_lt (hlt _ (List.getElem_mem hix))

theorem extInv_ME : linRows ((extInv.map rowEx).map (P2Air.exSubst (plonky3.ME.map rowEx))) = some id16 := by
  decide +kernel
theorem ME_extInv : linRows ((plonky3.ME.map rowEx).map (P2Air.exSubst (extInv.map rowEx))) = some id16 := by
  decide +kernel
theorem intInv_MI : linRows ((intInv.map rowEx).map (P2Air.exSubst (plonky3.MI.map rowEx))) = some id16 := by
  decide +kernel
theorem MI_intInv : linRows ((plonky3.MI.map rowEx).map (P2Air.exSubst (intInv.map rowEx))) = some id16 := by
  decide +kernel

/-- **The external layer `M_E` is invertible**: `extInv` undoes it on both
    sides, on every vector of sixteen elements below `p`. -/
theorem ext_inv (s : List Nat) (hs : s.length = 16) (hlt : ∀ x ∈ s, x < p) :
    matVec p extInv (matVec p plonky3.ME s) = s ∧ matVec p plonky3.ME (matVec p extInv s) = s :=
  ⟨inv_of_rows _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) extInv_ME s hs hlt,
   inv_of_rows _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) ME_extInv s hs hlt⟩

/-- **The internal layer `M_I` is invertible**: `intInv` undoes it on both
    sides, on every vector of sixteen elements below `p`. -/
theorem int_inv (s : List Nat) (hs : s.length = 16) (hlt : ∀ x ∈ s, x < p) :
    matVec p intInv (matVec p plonky3.MI s) = s ∧ matVec p plonky3.MI (matVec p intInv s) = s :=
  ⟨inv_of_rows _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) intInv_MI s hs hlt,
   inv_of_rows _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) MI_intInv s hs hlt⟩

/-- **The specification's external layer is invertible.** -/
theorem extLinear_inv (s : List Nat) (hs : s.length = 16) (hlt : ∀ x ∈ s, x < p) :
    matVec p extInv (extLinear s) = s ∧ extLinear (matVec p extInv s) = s := by
  have hl : (matVec p extInv s).length = 16 := by rw [matVec_len]; decide
  rw [extLinear_eq s hs, extLinear_eq _ hl]
  exact ext_inv s hs hlt

/-- **The specification's internal layer is invertible.** -/
theorem intLinear_inv (s : List Nat) (hs : s.length = 16) (hlt : ∀ x ∈ s, x < p) :
    matVec p intInv (intLinear s) = s ∧ intLinear (matVec p intInv s) = s := by
  have hl : (matVec p intInv s).length = 16 := by rw [matVec_len]; decide
  rw [intLinear_eq s hs, intLinear_eq _ hl]
  exact int_inv s hs hlt

end Poseidon2.Inv
