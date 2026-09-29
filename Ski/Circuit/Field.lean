/-!
# BabyBear

The Plonky3 circuit works over BabyBear, the prime field of
`P = 15 · 2^27 + 1 = 2013265921` elements.  Here it is `Fin P` with Lean's
own ring structure (`Lean.Grind.CommRing`), and the facts the circuit's
constraints need:

- **`P` is prime** (`euclid`), by trial division up to `√P`, checked in the
  kernel (`noDiv_P`).
- **No zero divisors** (`mul_eq_zero`), so a constraint `x (x - 1) = 0`
  makes `x` a bit (`bit_of`).
- **Small numbers are themselves** (`val_natCast`): a count or an address
  below `P` is the element it names.
-/

namespace Circuit

/-- BabyBear's modulus. -/
def P : Nat := 2013265921

theorem P_eq : P = 15 * 2 ^ 27 + 1 := rfl

instance : NeZero P := ⟨by decide⟩

/-- BabyBear. -/
abbrev F := Fin P

-- ---------------------------------------------------------------------------
-- P is prime
-- ---------------------------------------------------------------------------

/-- No divisor of `p` from `d` on, while `d * d ≤ p`, within `fuel` tries. -/
def noDiv (p : Nat) : Nat → Nat → Bool
  | 0, _ => true
  | fuel + 1, d => if d * d > p then true else if p % d == 0 then false else noDiv p fuel (d + 1)

set_option maxRecDepth 200000 in
theorem noDiv_P : noDiv P 50000 2 = true := by decide

theorem noDiv_sound (p : Nat) : ∀ (fuel d : Nat), noDiv p fuel d = true →
    ∀ e, d ≤ e → e * e ≤ p → e < d + fuel → p % e ≠ 0
  | 0, d, _, e, h1, _, h3 => absurd h1 (Nat.not_le_of_lt (by rw [Nat.add_zero] at h3; exact h3))
  | fuel + 1, d, h, e, h1, h2, h3 => by
    unfold noDiv at h
    by_cases hd : d * d > p
    · exact absurd (Nat.lt_of_lt_of_le hd (Nat.le_trans (Nat.mul_le_mul h1 h1) h2)) (Nat.lt_irrefl _)
    · rw [if_neg hd] at h
      by_cases hm : (p % d == 0) = true
      · rw [if_pos hm] at h; cases h
      · rw [if_neg hm] at h
        rcases Nat.lt_or_eq_of_le h1 with hlt | heq
        · refine noDiv_sound p fuel (d + 1) h e (Nat.succ_le_of_lt hlt) h2 ?_
          rw [Nat.add_assoc, Nat.add_comm 1 fuel]; exact h3
        · subst heq
          intro h0
          exact hm (by rw [h0]; rfl)

/-- A factor of `P` at most its square root is below the checked range. -/
theorem small_factor {e : Nat} (h2 : 2 ≤ e) (he : e * e ≤ P) (hdiv : e ∣ P) : False := by
  have hlt : e < 2 + 50000 :=
    Nat.lt_of_not_le fun hge =>
      Nat.lt_irrefl P (Nat.lt_of_lt_of_le (by decide : P < 50002 * 50002)
        (Nat.le_trans (Nat.mul_le_mul hge hge) he))
  exact noDiv_sound P 50000 2 noDiv_P e h2 he hlt (Nat.mod_eq_zero_of_dvd hdiv)

theorem P_pos : 0 < P := by decide

/-- No `d` with `2 ≤ d < P` divides `P`. -/
theorem no_divisor {d : Nat} (h2 : 2 ≤ d) (hd : d < P) : ¬ d ∣ P := by
  intro ⟨q, hq⟩
  have hq2 : 2 ≤ q := by
    rcases Nat.lt_or_ge q 2 with h | h
    · cases q with
      | zero => rw [Nat.mul_zero] at hq; exact absurd hq (Nat.ne_of_gt P_pos)
      | succ q =>
        cases q with
        | zero => rw [Nat.mul_one] at hq; exact absurd hq (Nat.ne_of_gt hd)
        | succ q => exact absurd h (Nat.not_lt_of_le (Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le q))))
    · exact h
  rcases Nat.le_total d q with hle | hle
  · exact small_factor h2 (by rw [hq]; exact Nat.mul_le_mul_left d hle) ⟨q, hq⟩
  · exact small_factor hq2 (by rw [hq, Nat.mul_comm d q]; exact Nat.mul_le_mul_left q hle)
      ⟨d, by rw [hq, Nat.mul_comm]⟩

/-- **Euclid's lemma for `P`.** -/
theorem euclid {a b : Nat} (h : P ∣ a * b) : P ∣ a ∨ P ∣ b := by
  by_cases ha : P ∣ a
  · exact .inl ha
  · right
    have hg1 : Nat.gcd P a ∣ P := Nat.gcd_dvd_left P a
    have hgpos : 0 < Nat.gcd P a := Nat.gcd_pos_of_pos_left a P_pos
    have hcop : Nat.Coprime P a := by
      show Nat.gcd P a = 1
      have hle : Nat.gcd P a ≤ P := Nat.le_of_dvd P_pos hg1
      rcases Nat.lt_or_ge (Nat.gcd P a) 2 with hl | hl
      · exact Nat.le_antisymm (Nat.le_of_lt_succ hl) hgpos
      · rcases Nat.lt_or_eq_of_le hle with hlt | heq
        · exact absurd hg1 (no_divisor hl hlt)
        · exact absurd (heq ▸ Nat.gcd_dvd_right P a) ha
    exact hcop.dvd_of_dvd_mul_left h

-- ---------------------------------------------------------------------------
-- The field
-- ---------------------------------------------------------------------------

theorem mul_eq_zero {a b : F} (h : a * b = 0) : a = 0 ∨ b = 0 := by
  have hv : (a.val * b.val) % P = 0 := by
    have := congrArg Fin.val h
    simpa [Fin.val_mul] using this
  rcases euclid (Nat.dvd_of_mod_eq_zero hv) with ha | hb
  · left
    apply Fin.ext
    have := Nat.eq_zero_of_dvd_of_lt ha a.isLt
    simpa using this
  · right
    apply Fin.ext
    have := Nat.eq_zero_of_dvd_of_lt hb b.isLt
    simpa using this

theorem sub_eq_zero {a b : F} (h : a - b = 0) : a = b := by
  have : a - b + b = b := by rw [h]; exact Lean.Grind.AddCommMonoid.zero_add b
  rw [Lean.Grind.Ring.sub_eq_add_neg, Lean.Grind.AddCommMonoid.add_assoc,
    Lean.Grind.Ring.neg_add_cancel, Lean.Grind.AddCommMonoid.add_zero] at this
  exact this

/-- **A bit**: `x (x - 1) = 0` makes `x` zero or one. -/
theorem bit_of {x : F} (h : x * (x - 1) = 0) : x = 0 ∨ x = 1 := by
  rcases mul_eq_zero h with h | h
  · exact .inl h
  · exact .inr (sub_eq_zero h)

/-- A natural number as an element. -/
def ofN (n : Nat) : F := Fin.ofNat P n

/-- A natural number below `P`, as an element, has itself as its value. -/
theorem val_ofN {n : Nat} (h : n < P) : (ofN n).val = n := by
  simp [ofN, Fin.ofNat, Nat.mod_eq_of_lt h]

theorem ofN_zero : ofN 0 = 0 := rfl
theorem ofN_one : ofN 1 = 1 := rfl

end Circuit
