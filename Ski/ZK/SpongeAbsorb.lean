import Ski.ZK.SpongeUnion

/-!
# Plonky3 0.8's absorption

`SpongeUnion` asks equal permutation inputs to come from states with equal
projections `κ` (`hpk2`).  Its instance `hpk2_satPT` overwrites part of
the rate and keeps the rest.  Plonky3 0.8's `DuplexChallenger::duplexing`
absorbs `n ≤ RATE` elements differently: it writes them to the first `n`
rate slots, zeroes the other rate slots, and adds `n` to the first
capacity element before permuting (`p3-challenger-0.8.0`,
`duplex_challenger.rs`).

- **The model.** A state below `Rr · p · Q` is a rate value below `Rr`, a
  first capacity element below `p` and the capacity's other elements
  below `Q`; a block `x` carries its length `n = x % (R + 1)` and its
  values `(x / (R + 1)) % p ^ n` (`len08`, `vals08`).  `inner08` writes the
  values, zero-filled to the rate, and adds `n` to the first capacity
  element modulo `p`.
- **The capacity fails `hpk2`.** The length tag lets a short block from
  one capacity and a longer block from another give one input: with
  `R = 2` and `p = 3`, the empty block from first element `1` and the
  one-element block `0` from first element `0` both reach `Rr · 1`
  (`inner08_full_fails`).
- **The rest of the capacity meets it.** Dividing the input by `Rr · p`
  recovers the capacity's other elements whatever the block, so `κ08`,
  those elements alone, meets `hpk2` (`inner08_hpk2`), with `hin`
  (`inner08_lt`) and `hF` at `F = Rr · p`, the states sharing them
  (`κ08_count`).  At BabyBear width 16 and rate 8, `F / K` is
  `1 / p ^ 7`, one field element less than the full capacity's `1 / p ^ 8`.
- **First commitments stay apart.** Two full-rate blocks with distinct
  values give distinct inputs from any state (`inner08_hd`).

`SpongeUnion`'s composites take `inner`, `κ` and `hpk2` as parameters, so
`inner08` and `κ08` fit them as they stand.  The other premises stay as
`SpongeUnion` states them: the tags `h0`, `hnz`, which 0.8 does not
provide, and the state `iv` fixed before the permutation, where
batch-stark absorbs a domain separator first.
-/

set_option autoImplicit false

namespace Circuit
open ZKF

/-- The length of block `x`: at most `R`. -/
def len08 (R x : Nat) : Nat := x % (R + 1)

/-- The values of block `x`, `len08 R x` field elements. -/
def vals08 (R p x : Nat) : Nat := (x / (R + 1)) % p ^ len08 R x

/-- **0.8's absorption**: the block's values zero-filled to the rate, its
    length added to the first capacity element. -/
def inner08 (R Rr p Q : Nat) (s x : Nat) : Nat :=
  vals08 R p x + Rr * (((s / Rr) % p + len08 R x) % p + p * ((s / (Rr * p)) % Q))

/-- The capacity's elements after the first. -/
def κ08 (Rr p Q : Nat) (s : Nat) : Nat := (s / (Rr * p)) % Q

theorem vals08_lt {R p : Nat} (hp : 0 < p) (x : Nat) : vals08 R p x < p ^ R := by
  unfold vals08
  refine Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.pow_pos hp)) (Nat.pow_le_pow_right hp ?_)
  unfold len08; exact Nat.le_of_lt_succ (Nat.mod_lt _ (Nat.succ_pos R))

/-- The input splits as values, first capacity element and the rest. -/
theorem inner08_div {R p Q : Nat} (hp : 0 < p) (s x : Nat) :
    inner08 R (p ^ R) p Q s x / (p ^ R * p) = (s / (p ^ R * p)) % Q := by
  have hRr : 0 < p ^ R := Nat.pow_pos hp
  unfold inner08
  rw [← Nat.div_div_eq_div_mul, Nat.add_mul_div_left _ _ hRr, Nat.div_eq_of_lt (vals08_lt hp x), Nat.zero_add,
    Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt (Nat.mod_lt _ hp), Nat.zero_add]

/-- **The rest of the capacity meets `hpk2`.** -/
theorem inner08_hpk2 {R p Q : Nat} (hp : 0 < p) :
    ∀ s s' x x', inner08 R (p ^ R) p Q s x = inner08 R (p ^ R) p Q s' x' → κ08 (p ^ R) p Q s = κ08 (p ^ R) p Q s' := by
  intro s s' x x' e
  have h := congrArg (· / (p ^ R * p)) e
  simp only [inner08_div hp] at h
  exact h

/-- Inputs stay below the state count. -/
theorem inner08_lt {R p Q : Nat} (hp : 0 < p) (hQ : 0 < Q) (s x : Nat) :
    inner08 R (p ^ R) p Q s x < p ^ R * (p * Q) := by
  have hRr : 0 < p ^ R := Nat.pow_pos hp
  unfold inner08
  have h1 : ((s / p ^ R) % p + len08 R x) % p + p * ((s / (p ^ R * p)) % Q) < p * Q := by
    have a := Nat.mod_lt ((s / p ^ R) % p + len08 R x) hp
    have b := Nat.mod_lt (s / (p ^ R * p)) hQ
    calc ((s / p ^ R) % p + len08 R x) % p + p * ((s / (p ^ R * p)) % Q)
        < p + p * ((s / (p ^ R * p)) % Q) := Nat.add_lt_add_right a _
      _ = p * ((s / (p ^ R * p)) % Q + 1) := by rw [Nat.mul_succ, Nat.add_comm]
      _ ≤ p * Q := Nat.mul_le_mul_left _ b
  calc vals08 R p x + p ^ R * (((s / p ^ R) % p + len08 R x) % p + p * ((s / (p ^ R * p)) % Q))
      < p ^ R + p ^ R * (((s / p ^ R) % p + len08 R x) % p + p * ((s / (p ^ R * p)) % Q)) :=
        Nat.add_lt_add_right (vals08_lt hp x) _
    _ = p ^ R * (((s / p ^ R) % p + len08 R x) % p + p * ((s / (p ^ R * p)) % Q) + 1) := by
        rw [Nat.mul_succ, Nat.add_comm]
    _ ≤ p ^ R * (p * Q) := Nat.mul_le_mul_left _ h1

theorem κ08_lt {Rr p Q : Nat} (hQ : 0 < Q) (s : Nat) : κ08 Rr p Q s < Q := Nat.mod_lt _ hQ

/-- **`hF` at `F = Rr p`**: the states sharing the capacity's other
    elements. -/
theorem κ08_count {Rr p Q : Nat} (hRp : 0 < Rr * p) (v : Nat) :
    sumTo (Rr * (p * Q)) (fun u => indB (decide (κ08 Rr p Q u = v))) ≤ Rr * p := by
  rw [← Nat.mul_assoc, sumTo_split (Rr * p) _ Q]
  have each : ∀ q, q < Q → sumTo (Rr * p) (fun r => indB (decide (κ08 Rr p Q (r + Rr * p * q) = v))) =
      Rr * p * indB (decide (q = v)) := fun q hq => by
    refine Eq.trans (sumTo_congr _ (fun r hr => ?_)) (sumTo_const (indB (decide (q = v))) (Rr * p))
    show indB (decide (((r + Rr * p * q) / (Rr * p)) % Q = v)) = indB (decide (q = v))
    rw [Nat.add_mul_div_left _ _ hRp, Nat.div_eq_of_lt hr, Nat.zero_add, Nat.mod_eq_of_lt hq]
  rw [sumTo_congr _ (fun q hq => each q hq), ← sumTo_mul]
  calc Rr * p * sumTo Q (fun q => indB (decide (q = v))) ≤ Rr * p * 1 :=
        Nat.mul_le_mul_left _ (sumTo_indEq v Q).1
    _ = Rr * p := Nat.mul_one _

/-- **Distinct full-rate first commitments give distinct inputs.** -/
theorem inner08_hd {R p Q : Nat} (iv : Nat) {a b : Nat} (ha : a < p ^ R) (hb : b < p ^ R) (hab : a ≠ b) :
    inner08 R (p ^ R) p Q iv (R + (R + 1) * a) ≠ inner08 R (p ^ R) p Q iv (R + (R + 1) * b) := by
  have hv : ∀ c, c < p ^ R → vals08 R p (R + (R + 1) * c) = c := by
    intro c hc
    have hl : len08 R (R + (R + 1) * c) = R := by
      unfold len08; rw [Nat.add_mul_mod_self_left]; exact Nat.mod_eq_of_lt (Nat.lt_succ_self R)
    unfold vals08; rw [hl, Nat.add_mul_div_left _ _ (Nat.succ_pos R), Nat.div_eq_of_lt (Nat.lt_succ_self R),
      Nat.zero_add, Nat.mod_eq_of_lt hc]
  intro e
  have hl : ∀ c, len08 R (R + (R + 1) * c) = R := fun c => by
    unfold len08; rw [Nat.add_mul_mod_self_left]; exact Nat.mod_eq_of_lt (Nat.lt_succ_self R)
  have h := congrArg (· % p ^ R) e
  simp only [inner08, hl, Nat.add_mul_mod_self_left] at h
  rw [hv a ha, hv b hb, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h
  exact hab h

/-- **The full capacity fails `hpk2` under 0.8's length tag**: at `R = 2`,
    `p = 3`, `Q = 1`, the empty block from first element `1` and the
    one-element block `0` from first element `0` reach one input, from
    different capacities. -/
theorem inner08_full_fails :
    inner08 2 (3 ^ 2) 3 1 (9 * 1) 0 = inner08 2 (3 ^ 2) 3 1 0 1 ∧ (9 * 1) / 3 ^ 2 ≠ 0 / 3 ^ 2 := by
  decide

/-- **0.8's absorption meets `SpongeUnion`'s sponge premises** with the
    capacity's other elements as `κ`: `hin`, `hκ`, `hF` at `F = p ^ R p`,
    `hpk2`, and `hd` for full-rate first commitments. -/
theorem absorb08_sat {R p Q : Nat} (hp : 0 < p) (hQ : 0 < Q) :
    (∀ s x, inner08 R (p ^ R) p Q s x < p ^ R * (p * Q)) ∧ (∀ u, κ08 (p ^ R) p Q u < Q) ∧
      (∀ v, sumTo (p ^ R * (p * Q)) (fun u => indB (decide (κ08 (p ^ R) p Q u = v))) ≤ p ^ R * p) ∧
      (∀ s s' x x', inner08 R (p ^ R) p Q s x = inner08 R (p ^ R) p Q s' x' → κ08 (p ^ R) p Q s = κ08 (p ^ R) p Q s') ∧
      (∀ iv a b, a < p ^ R → b < p ^ R → a ≠ b →
        inner08 R (p ^ R) p Q iv (R + (R + 1) * a) ≠ inner08 R (p ^ R) p Q iv (R + (R + 1) * b)) :=
  ⟨inner08_lt hp hQ, κ08_lt hQ, κ08_count (Nat.mul_pos (Nat.pow_pos hp) hp), inner08_hpk2 hp, fun iv _ _ ha hb hab => inner08_hd iv ha hb hab⟩

end Circuit
