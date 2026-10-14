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
  below `Q`.  A block `x < p ^ R` is a full-rate block whose values are
  `x`; a larger `x` carries between `1` and `R` elements (`len08`,
  `vals08`).  No block is empty: 0.8 permutes an empty buffer as a squeeze,
  leaving the rate and adding no tag.  `inner08` writes the values,
  zero-filled to the rate, and adds the length to the first capacity
  element modulo `p`.
- **The capacity fails `hpk2`.** The length tag lets a short block from
  one capacity and a longer block from another give one input: with
  `R = 2` and `p = 3`, the one-element block `1` from first element `1`
  and the two-element block `1 ‖ 0` from first element `0` both reach
  input `19` (`inner08_full_fails`).
- **The rest of the capacity meets it.** Dividing the input by `Rr · p`
  recovers the capacity's other elements whatever the block, so `κ08`,
  those elements alone, meets `hpk2` (`inner08_hpk2`), with `hin`
  (`inner08_lt`) and `hF` at `F = Rr · p`, the states sharing them
  (`κ08_count`).  At BabyBear width 16 and rate 8, `F / K` is
  `1 / p ^ 7`, one field element less than the full capacity's `1 / p ^ 8`.
- **First commitments stay apart.** Distinct first commitments below
  `p ^ R`, full-rate blocks of their own values, give distinct inputs
  from any state (`inner08_hd`), the form `SpongeUnion`'s `hd` takes for
  raw commitments `a, b < n1 ≤ p ^ R`.

`SpongeUnion`'s composites take `inner`, `κ`, `hin`, `hF`, `hpk2` and `hd`
as parameters, and `inner08`, `κ08` meet them (`absorb08_sat`).  The other
premises stay as `SpongeUnion` states them: the tags `h0`, `hnz`, which
0.8 does not provide (a tag `τ` can read only the values, since the
length enters the capacity); the state `iv` fixed before the permutation,
where batch-stark absorbs a domain separator first; and block alignment:
0.8's `observe` buffers elements and permutes at `RATE` of them or at a
squeeze, so a first commitment fills one block only when the buffer is
empty before it.
-/

set_option autoImplicit false

namespace Circuit
open ZKF

/-- The length of block `x`: `R` for `x < p ^ R`, a full-rate block whose
    values are `x`; else between `1` and `R`. -/
def len08 (R p x : Nat) : Nat := if x < p ^ R then R else (x - p ^ R) % R + 1

/-- The values of block `x`, `len08 R p x` field elements. -/
def vals08 (R p x : Nat) : Nat := if x < p ^ R then x else ((x - p ^ R) / R) % p ^ len08 R p x

/-- **0.8's absorption**: the block's values zero-filled to the rate, its
    length added to the first capacity element. -/
def inner08 (R Rr p Q : Nat) (s x : Nat) : Nat :=
  vals08 R p x + Rr * (((s / Rr) % p + len08 R p x) % p + p * ((s / (Rr * p)) % Q))

/-- The capacity's elements after the first. -/
def κ08 (Rr p Q : Nat) (s : Nat) : Nat := (s / (Rr * p)) % Q

theorem vals08_lt {R p : Nat} (hR : 0 < R) (hp : 0 < p) (x : Nat) : vals08 R p x < p ^ R := by
  unfold vals08
  by_cases hx : x < p ^ R
  · rw [if_pos hx]; exact hx
  · rw [if_neg hx]
    refine Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.pow_pos hp)) (Nat.pow_le_pow_right hp ?_)
    unfold len08; rw [if_neg hx]
    exact Nat.succ_le_of_lt (Nat.mod_lt _ hR)

/-- The input splits as values, first capacity element and the rest. -/
theorem inner08_div {R p Q : Nat} (hR : 0 < R) (hp : 0 < p) (s x : Nat) :
    inner08 R (p ^ R) p Q s x / (p ^ R * p) = (s / (p ^ R * p)) % Q := by
  have hRr : 0 < p ^ R := Nat.pow_pos hp
  unfold inner08
  rw [← Nat.div_div_eq_div_mul, Nat.add_mul_div_left _ _ hRr, Nat.div_eq_of_lt (vals08_lt hR hp x), Nat.zero_add,
    Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt (Nat.mod_lt _ hp), Nat.zero_add]

/-- **The rest of the capacity meets `hpk2`.** -/
theorem inner08_hpk2 {R p Q : Nat} (hR : 0 < R) (hp : 0 < p) :
    ∀ s s' x x', inner08 R (p ^ R) p Q s x = inner08 R (p ^ R) p Q s' x' → κ08 (p ^ R) p Q s = κ08 (p ^ R) p Q s' := by
  intro s s' x x' e
  have h := congrArg (· / (p ^ R * p)) e
  simp only [inner08_div hR hp] at h
  exact h

/-- Inputs stay below the state count. -/
theorem inner08_lt {R p Q : Nat} (hR : 0 < R) (hp : 0 < p) (hQ : 0 < Q) (s x : Nat) :
    inner08 R (p ^ R) p Q s x < p ^ R * (p * Q) := by
  have hRr : 0 < p ^ R := Nat.pow_pos hp
  unfold inner08
  have h1 : ((s / p ^ R) % p + len08 R p x) % p + p * ((s / (p ^ R * p)) % Q) < p * Q := by
    have a := Nat.mod_lt ((s / p ^ R) % p + len08 R p x) hp
    have b := Nat.mod_lt (s / (p ^ R * p)) hQ
    calc ((s / p ^ R) % p + len08 R p x) % p + p * ((s / (p ^ R * p)) % Q)
        < p + p * ((s / (p ^ R * p)) % Q) := Nat.add_lt_add_right a _
      _ = p * ((s / (p ^ R * p)) % Q + 1) := by rw [Nat.mul_succ, Nat.add_comm]
      _ ≤ p * Q := Nat.mul_le_mul_left _ b
  calc vals08 R p x + p ^ R * (((s / p ^ R) % p + len08 R p x) % p + p * ((s / (p ^ R * p)) % Q))
      < p ^ R + p ^ R * (((s / p ^ R) % p + len08 R p x) % p + p * ((s / (p ^ R * p)) % Q)) :=
        Nat.add_lt_add_right (vals08_lt hR hp x) _
    _ = p ^ R * (((s / p ^ R) % p + len08 R p x) % p + p * ((s / (p ^ R * p)) % Q) + 1) := by
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

/-- **Distinct full-rate first commitments give distinct inputs**: a
    first commitment below `p ^ R` is a full-rate block of its own value. -/
theorem inner08_hd {R p Q : Nat} (iv : Nat) {a b : Nat} (ha : a < p ^ R) (hb : b < p ^ R) (hab : a ≠ b) :
    inner08 R (p ^ R) p Q iv a ≠ inner08 R (p ^ R) p Q iv b := by
  have hv : ∀ c, c < p ^ R → vals08 R p c = c := fun c hc => by unfold vals08; rw [if_pos hc]
  have hl : ∀ c, c < p ^ R → len08 R p c = R := fun c hc => by unfold len08; rw [if_pos hc]
  intro e
  have h := congrArg (· % p ^ R) e
  simp only [inner08, hl a ha, hl b hb, Nat.add_mul_mod_self_left] at h
  rw [hv a ha, hv b hb, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h
  exact hab h

/-- **The full capacity fails `hpk2` under 0.8's length tag**: at `R = 2`,
    `p = 3`, `Q = 1`, the one-element block `1` (encoded `11`) from first
    capacity element `1` and the two-element block `1 ‖ 0` (encoded `1`)
    from first element `0` both reach input `19`, from different
    capacities. -/
theorem inner08_full_fails :
    inner08 2 (3 ^ 2) 3 1 9 11 = inner08 2 (3 ^ 2) 3 1 0 1 ∧ 9 / 3 ^ 2 ≠ 0 / 3 ^ 2 := by
  decide

/-- **0.8's absorption meets `SpongeUnion`'s sponge premises** with the
    capacity's other elements as `κ`: `hin`, `hκ`, `hF` at `F = p ^ R p`,
    `hpk2`, and `hd` for full-rate first commitments. -/
theorem absorb08_sat {R p Q : Nat} (hR : 0 < R) (hp : 0 < p) (hQ : 0 < Q) :
    (∀ s x, inner08 R (p ^ R) p Q s x < p ^ R * (p * Q)) ∧ (∀ u, κ08 (p ^ R) p Q u < Q) ∧
      (∀ v, sumTo (p ^ R * (p * Q)) (fun u => indB (decide (κ08 (p ^ R) p Q u = v))) ≤ p ^ R * p) ∧
      (∀ s s' x x', inner08 R (p ^ R) p Q s x = inner08 R (p ^ R) p Q s' x' → κ08 (p ^ R) p Q s = κ08 (p ^ R) p Q s') ∧
      (∀ iv a b, a < p ^ R → b < p ^ R → a ≠ b →
        inner08 R (p ^ R) p Q iv a ≠ inner08 R (p ^ R) p Q iv b) :=
  ⟨inner08_lt hR hp hQ, κ08_lt hQ, κ08_count (Nat.mul_pos (Nat.pow_pos hp) hp), inner08_hpk2 hR hp, fun iv _ _ ha hb hab => inner08_hd iv ha hb hab⟩

end Circuit
