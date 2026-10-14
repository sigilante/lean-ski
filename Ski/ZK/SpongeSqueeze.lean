import Ski.ZK.SpongeAlign

/-!
# Plonky3 0.8's empty-buffer squeeze

When a phase draws more than `RATE` elements, 0.8's `duplexing` permutes
an empty buffer: the state goes to the permutation unchanged, the rate
kept and no length added (`p3-challenger-0.8.0`, `duplex_challenger.rs`).
The bench's lookup phase does so (`1 + 4 + 4 = 9` elements drawn at
`GRIND_LOOKUP = 5`).  Here a block `SQ` beyond the absorbing blocks
models it (`inner08s`).

- **`hpk2` survives.** 0.8's absorption keeps the capacity's tail
  (`κ08_inner08`), so an input equal to a state forces that state's tail
  to be the absorbing state's; with the squeeze, `κ08` still meets
  `hpk2`, and `hin` (`inner08s_hpk2`, `inner08s_lt`).
- **`hdx` fails.** One squeeze sends two states to two first positions:
  each state is its own input (`inner08s_hdx_fails`).  `SpongeRoot`'s
  count of unpaid merges, one per step, rests on `hdx`.

So with squeezes the label argument leaves a squeeze landing exactly on a
first position unpaid, one per such landing rather than one per step.
Charging it to the near-collision with the state before the first
commitment, which it implies, may also pay a merge with the prefix and
halve the exponent; a sound bound needs exact landings counted apart
from near-collisions.  Not done here.
-/

set_option autoImplicit false

namespace Circuit
open ZKF

/-- **0.8's step with the squeeze**: block `SQ` permutes the state as it
    is; any other block absorbs as `inner08`. -/
def inner08s (R Rr p Q SQ : Nat) (s x : Nat) : Nat :=
  if x = SQ then s % (Rr * (p * Q)) else inner08 R Rr p Q s x

/-- **0.8's absorption keeps the capacity's tail.** -/
theorem κ08_inner08 {R p Q : Nat} (hR : 0 < R) (hp : 0 < p) (s x : Nat) :
    κ08 (p ^ R) p Q (inner08 R (p ^ R) p Q s x) = κ08 (p ^ R) p Q s := by
  unfold κ08
  rw [inner08_div hR hp, Nat.mod_mod]

/-- `s % (a Q) / a = (s / a) % Q`, without choice. -/
theorem mod_mul_div_eq (s a Q : Nat) (hQ : 0 < Q) : s % (a * Q) / a = s / a % Q := by
  rcases Nat.eq_zero_or_pos a with h0 | ha
  · subst h0; simp
  have hlt : s % (a * Q) / a < Q := (Nat.div_lt_iff_lt_mul ha).2 (by
    rw [Nat.mul_comm Q a]; exact Nat.mod_lt _ (Nat.mul_pos ha hQ))
  have e : s / a = s % (a * Q) / a + Q * (s / (a * Q)) := by
    conv => lhs; rw [← Nat.mod_add_div s (a * Q)]
    rw [show a * Q * (s / (a * Q)) = a * (Q * (s / (a * Q))) by rw [Nat.mul_assoc], Nat.add_mul_div_left _ _ ha]
  rw [e, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]

theorem κ08_mod {Rr p Q : Nat} (hQ : 0 < Q) (s : Nat) : κ08 Rr p Q (s % (Rr * (p * Q))) = κ08 Rr p Q s := by
  unfold κ08
  rw [← Nat.mul_assoc, mod_mul_div_eq s (Rr * p) Q hQ, Nat.mod_mod]

/-- **The squeeze keeps `hpk2`**: equal inputs come from states with equal
    tails, whichever of them squeezes. -/
theorem inner08s_hpk2 {R p Q SQ : Nat} (hR : 0 < R) (hp : 0 < p) (hQ : 0 < Q) :
    ∀ s s' x x', inner08s R (p ^ R) p Q SQ s x = inner08s R (p ^ R) p Q SQ s' x' →
      κ08 (p ^ R) p Q s = κ08 (p ^ R) p Q s' := by
  intro s s' x x' e
  have k := congrArg (κ08 (p ^ R) p Q) e
  unfold inner08s at k
  split at k <;> split at k <;>
    simp only [κ08_mod hQ, κ08_inner08 hR hp] at k <;> exact k

theorem inner08s_lt {R p Q SQ : Nat} (hR : 0 < R) (hp : 0 < p) (hQ : 0 < Q) (s x : Nat) :
    inner08s R (p ^ R) p Q SQ s x < p ^ R * (p * Q) := by
  unfold inner08s; split
  · exact Nat.mod_lt _ (Nat.mul_pos (Nat.pow_pos hp) (Nat.mul_pos hp hQ))
  · exact inner08_lt hR hp hQ s x

/-- **The squeeze breaks `hdx`**: at `R = 1`, `p = 2`, `Q = 1`, `SQ = 9`,
    the states `2` and `3`, squeezed, are the first positions of
    commitments `0` and `1` from state `0`. -/
theorem inner08s_hdx_fails :
    inner08s 1 (2 ^ 1) 2 1 9 2 9 = inner08s 1 (2 ^ 1) 2 1 9 0 0 ∧
      inner08s 1 (2 ^ 1) 2 1 9 3 9 = inner08s 1 (2 ^ 1) 2 1 9 0 1 := by
  decide

end Circuit
