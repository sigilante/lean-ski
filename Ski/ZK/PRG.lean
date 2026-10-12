import Ski.ZK.TranscriptN

/-!
# The prover's randomness from one seed

The transcript theorems count over uniform randomness: the PCS's draw `r`
and the blinding tuples `t` (`transcript_zkN` and its instances).  The
prover draws both from one 128-bit seed per proof, expanded by ChaCha20
(`bench/plonky3/src/seed.rs`).  This file states what that costs.

`PRGClose C NS NR m G δ`: for every test `D` of `(r, t)` in the class `C`,
the fraction of the `NS` seeds whose expansion `G s` passes `D` is within
`δ / (NS · K)` of the fraction of the uniform `(r, t)` that do,
`K = NR · Q4^m` (as counts, cross-multiplied).

The class matters.  Over every test the hypothesis fails for any generator
with fewer seeds than draws: the test "`(r, t)` is some `G s`" passes every
seed and almost no uniform draw.  A pseudorandom generator fools the
efficient tests only, so the theorems here take the smallest class they
use, `TTests real`: the real transcript's event at fixed challenges, one
test per pair `(α, β)`.  Each runs the honest prover on the witness, so it
is efficient when the event is (`pcs` and `tv` are, for Plonky3).  That
ChaCha20 fools these tests for an efficient event is an assumption, not a
theorem, and the seeded guarantee it gives is computational: for an event
such as "the view is some seed's", the hypothesis fails.

`prg_transfer` moves the count of any event in the class from uniform
randomness to the seed's, at a cost of `δ` for each pair of challenges,
and `transcript_prg` composes it with a transcript theorem: the real
transcript under the seed is within the transcript theorem's error plus
the generator's of the simulator's.
-/

namespace Circuit

open ZKF

/-- A count over the challenges and the seeds, the draws `G s` expanded
    from the seed `s`. -/
def tsumG (NS : Nat) (G : Nat → Nat × (Nat → Tup)) (f : EF → EF → Nat → (Nat → Tup) → Nat) : Nat :=
  sumTo Q4 fun i => sumTo Q4 fun j => sumTo NS fun s => f (efOf i) (efOf j) (G s).1 (G s).2

/-- **The generator's closeness on a class of tests**: every test in `C`
    has its count over the seeds, scaled, within `δ` of its count over
    uniform draws. -/
def PRGClose (C : (Nat → (Nat → Tup) → Bool) → Prop) (NS NR m : Nat)
    (G : Nat → Nat × (Nat → Tup)) (δ : Nat) : Prop :=
  ∀ D : Nat → (Nat → Tup) → Bool, C D →
    sumTo NS (fun s => indB (D (G s).1 (G s).2)) * (NR * Q4 ^ m) ≤
      sumTo NR (fun r => sumN m (fun t => indB (D r t))) * NS + δ ∧
    sumTo NR (fun r => sumN m (fun t => indB (D r t))) * NS ≤
      sumTo NS (fun s => indB (D (G s).1 (G s).2)) * (NR * Q4 ^ m) + δ

theorem sumTo_mulR (a : Nat) (f : Nat → Nat) : ∀ n, sumTo n f * a = sumTo n (fun c => f c * a)
  | 0 => Nat.zero_mul a
  | n + 1 => by
    show (sumTo n f + f n) * a = sumTo n (fun c => f c * a) + f n * a
    rw [Nat.add_mul, sumTo_mulR a f n]

/-- Two sums of a pointwise bound `f ≤ g · a + d`. -/
theorem sumTo_bound {f g : Nat → Nat} {a d : Nat} : ∀ n, (∀ i, i < n → f i ≤ g i * a + d) →
    sumTo n f ≤ sumTo n g * a + n * d := by
  intro n h
  have h1 : sumTo n f ≤ sumTo n (fun i => g i * a + d) := sumTo_mono n h
  rw [sumTo_add, sumTo_const, ← sumTo_mulR] at h1
  exact h1

/-- The tests a transcript theorem needs of the generator: the event
    `real α β` of the draws, at each fixed pair of challenges. -/
def TTests (real : EF → EF → Nat → (Nat → Tup) → Bool) (D : Nat → (Nat → Tup) → Bool) : Prop :=
  ∃ α β, D = real α β

/-- **Seeded counts track uniform ones**: for an event of the challenges
    and draws whose every slice at fixed challenges is in the class, its
    count under the seed, scaled, is within `Q4 · Q4 · δ` of its count
    under uniform draws. -/
theorem prg_transfer {C : (Nat → (Nat → Tup) → Bool) → Prop} {NS NR m δ : Nat}
    {G : Nat → Nat × (Nat → Tup)} (hG : PRGClose C NS NR m G δ)
    (f : EF → EF → Nat → (Nat → Tup) → Bool) (hC : ∀ α β, C (f α β)) :
    tsumG NS G (fun α β r t => indB (f α β r t)) * (NR * Q4 ^ m) ≤
      tsumN NR m (fun α β r t => indB (f α β r t)) * NS + Q4 * (Q4 * δ) ∧
    tsumN NR m (fun α β r t => indB (f α β r t)) * NS ≤
      tsumG NS G (fun α β r t => indB (f α β r t)) * (NR * Q4 ^ m) + Q4 * (Q4 * δ) := by
  unfold tsumG tsumN
  constructor
  · rw [sumTo_mulR]
    refine sumTo_bound Q4 fun i _ => ?_
    rw [sumTo_mulR]
    exact sumTo_bound Q4 fun j _ => (hG (f (efOf i) (efOf j)) (hC _ _)).1
  · rw [sumTo_mulR]
    refine sumTo_bound Q4 fun i _ => ?_
    rw [sumTo_mulR]
    exact sumTo_bound Q4 fun j _ => (hG (f (efOf i) (efOf j)) (hC _ _)).2

/-- **The seeded transcript is simulatable**: a transcript theorem's bound
    between the real and the simulated counts under uniform draws carries
    to the real transcript under the seed, plus the generator's `δ` for
    each pair of challenges.  Both sides are scaled to the common
    denominator `NS · NR · Q4^m`.  The generator need fool only the
    transcript's own tests (`TTests real`). -/
theorem transcript_prg {NS NR m δ e : Nat} {G : Nat → Nat × (Nat → Tup)}
    (real sim : EF → EF → Nat → (Nat → Tup) → Bool)
    (hG : PRGClose (TTests real) NS NR m G δ)
    (hzk : tsumN NR m (fun α β r t => indB (real α β r t)) ≤
        tsumN NR m (fun α β r t => indB (sim α β r t)) + e ∧
      tsumN NR m (fun α β r t => indB (sim α β r t)) ≤
        tsumN NR m (fun α β r t => indB (real α β r t)) + e) :
    tsumG NS G (fun α β r t => indB (real α β r t)) * (NR * Q4 ^ m) ≤
        tsumN NR m (fun α β r t => indB (sim α β r t)) * NS + e * NS + Q4 * (Q4 * δ) ∧
      tsumN NR m (fun α β r t => indB (sim α β r t)) * NS ≤
        tsumG NS G (fun α β r t => indB (real α β r t)) * (NR * Q4 ^ m) + e * NS + Q4 * (Q4 * δ) := by
  obtain ⟨h1, h2⟩ := prg_transfer hG real (fun α β => ⟨α, β, rfl⟩)
  constructor
  · refine Nat.le_trans h1 (Nat.add_le_add_right ?_ _)
    rw [← Nat.add_mul]
    exact Nat.mul_le_mul_right NS hzk.1
  · have h3 : tsumN NR m (fun α β r t => indB (sim α β r t)) * NS ≤
        tsumN NR m (fun α β r t => indB (real α β r t)) * NS + e * NS := by
      rw [← Nat.add_mul]
      exact Nat.mul_le_mul_right NS hzk.2
    refine Nat.le_trans h3 ?_
    rw [Nat.add_right_comm _ (e * NS)]
    exact Nat.add_le_add_right (Nat.le_trans h2 (Nat.le_refl _)) _

end Circuit
