import Ski.ZK.LogUpSound
import Ski.ZK.Generic

/-!
# Fiat–Shamir, round by round

A non-interactive proof draws each challenge by hashing the transcript so
far.  A cheating prover may hash as often as it likes, choosing each new
input from the answers it has seen, so a round with error `ε` is no longer
one attempt at `ε`: `q` hash calls give `q` attempts.  Grinding charges
each attempt: an answer counts only with a valid proof of work, one in
`2^b` of them.

**The attempts** (`fs_attempts`).  Model the hash as a random oracle, each
call answered uniformly from `N` values, every call a fresh input.  A call
is *bad* when its answer falls in a set the prover's history so far fixes
(`bad h a`, `h` the earlier answers), at most `e` of the `N`.  Then over
all `N^q` answer sequences, those with a bad call number at most
`q · e · N^(q-1)`: a fraction `q e / N`.  This is the union bound over
adaptive attempts, proved by counting.

**Fiat–Shamir from round-by-round soundness** (assumed, not proved here).
Wrap the prover so that it also makes the hash calls the verifier makes on
its final proof, `k` more for `k` rounds.  Round-by-round soundness then
makes an accepted proof of a false statement contain a bad call: one
whose challenge takes a doomed state to one that is not, a fraction at
most `ε_r` of round `r`'s answers after grinding.  Read every round's
answers in one answer space, and `fs_attempts` bounds the forgery at
`(q + k) · max_r ε_r`.  For the LogUp round this file proves the bad
fraction (`logup_fs`): the answer is a challenge pair and a proof-of-work
outcome, and the bad answers are the pairs `logup_accept` counts with a
valid nonce, so the answer sequences of `q` calls with a bad call are a
fraction at most `q · M (W + 2) / (P^4 · 2^b)`, for tables the prover may
change at every call.  The other rounds' fractions (the constraint
combination, the out-of-domain point, FRI's commit and query phases, the
opening batch) are `p3-security`'s, assumed; `ski-air fs-budget` reports
them for each released proof.

The model's idealizations: the hash is a random oracle; each call's input
is new (a repeated call reveals nothing new); a call's answer fixes the
round's challenge and whether its proof of work is valid, jointly uniform
(Plonky3's `sample_bits` masks a field element, so a nonce is valid with
probability `(15 · 2^(27-b) + 1) / P`, a hair above `2^-b`); `efOf`
enumerates `EF`; the transcript binds the tables before the challenge; and
`logup_fs`'s side conditions (`hw`, `hP`, `hidx`, `hM`) hold at every
history.
-/

namespace Circuit

open ZKF

/-- A sum over sequences of `q` answers, each below `N`, the first answer
    outermost. -/
def seqSum (N : Nat) : Nat → (List Nat → Nat) → Nat
  | 0, f => f []
  | q + 1, f => sumTo N (fun a => seqSum N q (fun l => f (a :: l)))

theorem seqSum_const (N c : Nat) : ∀ q, seqSum N q (fun _ => c) = N ^ q * c
  | 0 => (Nat.one_mul c).symm
  | q + 1 => by
    show sumTo N (fun _ => seqSum N q (fun _ => c)) = N ^ (q + 1) * c
    rw [seqSum_const N c q, sumTo_const, Nat.pow_succ, Nat.mul_comm (N ^ q) N, Nat.mul_assoc]

theorem seqSum_mono (N : Nat) : ∀ q {f g : List Nat → Nat}, (∀ l, f l ≤ g l) → seqSum N q f ≤ seqSum N q g
  | 0, _, _, h => h []
  | q + 1, _, _, h => sumTo_mono N (fun a _ => seqSum_mono N q (fun l => h (a :: l)))

theorem seqSum_add (N : Nat) : ∀ q (f g : List Nat → Nat),
    seqSum N q (fun l => f l + g l) = seqSum N q f + seqSum N q g
  | 0, _, _ => rfl
  | q + 1, f, g => by
    show sumTo N (fun a => seqSum N q (fun l => f (a :: l) + g (a :: l))) = _
    rw [show (fun a => seqSum N q (fun l => f (a :: l) + g (a :: l))) =
      fun a => seqSum N q (fun l => f (a :: l)) + seqSum N q (fun l => g (a :: l)) from
      funext fun a => seqSum_add N q _ _, sumTo_add]
    rfl

/-- Some call is bad: `bad h a` for an answer `a` after the answers `h`. -/
def hit (bad : List Nat → Nat → Bool) : List Nat → List Nat → Bool
  | _, [] => false
  | h, a :: l => bad h a || hit bad (h ++ [a]) l

theorem sumTo_mul_r (a : Nat) (f : Nat → Nat) : ∀ n, sumTo n f * a = sumTo n (fun c => f c * a)
  | 0 => Nat.zero_mul a
  | n + 1 => by
    show (sumTo n f + f n) * a = sumTo n (fun c => f c * a) + f n * a
    rw [Nat.add_mul, sumTo_mul_r a f n]

theorem indB_or (x y : Bool) : indB (x || y) ≤ indB x + indB y := by
  cases x <;> cases y <;> decide

/-- **Adaptive attempts.**  If every call's bad set has at most `e` of the
    `N` answers, whatever came before, the answer sequences with a bad call
    among `q` are at most `q e N^(q-1)` of the `N^q`. -/
theorem fs_attempts (N e : Nat) (bad : List Nat → Nat → Bool)
    (hb : ∀ h, sumTo N (fun a => indB (bad h a)) ≤ e) :
    ∀ q h, seqSum N q (fun l => indB (hit bad h l)) * N ≤ q * e * N ^ q
  | 0, _ => by
    show 0 * N ≤ 0 * e * N ^ 0
    rw [Nat.zero_mul, Nat.zero_mul, Nat.zero_mul]
    exact Nat.le_refl 0
  | q + 1, h => by
    have step : ∀ a, seqSum N q (fun l => indB (hit bad h (a :: l))) ≤
        N ^ q * indB (bad h a) + seqSum N q (fun l => indB (hit bad (h ++ [a]) l)) := by
      intro a
      rw [← seqSum_const N (indB (bad h a)) q, ← seqSum_add]
      exact seqSum_mono N q (fun l => indB_or _ _)
    have ih := fun a => fs_attempts N e bad hb q (h ++ [a])
    calc seqSum N (q + 1) (fun l => indB (hit bad h l)) * N
        = sumTo N (fun a => seqSum N q (fun l => indB (hit bad h (a :: l)))) * N := rfl
      _ ≤ sumTo N (fun a => N ^ q * indB (bad h a) + seqSum N q (fun l => indB (hit bad (h ++ [a]) l))) * N :=
          Nat.mul_le_mul_right N (sumTo_mono N (fun a _ => step a))
      _ = N ^ q * sumTo N (fun a => indB (bad h a)) * N +
            sumTo N (fun a => seqSum N q (fun l => indB (hit bad (h ++ [a]) l)) * N) := by
          rw [sumTo_add, sumTo_mul_left, Nat.add_mul, sumTo_mul_r]
      _ ≤ N ^ q * e * N + sumTo N (fun _ => q * e * N ^ q) :=
          Nat.add_le_add (Nat.mul_le_mul_right N (Nat.mul_le_mul_left _ (hb h)))
            (sumTo_mono N (fun a _ => ih a))
      _ = (q + 1) * e * N ^ (q + 1) := by
          rw [sumTo_const, Nat.pow_succ]
          generalize N ^ q = Y
          have e1 : Y * e * N = e * (Y * N) := by
            rw [Nat.mul_right_comm, Nat.mul_comm]
          have e2 : N * (q * e * Y) = q * e * (Y * N) := by
            rw [Nat.mul_comm N, Nat.mul_assoc (q * e) Y N]
          rw [e1, e2, Nat.succ_mul q e, Nat.add_mul, Nat.add_comm]

-- ---------------------------------------------------------------------------
-- Grinding
-- ---------------------------------------------------------------------------

/-- A sum over `T · G` answers, as `T` challenges times `G` nonce outcomes. -/
theorem sumTo_pair (G : Nat) (f : Nat → Nat) : ∀ T, sumTo (T * G) f = sumTo T (fun t => sumTo G (fun g => f (t * G + g)))
  | 0 => by rw [Nat.zero_mul]; rfl
  | T + 1 => by
    rw [Nat.succ_mul, sumTo_app, sumTo_pair G f T]
    rfl

theorem sumTo_at_zero (c : Nat) : ∀ G, 0 < G → sumTo G (fun g => if g = 0 then c else 0) = c
  | 1, _ => by show 0 + (if 0 = 0 then c else 0) = c; rw [if_pos rfl, Nat.zero_add]
  | G + 2, _ => by
    show sumTo (G + 1) _ + (if G + 1 = 0 then c else 0) = c
    rw [if_neg (Nat.succ_ne_zero G), Nat.add_zero]
    exact sumTo_at_zero c (G + 1) (Nat.zero_lt_succ G)

/-- **Grinding**: an answer counts only when its nonce part is valid, one
    in `G` of them, so the bad answers among `T · G` number no more than
    the bad challenges among `T`. -/
theorem grind_count (G T e : Nat) (hG : 0 < G) (acc : Nat → Bool)
    (hacc : sumTo T (fun t => indB (acc t)) ≤ e) :
    sumTo (T * G) (fun a => indB (decide (a % G = 0) && acc (a / G))) ≤ e := by
  rw [sumTo_pair]
  refine Nat.le_trans (Nat.le_of_eq (sumTo_congr T (fun t _ => ?_))) hacc
  rw [← sumTo_at_zero (indB (acc t)) G hG]
  refine sumTo_congr G (fun g hg => ?_)
  have hm : (t * G + g) % G = g := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hg]
  have hd : (t * G + g) / G = t := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hG, Nat.div_eq_of_lt hg, Nat.zero_add]
  rw [hm, hd]
  by_cases h0 : g = 0
  · rw [if_pos h0, decide_eq_true h0]; rfl
  · rw [if_neg h0, decide_eq_false h0]; rfl

-- ---------------------------------------------------------------------------
-- The LogUp round under Fiat–Shamir
-- ---------------------------------------------------------------------------

section
variable (idx : String → Nat) (W : Nat) (wd : String → Nat)

/-- The LogUp check passes for the tables `ts` at the challenge pair coded
    by `t < Q4 · Q4`: `α = efOf (t % Q4)`, `β = efOf (t / Q4)`. -/
def logupPass (ts : List (AirD × Table)) (t : Nat) : Bool :=
  Aborts (prefixOf (efOf (t % Q4)) (boff idx W (efOf (t / Q4)))) (efOf (t / Q4)) ts ||
    decide (sumL (fun p => terminal (prefixOf (efOf (t % Q4)) (boff idx W (efOf (t / Q4)))) (efOf (t / Q4))
      p.1 p.2) ts = EF.zero)

/-- **The LogUp round under Fiat–Shamir.**  Each hash call answers a
    challenge pair and a nonce outcome (`Q4 · Q4 · G` answers, `G = 2^b`
    for `b` bits of grinding).  After any history `h` the prover commits
    tables `ts h` of at most `M` messages; `u h` flags calls whose tables
    do not balance (`u h → ¬ Balanced`), and a flagged call is bad when its
    tables pass the check with a valid nonce.  Over `q` calls, the answer
    sequences with a bad call are at most a fraction
    `q · M (W + 2) / (P^4 · G)`. -/
theorem logup_fs (M G : Nat) (hG : 0 < G) (ts : List Nat → List (AirD × Table)) (u : List Nat → Bool)
    (hw : ∀ h, ∀ e ∈ allEntries (ts h), e.1.2.length = wd e.1.1 ∧ wd e.1.1 ≤ W)
    (hP : ∀ h, ∀ e ∈ allEntries (ts h), idx e.1.1 + 1 < P)
    (hidx : ∀ h, ∀ e ∈ allEntries (ts h), ∀ e' ∈ allEntries (ts h), idx e.1.1 = idx e'.1.1 → e.1.1 = e'.1.1)
    (hb : ∀ h, u h = true → ¬ Balanced (ts h)) (hM : ∀ h, (allEntries (ts h)).length ≤ M) (q : Nat) :
    seqSum (Q4 * Q4 * G) q (fun l => indB (hit (fun h a => u h && (decide (a % G = 0) &&
        logupPass idx W (ts h) (a / G))) [] l)) * (Q4 * Q4 * G) ≤
      q * (Q4 * (M * W) + 2 * (Q4 * M)) * (Q4 * Q4 * G) ^ q := by
  refine fs_attempts (Q4 * Q4 * G) _ _ (fun h => ?_) q []
  cases hu : u h with
  | false =>
    show sumTo (Q4 * Q4 * G) (fun a => indB (false && _)) ≤ _
    refine Nat.le_trans (Nat.le_of_eq ((sumTo_congr _ (fun a _ => rfl)).trans
      (by rw [sumTo_const, Nat.mul_zero] : sumTo (Q4 * Q4 * G) (fun _ => 0) = 0))) (Nat.zero_le _)
  | true =>
  show sumTo (Q4 * Q4 * G) (fun a => indB (true && _)) ≤ _
  refine grind_count G (Q4 * Q4) _ hG _ ?_
  -- the pairs, `β` outer, `α` inner, as `logup_accept` counts them
  rw [Nat.mul_comm Q4 Q4, sumTo_pair]
  have hs := logup_accept idx W wd (ts h) (hw h) (hP h) (hidx h) (hb h hu)
  refine Nat.le_trans (Nat.le_of_eq (sumTo_congr Q4 (fun j _ => sumTo_congr Q4 (fun i hi => ?_)))) (Nat.le_trans hs ?_)
  · have hm : (j * Q4 + i) % Q4 = i := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hi]
    have hd : (j * Q4 + i) / Q4 = j := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.lt_of_le_of_lt (Nat.zero_le i) hi),
        Nat.div_eq_of_lt hi, Nat.zero_add]
    show indB (logupPass idx W (ts h) (j * Q4 + i)) = _
    unfold logupPass indB
    rw [hm, hd]
  · exact Nat.add_le_add (Nat.mul_le_mul_left Q4 (Nat.mul_le_mul_right W (hM h)))
      (Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left Q4 (hM h)))

end

end Circuit
