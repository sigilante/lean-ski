import Ski.ZK.FSOpenInst

/-!
# Fiat–Shamir over two rounds

A later round's challenge is hashed from a later message, which the real
prover computes after the earlier challenge and before its own.  The
simulator may compute it after drawing the challenge it will program
(`fs_zkc`): it draws the challenges, simulates, commits, and sets the
oracle at each commitment to its challenge.  Two rounds hash into two
oracle tables, independent as a domain-separated oracle's are (`fs_zk2`):
the real proof draws `c₁ = H₁(m₁)` and `c₂ = H₂(m₂ c₁)`; reprogramming
the second table at each first table, then the first, turns the real
count into the public-coin count at every pair of tables, and the
public-coin simulation does the rest.
-/

namespace Circuit

open ZKF

/-- **Fiat–Shamir with the simulator's message chosen after the
    challenge**: `fs_zk` with `smsg` reading the challenge. -/
theorem fs_zkc {X Vw : Type} {K n ε : Nat} (hK : 0 < K) (sm : (X → Nat) → Nat)
    (hsm : ∀ (N : Nat) (f : Nat → X → Nat), sm (fun x => sumTo N (fun i => f i x)) = sumTo N (fun i => sm (f i)))
    (msg : X → Nat) (smsg : Nat → X → Nat) (hmsg : ∀ x, msg x < n) (rv sv : Nat → X → Vw) (gd : Nat → Bool)
    (h : ∀ F : Nat → Nat → Vw → Bool,
      sumTo K (fun c => sm (fun x => indB (gd c && F c (msg x) (rv c x)))) ≤
        sumTo K (fun c => sm (fun x => indB (gd c && F c (smsg c x) (sv c x)))) + ε)
    (E : Nat → Nat → Nat → Vw → Bool) :
    K * sumTo (K ^ n) (fun H => sm (fun x => indB (gd (rget K (msg x) H) && E H (msg x) (rget K (msg x) H)
      (rv (rget K (msg x) H) x)))) ≤
      sumTo (K ^ n) (fun H => sumTo K (fun c => sm (fun x => indB (gd c && E (rset K (smsg c x) H c) (smsg c x) c
        (sv c x))))) + K ^ n * ε := by
  rw [fs_real hK sm hsm msg hmsg rv (fun H m c v => gd c && E H m c v)]
  calc sumTo (K ^ n) (fun H => sumTo K (fun c => sm (fun x => indB (gd c && E (rset K (msg x) H c) (msg x) c (rv c x)))))
      ≤ sumTo (K ^ n) (fun H => sumTo K (fun c => sm (fun x => indB (gd c && E (rset K (smsg c x) H c) (smsg c x) c
          (sv c x)))) + ε) :=
        sumTo_mono _ (fun H _ => h (fun c m v => E (rset K m H c) m c v))
    _ = _ := by rw [sumTo_add, sumTo_const]

/-- **Fiat–Shamir over two rounds**, two independent oracle tables: the
    real proof's first message `m₁ x`, its first challenge `c₁ = H₁(m₁)`,
    its second message `m₂ c₁ x`, its second challenge `c₂ = H₂(m₂)` and
    its view `rv c₁ c₂ x`; the simulator's messages and view read both
    challenges.  `K₁ K₂` times the real count is within
    `K₁^n₁ K₂^n₂ ε` of the simulator's, which programs both tables. -/
theorem fs_zk2 {X Vw : Type} {K1 K2 n1 n2 ε : Nat} (hK1 : 0 < K1) (hK2 : 0 < K2) (sm : (X → Nat) → Nat)
    (hsm : ∀ (N : Nat) (f : Nat → X → Nat), sm (fun x => sumTo N (fun i => f i x)) = sumTo N (fun i => sm (f i)))
    (m1 : X → Nat) (m2 : Nat → X → Nat) (hm1 : ∀ x, m1 x < n1) (hm2 : ∀ c x, m2 c x < n2)
    (s1 s2 : Nat → Nat → X → Nat) (rv sv : Nat → Nat → X → Vw) (gd : Nat → Nat → Bool)
    (h : ∀ F : Nat → Nat → Nat → Nat → Vw → Bool,
      sumTo K1 (fun c1 => sumTo K2 (fun c2 => sm (fun x => indB (gd c1 c2 && F c1 c2 (m1 x) (m2 c1 x) (rv c1 c2 x))))) ≤
        sumTo K1 (fun c1 => sumTo K2 (fun c2 => sm (fun x =>
          indB (gd c1 c2 && F c1 c2 (s1 c1 c2 x) (s2 c1 c2 x) (sv c1 c2 x))))) + ε)
    (E : Nat → Nat → Nat → Nat → Vw → Bool) :
    K1 * (K2 * sumTo (K1 ^ n1) (fun H1 => sumTo (K2 ^ n2) (fun H2 => sm (fun x =>
      indB (gd (rget K1 (m1 x) H1) (rget K2 (m2 (rget K1 (m1 x) H1) x) H2) &&
        E H1 H2 (m1 x) (m2 (rget K1 (m1 x) H1) x)
          (rv (rget K1 (m1 x) H1) (rget K2 (m2 (rget K1 (m1 x) H1) x) H2) x)))))) ≤
    sumTo (K1 ^ n1) (fun H1 => sumTo (K2 ^ n2) (fun H2 => sumTo K1 (fun c1 => sumTo K2 (fun c2 => sm (fun x =>
      indB (gd c1 c2 && E (rset K1 (s1 c1 c2 x) H1 c1) (rset K2 (s2 c1 c2 x) H2 c2) (s1 c1 c2 x) (s2 c1 c2 x)
        (sv c1 c2 x))))))) + K1 ^ n1 * (K2 ^ n2 * ε) := by
  -- the inner round, at each first table
  have inner : ∀ H1, K2 * sumTo (K2 ^ n2) (fun H2 => sm (fun x =>
      indB (gd (rget K1 (m1 x) H1) (rget K2 (m2 (rget K1 (m1 x) H1) x) H2) &&
        E H1 H2 (m1 x) (m2 (rget K1 (m1 x) H1) x)
          (rv (rget K1 (m1 x) H1) (rget K2 (m2 (rget K1 (m1 x) H1) x) H2) x)))) =
      sumTo (K2 ^ n2) (fun H2 => sumTo K2 (fun c2 => sm (fun x =>
        indB (gd (rget K1 (m1 x) H1) c2 && E H1 (rset K2 (m2 (rget K1 (m1 x) H1) x) H2 c2) (m1 x)
          (m2 (rget K1 (m1 x) H1) x) (rv (rget K1 (m1 x) H1) c2 x))))) := fun H1 =>
    fs_real (Vw := Nat × Nat × Vw) hK2 sm hsm (fun x => m2 (rget K1 (m1 x) H1) x) (fun x => hm2 _ x)
      (fun c2 x => (m1 x, rget K1 (m1 x) H1, rv (rget K1 (m1 x) H1) c2 x))
      (fun H2 mm c2 w => gd w.2.1 c2 && E H1 H2 w.1 mm w.2.2)
  -- the outer round, the second table and challenge summed beside the randomness
  let sm' : (Nat × Nat × X → Nat) → Nat := fun g =>
    sumTo (K2 ^ n2) (fun H2 => sumTo K2 (fun c2 => sm (fun x => g (H2, c2, x))))
  have hsm' : ∀ (N : Nat) (f : Nat → Nat × Nat × X → Nat),
      sm' (fun y => sumTo N (fun i => f i y)) = sumTo N (fun i => sm' (f i)) := fun N f => by
    show sumTo (K2 ^ n2) (fun H2 => sumTo K2 (fun c2 => sm (fun x => sumTo N (fun i => f i (H2, c2, x))))) =
      sumTo N (fun i => sumTo (K2 ^ n2) (fun H2 => sumTo K2 (fun c2 => sm (fun x => f i (H2, c2, x)))))
    simp only [hsm N]
    have e1 : ∀ H2, sumTo K2 (fun c2 => sumTo N (fun i => sm (fun x => f i (H2, c2, x)))) =
        sumTo N (fun i => sumTo K2 (fun c2 => sm (fun x => f i (H2, c2, x)))) := fun H2 => sumTo_exch _ N K2
    rw [sumTo_congr _ (fun H2 _ => e1 H2)]
    exact sumTo_exch _ N (K2 ^ n2)
  have outer := fs_real (X := Nat × Nat × X) (Vw := Nat × Nat × Nat × Vw) hK1 sm' hsm' (fun y => m1 y.2.2)
    (fun y => hm1 _) (fun c1 y => (y.1, y.2.1, m2 c1 y.2.2, rv c1 y.2.1 y.2.2))
    (fun H1 mm c1 w => gd c1 w.2.1 && E H1 (rset K2 w.2.2.1 w.1 w.2.1) mm w.2.2.1 w.2.2.2)
  have step1 : K1 * (K2 * sumTo (K1 ^ n1) (fun H1 => sumTo (K2 ^ n2) (fun H2 => sm (fun x =>
      indB (gd (rget K1 (m1 x) H1) (rget K2 (m2 (rget K1 (m1 x) H1) x) H2) &&
        E H1 H2 (m1 x) (m2 (rget K1 (m1 x) H1) x)
          (rv (rget K1 (m1 x) H1) (rget K2 (m2 (rget K1 (m1 x) H1) x) H2) x)))))) =
      sumTo (K1 ^ n1) (fun H1 => sumTo (K2 ^ n2) (fun H2 => sumTo K1 (fun c1 => sumTo K2 (fun c2 => sm (fun x =>
        indB (gd c1 c2 && E (rset K1 (m1 x) H1 c1) (rset K2 (m2 c1 x) H2 c2) (m1 x) (m2 c1 x) (rv c1 c2 x))))))) := by
    rw [sumTo_mul, sumTo_congr _ (fun H1 _ => inner H1)]
    refine Eq.trans outer ?_
    refine sumTo_congr _ (fun H1 _ => ?_)
    show sumTo K1 (fun c1 => sumTo (K2 ^ n2) (fun H2 => sumTo K2 (fun c2 => sm (fun x => _)))) = _
    rw [sumTo_exch _ (K2 ^ n2) K1]
  rw [step1]
  calc sumTo (K1 ^ n1) (fun H1 => sumTo (K2 ^ n2) (fun H2 => sumTo K1 (fun c1 => sumTo K2 (fun c2 => sm (fun x =>
        indB (gd c1 c2 && E (rset K1 (m1 x) H1 c1) (rset K2 (m2 c1 x) H2 c2) (m1 x) (m2 c1 x) (rv c1 c2 x)))))))
      ≤ sumTo (K1 ^ n1) (fun H1 => sumTo (K2 ^ n2) (fun H2 => sumTo K1 (fun c1 => sumTo K2 (fun c2 => sm (fun x =>
        indB (gd c1 c2 && E (rset K1 (s1 c1 c2 x) H1 c1) (rset K2 (s2 c1 c2 x) H2 c2) (s1 c1 c2 x) (s2 c1 c2 x)
          (sv c1 c2 x))))) + ε)) :=
        sumTo_mono _ (fun H1 _ => sumTo_mono _ (fun H2 _ =>
          h (fun c1 c2 a b v => E (rset K1 a H1 c1) (rset K2 b H2 c2) a b v)))
    _ = _ := by
      simp only [sumTo_add, sumTo_const]

end Circuit
