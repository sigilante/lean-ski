import Ski.ZK.FSOpen2Inst2

/-!
# Fiat–Shamir over three rounds

Plonky3 draws three challenges between its commitments: the LogUp
challenges after the main trace, the constraint-folding challenge after
the permutation trace, and `ζ` after the quotient.  Here the
reprogramming of `fs_zk2` is an equality of its own (`fs_real2`), applied
inside each first table for the later two rounds and then once more for
the first (`fs_real3`), and the public-coin bound finishes (`fs_zk3`).
Three oracle tables, independent as a domain-separated oracle's are.
-/

namespace Circuit

open ZKF

/-- **Two rounds reprogrammed**: `K1 K2` times the count over the two tables
    with the challenges read at the messages is the count over the tables
    and every pair of challenges, each table set at its message. -/
theorem fs_real2 {X Vw : Type} {K1 K2 n1 n2 : Nat} (hK1 : 0 < K1) (hK2 : 0 < K2) (sm : (X → Nat) → Nat)
    (hsm : ∀ (N : Nat) (f : Nat → X → Nat), sm (fun x => sumTo N (fun i => f i x)) = sumTo N (fun i => sm (f i)))
    (m1 : X → Nat) (m2 : Nat → X → Nat) (hm1 : ∀ x, m1 x < n1) (hm2 : ∀ c x, m2 c x < n2)
    (rv : Nat → Nat → X → Vw) (E : Nat → Nat → Nat → Nat → Nat → Nat → Vw → Bool) :
    K1 * (K2 * sumTo (K1 ^ n1) (fun H1 => sumTo (K2 ^ n2) (fun H2 => sm (fun x =>
      indB (E H1 H2 (rget K1 (m1 x) H1) (rget K2 (m2 (rget K1 (m1 x) H1) x) H2) (m1 x) (m2 (rget K1 (m1 x) H1) x)
          (rv (rget K1 (m1 x) H1) (rget K2 (m2 (rget K1 (m1 x) H1) x) H2) x)))))) =
    sumTo (K1 ^ n1) (fun H1 => sumTo (K2 ^ n2) (fun H2 => sumTo K1 (fun c1 => sumTo K2 (fun c2 => sm (fun x =>
      indB (E (rset K1 (m1 x) H1 c1) (rset K2 (m2 c1 x) H2 c2) c1 c2 (m1 x) (m2 c1 x) (rv c1 c2 x))))))) := by
  have inner : ∀ H1, K2 * sumTo (K2 ^ n2) (fun H2 => sm (fun x =>
      indB (E H1 H2 (rget K1 (m1 x) H1) (rget K2 (m2 (rget K1 (m1 x) H1) x) H2) (m1 x) (m2 (rget K1 (m1 x) H1) x)
          (rv (rget K1 (m1 x) H1) (rget K2 (m2 (rget K1 (m1 x) H1) x) H2) x)))) =
      sumTo (K2 ^ n2) (fun H2 => sumTo K2 (fun c2 => sm (fun x =>
        indB (E H1 (rset K2 (m2 (rget K1 (m1 x) H1) x) H2 c2) (rget K1 (m1 x) H1) c2 (m1 x)
          (m2 (rget K1 (m1 x) H1) x) (rv (rget K1 (m1 x) H1) c2 x))))) := fun H1 =>
    fs_real (Vw := Nat × Nat × Vw) hK2 sm hsm (fun x => m2 (rget K1 (m1 x) H1) x) (fun x => hm2 _ x)
      (fun c2 x => (m1 x, rget K1 (m1 x) H1, rv (rget K1 (m1 x) H1) c2 x))
      (fun H2 mm c2 w => E H1 H2 w.2.1 c2 w.1 mm w.2.2)
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
    (fun H1 mm c1 w => E H1 (rset K2 w.2.2.1 w.1 w.2.1) c1 w.2.1 mm w.2.2.1 w.2.2.2)
  rw [sumTo_mul, sumTo_congr _ (fun H1 _ => inner H1)]
  refine Eq.trans outer ?_
  refine sumTo_congr _ (fun H1 _ => ?_)
  show sumTo K1 (fun c1 => sumTo (K2 ^ n2) (fun H2 => sumTo K2 (fun c2 => sm (fun x => _)))) = _
  rw [sumTo_exch _ (K2 ^ n2) K1]

/-- **Three rounds reprogrammed.** -/
theorem fs_real3 {X Vw : Type} {K1 K2 K3 n1 n2 n3 : Nat} (hK1 : 0 < K1) (hK2 : 0 < K2) (hK3 : 0 < K3)
    (sm : (X → Nat) → Nat)
    (hsm : ∀ (N : Nat) (f : Nat → X → Nat), sm (fun x => sumTo N (fun i => f i x)) = sumTo N (fun i => sm (f i)))
    (m1 : X → Nat) (m2 : Nat → X → Nat) (m3 : Nat → Nat → X → Nat) (hm1 : ∀ x, m1 x < n1)
    (hm2 : ∀ c x, m2 c x < n2) (hm3 : ∀ c c' x, m3 c c' x < n3) (rv : Nat → Nat → Nat → X → Vw)
    (E : Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Vw → Bool) :
    K1 * (K2 * (K3 * sumTo (K1 ^ n1) (fun H1 => sumTo (K2 ^ n2) (fun H2 => sumTo (K3 ^ n3) (fun H3 => sm (fun x =>
      indB (E H1 H2 H3 (rget K1 (m1 x) H1) (rget K2 (m2 (rget K1 (m1 x) H1) x) H2)
        (rget K3 (m3 (rget K1 (m1 x) H1) (rget K2 (m2 (rget K1 (m1 x) H1) x) H2) x) H3)
        (m1 x) (m2 (rget K1 (m1 x) H1) x) (m3 (rget K1 (m1 x) H1) (rget K2 (m2 (rget K1 (m1 x) H1) x) H2) x)
        (rv (rget K1 (m1 x) H1) (rget K2 (m2 (rget K1 (m1 x) H1) x) H2)
          (rget K3 (m3 (rget K1 (m1 x) H1) (rget K2 (m2 (rget K1 (m1 x) H1) x) H2) x) H3) x)))))))) =
    sumTo (K1 ^ n1) (fun H1 => sumTo (K2 ^ n2) (fun H2 => sumTo (K3 ^ n3) (fun H3 => sumTo K1 (fun c1 =>
      sumTo K2 (fun c2 => sumTo K3 (fun c3 => sm (fun x =>
        indB (E (rset K1 (m1 x) H1 c1) (rset K2 (m2 c1 x) H2 c2) (rset K3 (m3 c1 c2 x) H3 c3) c1 c2 c3
          (m1 x) (m2 c1 x) (m3 c1 c2 x) (rv c1 c2 c3 x))))))))) := by
  -- the later two rounds, at each first table
  have inner : ∀ H1, K2 * (K3 * sumTo (K2 ^ n2) (fun H2 => sumTo (K3 ^ n3) (fun H3 => sm (fun x =>
      indB (E H1 H2 H3 (rget K1 (m1 x) H1) (rget K2 (m2 (rget K1 (m1 x) H1) x) H2)
        (rget K3 (m3 (rget K1 (m1 x) H1) (rget K2 (m2 (rget K1 (m1 x) H1) x) H2) x) H3)
        (m1 x) (m2 (rget K1 (m1 x) H1) x) (m3 (rget K1 (m1 x) H1) (rget K2 (m2 (rget K1 (m1 x) H1) x) H2) x)
        (rv (rget K1 (m1 x) H1) (rget K2 (m2 (rget K1 (m1 x) H1) x) H2)
          (rget K3 (m3 (rget K1 (m1 x) H1) (rget K2 (m2 (rget K1 (m1 x) H1) x) H2) x) H3) x)))))) =
      sumTo (K2 ^ n2) (fun H2 => sumTo (K3 ^ n3) (fun H3 => sumTo K2 (fun c2 => sumTo K3 (fun c3 => sm (fun x =>
        indB (E H1 (rset K2 (m2 (rget K1 (m1 x) H1) x) H2 c2) (rset K3 (m3 (rget K1 (m1 x) H1) c2 x) H3 c3)
          (rget K1 (m1 x) H1) c2 c3 (m1 x) (m2 (rget K1 (m1 x) H1) x) (m3 (rget K1 (m1 x) H1) c2 x)
          (rv (rget K1 (m1 x) H1) c2 c3 x))))))) := fun H1 =>
    fs_real2 (Vw := Nat × Nat × Vw) hK2 hK3 sm hsm (fun x => m2 (rget K1 (m1 x) H1) x)
      (fun c2 x => m3 (rget K1 (m1 x) H1) c2 x) (fun x => hm2 _ x) (fun _ x => hm3 _ _ x)
      (fun c2 c3 x => (m1 x, rget K1 (m1 x) H1, rv (rget K1 (m1 x) H1) c2 c3 x))
      (fun H2 H3 c2 c3 mm2 mm3 w => E H1 H2 H3 w.2.1 c2 c3 w.1 mm2 mm3 w.2.2)
  -- the first round, the later tables and challenges summed beside the randomness
  let sm' : (Nat × Nat × Nat × Nat × X → Nat) → Nat := fun g =>
    sumTo (K2 ^ n2) (fun H2 => sumTo (K3 ^ n3) (fun H3 => sumTo K2 (fun c2 => sumTo K3 (fun c3 =>
      sm (fun x => g (H2, H3, c2, c3, x))))))
  have hsm' : ∀ (N : Nat) (f : Nat → Nat × Nat × Nat × Nat × X → Nat),
      sm' (fun y => sumTo N (fun i => f i y)) = sumTo N (fun i => sm' (f i)) := fun N f => by
    show sumTo (K2 ^ n2) (fun H2 => sumTo (K3 ^ n3) (fun H3 => sumTo K2 (fun c2 => sumTo K3 (fun c3 =>
      sm (fun x => sumTo N (fun i => f i (H2, H3, c2, c3, x))))))) = _
    simp only [hsm N]
    rw [sumTo_congr _ (fun H2 _ => sumTo_congr _ (fun H3 _ => sumTo_congr _ (fun c2 _ =>
      sumTo_exch (fun c3 i => sm (fun x => f i (H2, H3, c2, c3, x))) N K3)))]
    rw [sumTo_congr _ (fun H2 _ => sumTo_congr _ (fun H3 _ =>
      sumTo_exch (fun c2 i => sumTo K3 (fun c3 => sm (fun x => f i (H2, H3, c2, c3, x)))) N K2))]
    rw [sumTo_congr _ (fun H2 _ => sumTo_exch (fun H3 i => sumTo K2 (fun c2 => sumTo K3 (fun c3 =>
      sm (fun x => f i (H2, H3, c2, c3, x))))) N (K3 ^ n3))]
    exact sumTo_exch _ N (K2 ^ n2)
  have outer := fs_real (X := Nat × Nat × Nat × Nat × X) (Vw := Nat × Nat × Nat × Nat × Nat × Nat × Vw) hK1 sm' hsm'
    (fun y => m1 y.2.2.2.2) (fun y => hm1 _)
    (fun c1 y => (y.1, y.2.1, y.2.2.1, y.2.2.2.1, m2 c1 y.2.2.2.2, m3 c1 y.2.2.1 y.2.2.2.2, rv c1 y.2.2.1 y.2.2.2.1 y.2.2.2.2))
    (fun H1 mm c1 w => E H1 (rset K2 w.2.2.2.2.1 w.1 w.2.2.1) (rset K3 w.2.2.2.2.2.1 w.2.1 w.2.2.2.1) c1 w.2.2.1
      w.2.2.2.1 mm w.2.2.2.2.1 w.2.2.2.2.2.1 w.2.2.2.2.2.2)
  rw [sumTo_mul K3 _ (K1 ^ n1), sumTo_mul K2 _ (K1 ^ n1), sumTo_congr _ (fun H1 _ => inner H1)]
  refine Eq.trans outer ?_
  refine sumTo_congr _ (fun H1 _ => ?_)
  show sumTo K1 (fun c1 => sumTo (K2 ^ n2) (fun H2 => sumTo (K3 ^ n3) (fun H3 => sumTo K2 (fun c2 =>
    sumTo K3 (fun c3 => sm (fun x => _)))))) = _
  rw [sumTo_exch _ (K2 ^ n2) K1]
  refine sumTo_congr _ (fun H2 _ => ?_)
  rw [sumTo_exch _ (K3 ^ n3) K1]

/-- **Fiat–Shamir over three rounds**, three oracle tables: the real proof's
    messages `m1 x`, `m2 c1 x`, `m3 c1 c2 x`, each challenge the table's
    answer at its message; the simulator's messages read all three
    challenges.  `K1 K2 K3` times the real count is at most the
    simulator's, which programs every table, plus `K1^n1 K2^n2 K3^n3 ε`;
    one direction only.
    One proof per oracle: each table is programmed at one point. -/
theorem fs_zk3 {X Vw : Type} {K1 K2 K3 n1 n2 n3 ε : Nat} (hK1 : 0 < K1) (hK2 : 0 < K2) (hK3 : 0 < K3)
    (sm : (X → Nat) → Nat)
    (hsm : ∀ (N : Nat) (f : Nat → X → Nat), sm (fun x => sumTo N (fun i => f i x)) = sumTo N (fun i => sm (f i)))
    (m1 : X → Nat) (m2 : Nat → X → Nat) (m3 : Nat → Nat → X → Nat) (hm1 : ∀ x, m1 x < n1)
    (hm2 : ∀ c x, m2 c x < n2) (hm3 : ∀ c c' x, m3 c c' x < n3)
    (s1 s2 s3 : Nat → Nat → Nat → X → Nat) (rv sv : Nat → Nat → Nat → X → Vw) (gd : Nat → Nat → Nat → Bool)
    (h : ∀ F : Nat → Nat → Nat → Nat → Nat → Nat → Vw → Bool,
      sumTo K1 (fun c1 => sumTo K2 (fun c2 => sumTo K3 (fun c3 => sm (fun x =>
        indB (gd c1 c2 c3 && F c1 c2 c3 (m1 x) (m2 c1 x) (m3 c1 c2 x) (rv c1 c2 c3 x)))))) ≤
      sumTo K1 (fun c1 => sumTo K2 (fun c2 => sumTo K3 (fun c3 => sm (fun x =>
        indB (gd c1 c2 c3 && F c1 c2 c3 (s1 c1 c2 c3 x) (s2 c1 c2 c3 x) (s3 c1 c2 c3 x) (sv c1 c2 c3 x)))))) + ε)
    (E : Nat → Nat → Nat → Nat → Nat → Nat → Vw → Bool) :
    K1 * (K2 * (K3 * sumTo (K1 ^ n1) (fun H1 => sumTo (K2 ^ n2) (fun H2 => sumTo (K3 ^ n3) (fun H3 => sm (fun x =>
      indB (gd (rget K1 (m1 x) H1) (rget K2 (m2 (rget K1 (m1 x) H1) x) H2)
          (rget K3 (m3 (rget K1 (m1 x) H1) (rget K2 (m2 (rget K1 (m1 x) H1) x) H2) x) H3) &&
        E H1 H2 H3 (m1 x) (m2 (rget K1 (m1 x) H1) x) (m3 (rget K1 (m1 x) H1) (rget K2 (m2 (rget K1 (m1 x) H1) x) H2) x)
          (rv (rget K1 (m1 x) H1) (rget K2 (m2 (rget K1 (m1 x) H1) x) H2)
            (rget K3 (m3 (rget K1 (m1 x) H1) (rget K2 (m2 (rget K1 (m1 x) H1) x) H2) x) H3) x)))))))) ≤
    sumTo (K1 ^ n1) (fun H1 => sumTo (K2 ^ n2) (fun H2 => sumTo (K3 ^ n3) (fun H3 => sumTo K1 (fun c1 =>
      sumTo K2 (fun c2 => sumTo K3 (fun c3 => sm (fun x =>
        indB (gd c1 c2 c3 && E (rset K1 (s1 c1 c2 c3 x) H1 c1) (rset K2 (s2 c1 c2 c3 x) H2 c2)
          (rset K3 (s3 c1 c2 c3 x) H3 c3) (s1 c1 c2 c3 x) (s2 c1 c2 c3 x) (s3 c1 c2 c3 x) (sv c1 c2 c3 x))))))))) +
      K1 ^ n1 * (K2 ^ n2 * (K3 ^ n3 * ε)) := by
  rw [fs_real3 hK1 hK2 hK3 sm hsm m1 m2 m3 hm1 hm2 hm3 rv
    (fun H1 H2 H3 c1 c2 c3 a b c v => gd c1 c2 c3 && E H1 H2 H3 a b c v)]
  calc sumTo (K1 ^ n1) (fun H1 => sumTo (K2 ^ n2) (fun H2 => sumTo (K3 ^ n3) (fun H3 => sumTo K1 (fun c1 =>
        sumTo K2 (fun c2 => sumTo K3 (fun c3 => sm (fun x =>
          indB (gd c1 c2 c3 && E (rset K1 (m1 x) H1 c1) (rset K2 (m2 c1 x) H2 c2) (rset K3 (m3 c1 c2 x) H3 c3)
            (m1 x) (m2 c1 x) (m3 c1 c2 x) (rv c1 c2 c3 x)))))))))
      ≤ sumTo (K1 ^ n1) (fun H1 => sumTo (K2 ^ n2) (fun H2 => sumTo (K3 ^ n3) (fun H3 => sumTo K1 (fun c1 =>
        sumTo K2 (fun c2 => sumTo K3 (fun c3 => sm (fun x =>
          indB (gd c1 c2 c3 && E (rset K1 (s1 c1 c2 c3 x) H1 c1) (rset K2 (s2 c1 c2 c3 x) H2 c2)
            (rset K3 (s3 c1 c2 c3 x) H3 c3) (s1 c1 c2 c3 x) (s2 c1 c2 c3 x) (s3 c1 c2 c3 x) (sv c1 c2 c3 x)))))) + ε))) :=
        sumTo_mono _ (fun H1 _ => sumTo_mono _ (fun H2 _ => sumTo_mono _ (fun H3 _ =>
          h (fun c1 c2 c3 a b c v => E (rset K1 a H1 c1) (rset K2 b H2 c2) (rset K3 c H3 c3) a b c v))))
    _ = _ := by simp only [sumTo_add, sumTo_const]

/-- A count `sm` that commutes with finite sums adds. -/
theorem sm_add {X : Type} (sm : (X → Nat) → Nat)
    (hsm : ∀ (N : Nat) (f : Nat → X → Nat), sm (fun x => sumTo N (fun i => f i x)) = sumTo N (fun i => sm (f i)))
    (f g : X → Nat) : sm (fun x => f x + g x) = sm f + sm g := by
  have e := hsm 2 (fun i x => if i = 0 then f x else g x)
  have e1 : (fun x => sumTo 2 (fun i => if i = 0 then f x else g x)) = (fun x => f x + g x) :=
    funext fun x => by show 0 + (if 0 = 0 then f x else g x) + (if 1 = 0 then f x else g x) = _; simp
  have e2 : sumTo 2 (fun i => sm (fun x => if i = 0 then f x else g x)) = sm f + sm g := by
    show 0 + sm (fun x => if 0 = 0 then f x else g x) + sm (fun x => if 1 = 0 then f x else g x) = _; simp
  rw [e1, e2] at e; exact e

/-- A count `sm` that commutes with finite sums is monotone. -/
theorem sm_mono {X : Type} (sm : (X → Nat) → Nat)
    (hsm : ∀ (N : Nat) (f : Nat → X → Nat), sm (fun x => sumTo N (fun i => f i x)) = sumTo N (fun i => sm (f i)))
    {f g : X → Nat} (h : ∀ x, f x ≤ g x) : sm f ≤ sm g := by
  have e : g = fun x => f x + (g x - f x) := funext fun x => (Nat.add_sub_of_le (h x)).symm
  rw [e, sm_add sm hsm]; exact Nat.le_add_right _ _

/-- **Fiat–Shamir over three rounds, unguarded**: `fs_zk3` with the guard
    gone from both counts, the guarded-out challenges' public-coin mass
    `B` in the bound.  `K1 K2 K3` times the real count is at most the
    simulator's plus `K1^n1 K2^n2 K3^n3 (ε + B)`; one direction only, one
    proof per oracle. -/
theorem fs_zk3U {X Vw : Type} {K1 K2 K3 n1 n2 n3 ε : Nat} (hK1 : 0 < K1) (hK2 : 0 < K2) (hK3 : 0 < K3)
    (sm : (X → Nat) → Nat)
    (hsm : ∀ (N : Nat) (f : Nat → X → Nat), sm (fun x => sumTo N (fun i => f i x)) = sumTo N (fun i => sm (f i)))
    (m1 : X → Nat) (m2 : Nat → X → Nat) (m3 : Nat → Nat → X → Nat) (hm1 : ∀ x, m1 x < n1)
    (hm2 : ∀ c x, m2 c x < n2) (hm3 : ∀ c c' x, m3 c c' x < n3)
    (s1 s2 s3 : Nat → Nat → Nat → X → Nat) (rv sv : Nat → Nat → Nat → X → Vw) (gd : Nat → Nat → Nat → Bool)
    (h : ∀ F : Nat → Nat → Nat → Nat → Nat → Nat → Vw → Bool,
      sumTo K1 (fun c1 => sumTo K2 (fun c2 => sumTo K3 (fun c3 => sm (fun x =>
        indB (gd c1 c2 c3 && F c1 c2 c3 (m1 x) (m2 c1 x) (m3 c1 c2 x) (rv c1 c2 c3 x)))))) ≤
      sumTo K1 (fun c1 => sumTo K2 (fun c2 => sumTo K3 (fun c3 => sm (fun x =>
        indB (gd c1 c2 c3 && F c1 c2 c3 (s1 c1 c2 c3 x) (s2 c1 c2 c3 x) (s3 c1 c2 c3 x) (sv c1 c2 c3 x)))))) + ε)
    (E : Nat → Nat → Nat → Nat → Nat → Nat → Vw → Bool) :
    let B := sumTo K1 (fun c1 => sumTo K2 (fun c2 => sumTo K3 (fun c3 => sm (fun _ => indB (!gd c1 c2 c3)))))
    K1 * (K2 * (K3 * sumTo (K1 ^ n1) (fun H1 => sumTo (K2 ^ n2) (fun H2 => sumTo (K3 ^ n3) (fun H3 => sm (fun x =>
      indB (E H1 H2 H3 (m1 x) (m2 (rget K1 (m1 x) H1) x) (m3 (rget K1 (m1 x) H1) (rget K2 (m2 (rget K1 (m1 x) H1) x) H2) x)
          (rv (rget K1 (m1 x) H1) (rget K2 (m2 (rget K1 (m1 x) H1) x) H2)
            (rget K3 (m3 (rget K1 (m1 x) H1) (rget K2 (m2 (rget K1 (m1 x) H1) x) H2) x) H3) x)))))))) ≤
    sumTo (K1 ^ n1) (fun H1 => sumTo (K2 ^ n2) (fun H2 => sumTo (K3 ^ n3) (fun H3 => sumTo K1 (fun c1 =>
      sumTo K2 (fun c2 => sumTo K3 (fun c3 => sm (fun x =>
        indB (E (rset K1 (s1 c1 c2 c3 x) H1 c1) (rset K2 (s2 c1 c2 c3 x) H2 c2)
          (rset K3 (s3 c1 c2 c3 x) H3 c3) (s1 c1 c2 c3 x) (s2 c1 c2 c3 x) (s3 c1 c2 c3 x) (sv c1 c2 c3 x))))))))) +
      K1 ^ n1 * (K2 ^ n2 * (K3 ^ n3 * (ε + B))) := by
  intro B
  -- the real count splits at the guard
  have split : ∀ (G : X → Bool) (F : X → Bool), sm (fun x => indB (F x)) ≤
      sm (fun x => indB (G x && F x)) + sm (fun x => indB (!G x)) := fun G F => by
    rw [← sm_add sm hsm]
    exact sm_mono sm hsm (fun x => by cases G x <;> cases F x <;> decide)
  have hg := fs_zk3 hK1 hK2 hK3 sm hsm m1 m2 m3 hm1 hm2 hm3 s1 s2 s3 rv sv gd h E
  have hb := fs_real3 hK1 hK2 hK3 sm hsm m1 m2 m3 hm1 hm2 hm3 rv
    (fun _ _ _ c1 c2 c3 _ _ _ _ => !gd c1 c2 c3)
  simp only [sumTo_const] at hb
  have hs : ∀ H1 H2 H3, sumTo K1 (fun c1 => sumTo K2 (fun c2 => sumTo K3 (fun c3 => sm (fun x =>
      indB (gd c1 c2 c3 && E (rset K1 (s1 c1 c2 c3 x) H1 c1) (rset K2 (s2 c1 c2 c3 x) H2 c2)
        (rset K3 (s3 c1 c2 c3 x) H3 c3) (s1 c1 c2 c3 x) (s2 c1 c2 c3 x) (s3 c1 c2 c3 x) (sv c1 c2 c3 x)))))) ≤
      sumTo K1 (fun c1 => sumTo K2 (fun c2 => sumTo K3 (fun c3 => sm (fun x =>
      indB (E (rset K1 (s1 c1 c2 c3 x) H1 c1) (rset K2 (s2 c1 c2 c3 x) H2 c2)
        (rset K3 (s3 c1 c2 c3 x) H3 c3) (s1 c1 c2 c3 x) (s2 c1 c2 c3 x) (s3 c1 c2 c3 x) (sv c1 c2 c3 x)))))) :=
    fun H1 H2 H3 => sumTo_mono _ (fun c1 _ => sumTo_mono _ (fun c2 _ => sumTo_mono _ (fun c3 _ =>
      sm_mono sm hsm (fun x => by cases gd c1 c2 c3 <;> simp [indB]))))
  have hS := sumTo_mono _ (fun H1 (_ : H1 < K1 ^ n1) => sumTo_mono _ (fun H2 (_ : H2 < K2 ^ n2) =>
    sumTo_mono _ (fun H3 (_ : H3 < K3 ^ n3) => hs H1 H2 H3)))
  have hR := sumTo_mono _ (fun H1 (_ : H1 < K1 ^ n1) => sumTo_mono _ (fun H2 (_ : H2 < K2 ^ n2) =>
    sumTo_mono _ (fun H3 (_ : H3 < K3 ^ n3) =>
      split (fun x => gd (rget K1 (m1 x) H1) (rget K2 (m2 (rget K1 (m1 x) H1) x) H2)
          (rget K3 (m3 (rget K1 (m1 x) H1) (rget K2 (m2 (rget K1 (m1 x) H1) x) H2) x) H3))
        (fun x => E H1 H2 H3 (m1 x) (m2 (rget K1 (m1 x) H1) x)
          (m3 (rget K1 (m1 x) H1) (rget K2 (m2 (rget K1 (m1 x) H1) x) H2) x)
          (rv (rget K1 (m1 x) H1) (rget K2 (m2 (rget K1 (m1 x) H1) x) H2)
            (rget K3 (m3 (rget K1 (m1 x) H1) (rget K2 (m2 (rget K1 (m1 x) H1) x) H2) x) H3) x)))))
  simp only [sumTo_add] at hR
  have hR' := Nat.mul_le_mul_left K1 (Nat.mul_le_mul_left K2 (Nat.mul_le_mul_left K3 hR))
  simp only [Nat.mul_add] at hR' ⊢
  rw [hb] at hR'
  exact Nat.le_trans (Nat.le_trans hR' (Nat.add_le_add_right (Nat.le_trans hg (Nat.add_le_add_right hS _)) _))
    (Nat.le_of_eq (Nat.add_assoc _ _ _))

end Circuit
