import Ski.ZK.SpongeDuplex

/-!
# A single proof's four challenges as independent states

`zk_duplexC` starts from a bound whose real view reads its challenges from
independent uniform states.  A single Sudoku proof's bound (`sud_fs4T`)
reads them from four tables at its transcript's indices.  With the output
and the simulated view not reading the tables, the distinguisher can read
the four challenges back off the tables at the indices its view shows, so
the tables sum down to four uniform challenges.

- **The tables summed down.** Four tables read adaptively, each index
  chosen from the earlier challenges, sum to `Π K_j^{N_j}` over the four
  challenges (`sum4_tables`), so a four-table bound becomes one with four
  uniform challenges and no tables (`hypC_of_read4T`), when the output and
  the simulated view read no table, the simulated view shows the
  programmed indices and the fourth index is recoverable from the views.
- **Full states.** The challenges lifted to states below `K = K_j L_j`,
  each challenge its state's low part (`Wof4`, `cW4_Wof4`, `sum_W4`), the
  error times the high parts' count (`hypW_of_hypC`).
- **The duplex.** With `zk_duplexC`, the four challenges squeezed from one
  run, each the low part of its squeezed state (`zk_duplex4`).
-/

set_option autoImplicit false

namespace Circuit
open ZKF

/-- Four tables read adaptively: the first at `m1`, each later one at an
    index chosen from the earlier answers. -/
def rdAd4 (K1 K2 K3 K4 : Nat) (m1 : Nat) (m2 : Nat → Nat) (m3 : Nat → Nat → Nat) (q : Nat → Nat → Nat → Nat)
    (G : Nat → Nat → Nat → Nat → Nat) (H1 H2 H3 H4 : Nat) : Nat :=
  G (rget K1 m1 H1) (rget K2 (m2 (rget K1 m1 H1)) H2)
    (rget K3 (m3 (rget K1 m1 H1) (rget K2 (m2 (rget K1 m1 H1)) H2)) H3)
    (rget K4 (q (rget K1 m1 H1) (rget K2 (m2 (rget K1 m1 H1)) H2)
      (rget K3 (m3 (rget K1 m1 H1) (rget K2 (m2 (rget K1 m1 H1)) H2)) H3)) H4)

/-- **Four tables read adaptively sum to four uniform challenges.** -/
theorem sum4_tables {K1 K2 K3 K4 N1 N2 N3 N4 : Nat} (hK1 : 0 < K1) (hK2 : 0 < K2) (hK3 : 0 < K3) (hK4 : 0 < K4)
    (m1 : Nat) (m2 : Nat → Nat) (m3 : Nat → Nat → Nat) (q : Nat → Nat → Nat → Nat)
    (hm1 : m1 < N1) (hm2 : ∀ c1, m2 c1 < N2) (hm3 : ∀ c1 c2, m3 c1 c2 < N3) (hq : ∀ c1 c2 c3, q c1 c2 c3 < N4)
    (G : Nat → Nat → Nat → Nat → Nat) :
    K4 * (K1 * (K2 * K3)) * sumTo (K4 ^ N4) (fun H4 => sumTo (K1 ^ N1) (fun H1 => sumTo (K2 ^ N2) (fun H2 =>
      sumTo (K3 ^ N3) (fun H3 => rdAd4 K1 K2 K3 K4 m1 m2 m3 q G H1 H2 H3 H4)))) =
      K4 ^ N4 * (K1 ^ N1 * (K2 ^ N2 * K3 ^ N3)) * sumTo K4 (fun c4 => sumTo K1 (fun c1 => sumTo K2 (fun c2 =>
        sumTo K3 (fun c3 => G c1 c2 c3 c4)))) := by
  -- one table at a time, the last read first
  let f4 := fun c1 c2 c3 H4 => G c1 c2 c3 (rget K4 (q c1 c2 c3) H4)
  let f3 := fun c1 c2 H3 H4 => f4 c1 c2 (rget K3 (m3 c1 c2) H3) H4
  let f2 := fun c1 H2 H3 H4 => f3 c1 (rget K2 (m2 c1) H2) H3 H4
  let g4 := fun c1 c2 c3 => sumTo K4 (fun c4 => G c1 c2 c3 c4)
  let g3 := fun c1 c2 => sumTo K3 (fun c3 => g4 c1 c2 c3)
  let g2 := fun c1 => sumTo K2 (fun c2 => g3 c1 c2)
  have s4 : ∀ c1 c2 c3, K4 * sumTo (K4 ^ N4) (fun H4 => f4 c1 c2 c3 H4) = K4 ^ N4 * g4 c1 c2 c3 :=
    fun c1 c2 c3 => sumTo_rget_one hK4 (hq c1 c2 c3) (G c1 c2 c3)
  have s3 : ∀ c1 c2, K3 * sumTo (K3 ^ N3) (fun H3 => K4 * sumTo (K4 ^ N4) (fun H4 => f3 c1 c2 H3 H4)) =
      K4 ^ N4 * (K3 ^ N3 * g3 c1 c2) := fun c1 c2 => by
    rw [sumTo_congr _ (fun H3 _ => s4 c1 c2 _), ← sumTo_mul, Nat.mul_left_comm,
      sumTo_rget_one hK3 (hm3 c1 c2) (g4 c1 c2)]
  have s2 : ∀ c1, K2 * sumTo (K2 ^ N2) (fun H2 => K3 * sumTo (K3 ^ N3) (fun H3 => K4 * sumTo (K4 ^ N4) (fun H4 =>
      f2 c1 H2 H3 H4))) = K4 ^ N4 * (K3 ^ N3 * (K2 ^ N2 * g2 c1)) := fun c1 => by
    rw [sumTo_congr _ (fun H2 _ => s3 c1 _), ← sumTo_mul, ← sumTo_mul, Nat.mul_left_comm K2, Nat.mul_left_comm K2,
      sumTo_rget_one hK2 (hm2 c1) (g3 c1)]
  have s1 : K1 * sumTo (K1 ^ N1) (fun H1 => K2 * sumTo (K2 ^ N2) (fun H2 => K3 * sumTo (K3 ^ N3) (fun H3 =>
      K4 * sumTo (K4 ^ N4) (fun H4 => rdAd4 K1 K2 K3 K4 m1 m2 m3 q G H1 H2 H3 H4)))) =
      K4 ^ N4 * (K3 ^ N3 * (K2 ^ N2 * (K1 ^ N1 * sumTo K1 g2))) := by
    show K1 * sumTo (K1 ^ N1) (fun H1 => K2 * sumTo (K2 ^ N2) (fun H2 => K3 * sumTo (K3 ^ N3) (fun H3 =>
      K4 * sumTo (K4 ^ N4) (fun H4 => f2 (rget K1 m1 H1) H2 H3 H4)))) = _
    rw [sumTo_congr _ (fun H1 _ => s2 _), ← sumTo_mul, ← sumTo_mul, ← sumTo_mul, Nat.mul_left_comm K1,
      Nat.mul_left_comm K1, Nat.mul_left_comm K1, sumTo_rget_one hK1 hm1 g2]
  -- the tables reordered, the factors pushed in
  have lhs : K4 * (K1 * (K2 * K3)) * sumTo (K4 ^ N4) (fun H4 => sumTo (K1 ^ N1) (fun H1 => sumTo (K2 ^ N2) (fun H2 =>
      sumTo (K3 ^ N3) (fun H3 => rdAd4 K1 K2 K3 K4 m1 m2 m3 q G H1 H2 H3 H4)))) =
      K1 * sumTo (K1 ^ N1) (fun H1 => K2 * sumTo (K2 ^ N2) (fun H2 => K3 * sumTo (K3 ^ N3) (fun H3 =>
        K4 * sumTo (K4 ^ N4) (fun H4 => rdAd4 K1 K2 K3 K4 m1 m2 m3 q G H1 H2 H3 H4)))) := by
    rw [sumTo_exch _ (K1 ^ N1) (K4 ^ N4),
      sumTo_congr (K1 ^ N1) (fun H1 _ => sumTo_exch _ (K2 ^ N2) (K4 ^ N4)),
      sumTo_congr (K1 ^ N1) (fun H1 _ => sumTo_congr (K2 ^ N2) (fun H2 _ => sumTo_exch _ (K3 ^ N3) (K4 ^ N4)))]
    simp only [← sumTo_mul]
    ac_rfl
  rw [lhs, s1]
  -- the challenges reordered
  have rhs : sumTo K1 g2 = sumTo K4 (fun c4 => sumTo K1 (fun c1 => sumTo K2 (fun c2 => sumTo K3 (fun c3 => G c1 c2 c3 c4)))) := by
    show sumTo K1 (fun c1 => sumTo K2 (fun c2 => sumTo K3 (fun c3 => sumTo K4 (fun c4 => G c1 c2 c3 c4)))) = _
    rw [sumTo_congr K1 (fun c1 _ => sumTo_congr K2 (fun c2 _ => sumTo_exch (fun c3 c4 => G c1 c2 c3 c4) K4 K3)),
      sumTo_congr K1 (fun c1 _ => sumTo_exch (fun c2 c4 => sumTo K3 (fun c3 => G c1 c2 c3 c4)) K4 K2),
      sumTo_exch (fun c1 c4 => sumTo K2 (fun c2 => sumTo K3 (fun c3 => G c1 c2 c3 c4))) K4 K1]
  rw [rhs]
  ac_rfl

/-- **A four-table bound with the challenges uniform.**  A bound in
    `sud_fs4T`'s form over four tables (`ZKBT` with `read4T` and `prog4`),
    its output not reading the tables (`hout`), its simulated view neither
    (`hsv`) and showing the programmed indices (`hsvp`), and the fourth
    index recoverable from either view (`qV`), gives the same bound with the
    four challenges drawn uniformly and no tables, times the tables' count
    `Π K_j^{N_j}`. -/
theorem hypC_of_read4T {X O : Type} {K1 K2 K3 K4 N1 N2 N3 N4 ε : Nat} (hK1 : 0 < K1) (hK2 : 0 < K2) (hK3 : 0 < K3)
    (hK4 : 0 < K4) (sm : (X → Nat) → Nat) (hsm : Lin sm)
    (m1 : X → Nat) (m2 : Nat → X → Nat) (m3 : Nat → Nat → X → Nat) (q : Nat → Nat → Nat → X → Nat)
    (out : Nat × Nat × Nat × Nat → Nat → Nat → Nat → Nat → X → O)
    (pts : Nat × Nat × Nat × Nat → X → Nat × Nat × Nat × Nat)
    (sv : Nat × Nat × Nat × Nat → Nat × Nat × Nat × Nat → X → Nat × Nat × Nat × O)
    (hm1 : ∀ x, m1 x < N1) (hm2 : ∀ c x, m2 c x < N2) (hm3 : ∀ c1 c2 x, m3 c1 c2 x < N3)
    (hq : ∀ c1 c2 c3 x, q c1 c2 c3 x < N4)
    (hp1 : ∀ c x, (pts c x).1 < N1) (hp2 : ∀ c x, (pts c x).2.1 < N2) (hp3 : ∀ c x, (pts c x).2.2.1 < N3)
    (hp4 : ∀ c x, (pts c x).2.2.2 < N4)
    (hout : ∀ H H', out H = out H') (hsv : ∀ H H' c x, sv H c x = sv H' c x)
    (hsvp : ∀ H c x, (sv H c x).1 = (pts c x).1 ∧ (sv H c x).2.1 = (pts c x).2.1 ∧ (sv H c x).2.2.1 = (pts c x).2.2.1)
    (qV : Nat × Nat × Nat × O → Nat)
    (hqr : ∀ H c4 c1 c2 c3 x, qV (m1 x, m2 c1 x, m3 c1 c2 x, out H c4 c1 c2 c3 x) = q c1 c2 c3 x)
    (hqs : ∀ H c x, qV (sv H c x) = (pts c x).2.2.2)
    (h : ZKBT (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo (K4 ^ N4) (fun H4 => sumTo (K1 ^ N1) (fun H1 =>
        sumTo (K2 ^ N2) (fun H2 => sumTo (K3 ^ N3) (fun H3 => f (H1, H2, H3, H4))))))
      (K4 * (K1 * (K2 * K3))) sm
      (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo K4 (fun c4 => sumTo K1 (fun c1 =>
        sumTo K2 (fun c2 => sumTo K3 (fun c3 => f (c1, c2, c3, c4))))))
      (read4T K1 K2 K3 K4 m1 m2 m3 q out) (fun H c x => prog4 K1 K2 K3 K4 H (pts c x) c) sv ε)
    (D : Nat × Nat × Nat × Nat → Nat × Nat × Nat × O → Bool) :
    K4 ^ N4 * (K1 ^ N1 * (K2 ^ N2 * K3 ^ N3)) * sm (fun x => sumTo K4 (fun c4 => sumTo K1 (fun c1 =>
        sumTo K2 (fun c2 => sumTo K3 (fun c3 =>
          indB (D (c1, c2, c3, c4) (m1 x, m2 c1 x, m3 c1 c2 x, out (0, 0, 0, 0) c4 c1 c2 c3 x))))))) ≤
      K4 ^ N4 * (K1 ^ N1 * (K2 ^ N2 * K3 ^ N3)) * sumTo K4 (fun c4 => sumTo K1 (fun c1 => sumTo K2 (fun c2 =>
        sumTo K3 (fun c3 => sm (fun x => indB (D (c1, c2, c3, c4) (sv (0, 0, 0, 0) (c1, c2, c3, c4) x))))))) + ε := by
  let E : Nat × Nat × Nat × Nat → Nat × Nat × Nat × O → Bool := fun H v =>
    D (rget K1 v.1 H.1, rget K2 v.2.1 H.2.1, rget K3 v.2.2.1 H.2.2.1, rget K4 (qV v) H.2.2.2) v
  have hE := h E
  -- the real side, read back off the tables
  have hr : ∀ x H1 H2 H3 H4, indB (E (H1, H2, H3, H4) (read4T K1 K2 K3 K4 m1 m2 m3 q out (H1, H2, H3, H4) x)) =
      rdAd4 K1 K2 K3 K4 (m1 x) (fun c1 => m2 c1 x) (fun c1 c2 => m3 c1 c2 x) (fun c1 c2 c3 => q c1 c2 c3 x)
        (fun c1 c2 c3 c4 => indB (D (c1, c2, c3, c4) (m1 x, m2 c1 x, m3 c1 c2 x, out (0, 0, 0, 0) c4 c1 c2 c3 x)))
        H1 H2 H3 H4 := by
    intro x H1 H2 H3 H4
    unfold read4T rdAd4
    show indB (D (_, _, _, rget K4 (qV (m1 x, m2 (rget K1 (m1 x) H1) x,
        m3 (rget K1 (m1 x) H1) (rget K2 (m2 (rget K1 (m1 x) H1) x) H2) x, _)) H4) _) = _
    rw [hqr, hout (H1, H2, H3, H4) (0, 0, 0, 0)]
  -- the simulated side does not read the tables
  have hs : ∀ H c4 c1 c2 c3 x, c1 < K1 → c2 < K2 → c3 < K3 → c4 < K4 →
      indB (E (prog4 K1 K2 K3 K4 H (pts (c1, c2, c3, c4) x) (c1, c2, c3, c4)) (sv H (c1, c2, c3, c4) x)) =
        indB (D (c1, c2, c3, c4) (sv (0, 0, 0, 0) (c1, c2, c3, c4) x)) := by
    intro H c4 c1 c2 c3 x h1 h2 h3 h4
    obtain ⟨e1, e2, e3⟩ := hsvp H (c1, c2, c3, c4) x
    show indB (D (rget K1 (sv H (c1, c2, c3, c4) x).1 (rset K1 (pts (c1, c2, c3, c4) x).1 H.1 c1),
      rget K2 (sv H (c1, c2, c3, c4) x).2.1 (rset K2 (pts (c1, c2, c3, c4) x).2.1 H.2.1 c2),
      rget K3 (sv H (c1, c2, c3, c4) x).2.2.1 (rset K3 (pts (c1, c2, c3, c4) x).2.2.1 H.2.2.1 c3),
      rget K4 (qV (sv H (c1, c2, c3, c4) x)) (rset K4 (pts (c1, c2, c3, c4) x).2.2.2 H.2.2.2 c4))
      (sv H (c1, c2, c3, c4) x)) = _
    rw [e1, e2, e3, hqs, rget_rset hK1 h1, rget_rset hK2 h2, rget_rset hK3 h3, rget_rset hK4 h4,
      hsv H (0, 0, 0, 0)]
  have lsm : ∀ (N : Nat) (f : Nat → X → Nat), sumTo N (fun i => sm (f i)) = sm (fun x => sumTo N (fun i => f i x)) :=
    fun N f => (hsm N f).symm
  -- the left side
  have eL : K4 * (K1 * (K2 * K3)) * sumTo (K4 ^ N4) (fun H4 => sumTo (K1 ^ N1) (fun H1 =>
      sumTo (K2 ^ N2) (fun H2 => sumTo (K3 ^ N3) (fun H3 => sm (fun x =>
        indB (E (H1, H2, H3, H4) (read4T K1 K2 K3 K4 m1 m2 m3 q out (H1, H2, H3, H4) x))))))) =
      K4 ^ N4 * (K1 ^ N1 * (K2 ^ N2 * K3 ^ N3)) * sm (fun x => sumTo K4 (fun c4 => sumTo K1 (fun c1 =>
        sumTo K2 (fun c2 => sumTo K3 (fun c3 =>
          indB (D (c1, c2, c3, c4) (m1 x, m2 c1 x, m3 c1 c2 x, out (0, 0, 0, 0) c4 c1 c2 c3 x))))))) := by
    simp only [lsm]
    rw [← smK sm hsm, ← smK sm hsm]
    refine congrArg sm (funext fun x => ?_)
    simp only [hr]
    exact sum4_tables hK1 hK2 hK3 hK4 _ _ _ _ (hm1 x) (fun c1 => hm2 c1 x) (fun c1 c2 => hm3 c1 c2 x)
      (fun c1 c2 c3 => hq c1 c2 c3 x) _
  -- the right side
  have eR : sumTo (K4 ^ N4) (fun H4 => sumTo (K1 ^ N1) (fun H1 => sumTo (K2 ^ N2) (fun H2 => sumTo (K3 ^ N3) (fun H3 =>
      sumTo K4 (fun c4 => sumTo K1 (fun c1 => sumTo K2 (fun c2 => sumTo K3 (fun c3 => sm (fun x =>
        indB (E (prog4 K1 K2 K3 K4 (H1, H2, H3, H4) (pts (c1, c2, c3, c4) x) (c1, c2, c3, c4))
          (sv (H1, H2, H3, H4) (c1, c2, c3, c4) x))))))))))) =
      K4 ^ N4 * (K1 ^ N1 * (K2 ^ N2 * K3 ^ N3)) * sumTo K4 (fun c4 => sumTo K1 (fun c1 => sumTo K2 (fun c2 =>
        sumTo K3 (fun c3 => sm (fun x => indB (D (c1, c2, c3, c4) (sv (0, 0, 0, 0) (c1, c2, c3, c4) x))))))) := by
    have inner : ∀ H, sumTo K4 (fun c4 => sumTo K1 (fun c1 => sumTo K2 (fun c2 => sumTo K3 (fun c3 => sm (fun x =>
        indB (E (prog4 K1 K2 K3 K4 H (pts (c1, c2, c3, c4) x) (c1, c2, c3, c4)) (sv H (c1, c2, c3, c4) x))))))) =
        sumTo K4 (fun c4 => sumTo K1 (fun c1 => sumTo K2 (fun c2 =>
          sumTo K3 (fun c3 => sm (fun x => indB (D (c1, c2, c3, c4) (sv (0, 0, 0, 0) (c1, c2, c3, c4) x))))))) :=
      fun H => sumTo_congr _ (fun c4 h4 => sumTo_congr _ (fun c1 h1 => sumTo_congr _ (fun c2 h2 => sumTo_congr _
        (fun c3 h3 => congrArg sm (funext fun x => hs H c4 c1 c2 c3 x h1 h2 h3 h4)))))
    rw [sumTo_congr _ (fun H4 _ => sumTo_congr _ (fun H1 _ => sumTo_congr _ (fun H2 _ => sumTo_congr _
      (fun H3 _ => inner (H1, H2, H3, H4)))))]
    rw [sumTo_const, sumTo_const, sumTo_const, sumTo_const]
    ac_rfl
  have hE' := hE
  show _ ≤ _
  calc _ = K4 * (K1 * (K2 * K3)) * sumTo (K4 ^ N4) (fun H4 => sumTo (K1 ^ N1) (fun H1 =>
        sumTo (K2 ^ N2) (fun H2 => sumTo (K3 ^ N3) (fun H3 => sm (fun x =>
          indB (E (H1, H2, H3, H4) (read4T K1 K2 K3 K4 m1 m2 m3 q out (H1, H2, H3, H4) x))))))) := eL.symm
    _ ≤ _ := hE'
    _ = _ := congrArg (· + ε) eR

/-- Three inner sums reversed. -/
theorem sum3_rev {A1 A2 A3 : Nat} (f : Nat → Nat → Nat → Nat) :
    sumTo A1 (fun c1 => sumTo A2 (fun c2 => sumTo A3 (fun c3 => f c1 c2 c3))) =
      sumTo A3 (fun c3 => sumTo A2 (fun c2 => sumTo A1 (fun c1 => f c1 c2 c3))) := by
  rw [sumTo_congr A1 (fun c1 _ => sumTo_exch (fun c2 c3 => f c1 c2 c3) A3 A2),
    sumTo_exch (fun c1 c3 => sumTo A2 (fun c2 => f c1 c2 c3)) A3 A1]
  exact sumTo_congr A3 (fun c3 _ => sumTo_exch (fun c1 c2 => f c1 c2 c3) A2 A1)

/-- **The four digits of `W < K^4`, each a challenge and a high part.**
    With `K = K_j L_j`, the states `c_j + K_j h_j` as the digits of `W`,
    first `c1`, then `c2`, `c3`, `c4`. -/
def Wof4 (K K1 K2 K3 K4 c1 c2 c3 c4 h1 h2 h3 h4 : Nat) : Nat :=
  (c1 + K1 * h1) + K * ((c2 + K2 * h2) + K * ((c3 + K3 * h3) + K * (c4 + K4 * h4)))

theorem sum_digitL {K Kc L : Nat} (hK : K = Kc * L) (g : Nat → Nat) :
    sumTo K g = sumTo L (fun h => sumTo Kc (fun c => g (c + Kc * h))) := by
  rw [hK, sumTo_split]

/-- **A sum over `W < K^4` is the sum over the four challenges and high
    parts.** -/
theorem sum_W4 {K K1 K2 K3 K4 L1 L2 L3 L4 : Nat} (e1 : K = K1 * L1) (e2 : K = K2 * L2) (e3 : K = K3 * L3)
    (e4 : K = K4 * L4) (G : Nat → Nat) :
    sumTo (K ^ 4) G = sumTo L4 (fun h4 => sumTo L3 (fun h3 => sumTo L2 (fun h2 => sumTo L1 (fun h1 =>
      sumTo K4 (fun c4 => sumTo K3 (fun c3 => sumTo K2 (fun c2 => sumTo K1 (fun c1 =>
        G (Wof4 K K1 K2 K3 K4 c1 c2 c3 c4 h1 h2 h3 h4))))))))) := by
  -- the four digits
  have d : sumTo (K ^ 4) G = sumTo K (fun w4 => sumTo K (fun w3 => sumTo K (fun w2 => sumTo K (fun w1 =>
      G (w1 + K * (w2 + K * (w3 + K * w4))))))) := by
    rw [show K ^ 4 = K * (K * (K * K)) by rw [Nat.pow_succ, Nat.pow_succ, Nat.pow_succ, Nat.pow_one]; ac_rfl,
      sumTo_split K _ (K * (K * K))]
    rw [sumTo_split K _ (K * K)]
    rw [sumTo_split K _ K]
  -- each digit a challenge and a high part
  rw [d, sum_digitL e4]
  rw [sumTo_congr L4 (fun h4 _ => sumTo_congr K4 (fun c4 _ => sum_digitL e3 _))]
  rw [sumTo_congr L4 (fun h4 _ => sumTo_congr K4 (fun c4 _ => sumTo_congr L3 (fun h3 _ => sumTo_congr K3
    (fun c3 _ => sum_digitL e2 _))))]
  rw [sumTo_congr L4 (fun h4 _ => sumTo_congr K4 (fun c4 _ => sumTo_congr L3 (fun h3 _ => sumTo_congr K3
    (fun c3 _ => sumTo_congr L2 (fun h2 _ => sumTo_congr K2 (fun c2 _ => sum_digitL e1 _))))))]
  -- the high parts outward
  refine Eq.trans (sumTo_congr L4 (fun h4 _ => sumTo_exch _ L3 K4)) ?_
  refine Eq.trans (sumTo_congr L4 (fun h4 _ => sumTo_congr L3 (fun h3 _ => sumTo_congr K4 (fun c4 _ =>
    sumTo_exch _ L2 K3)))) ?_
  refine Eq.trans (sumTo_congr L4 (fun h4 _ => sumTo_congr L3 (fun h3 _ => sumTo_exch _ L2 K4))) ?_
  refine Eq.trans (sumTo_congr L4 (fun h4 _ => sumTo_congr L3 (fun h3 _ => sumTo_congr L2 (fun h2 _ =>
    sumTo_congr K4 (fun c4 _ => sumTo_congr K3 (fun c3 _ => sumTo_exch _ L1 K2)))))) ?_
  refine Eq.trans (sumTo_congr L4 (fun h4 _ => sumTo_congr L3 (fun h3 _ => sumTo_congr L2 (fun h2 _ =>
    sumTo_congr K4 (fun c4 _ => sumTo_exch _ L1 K3))))) ?_
  exact sumTo_congr L4 (fun h4 _ => sumTo_congr L3 (fun h3 _ => sumTo_congr L2 (fun h2 _ => sumTo_exch _ L1 K4)))

/-- The four challenges read off `W`'s digits. -/
def cW4 (K K1 K2 K3 K4 W : Nat) : Nat × Nat × Nat × Nat :=
  (rget K 0 W % K1, rget K 1 W % K2, rget K 2 W % K3, rget K 3 W % K4)

theorem digit_lt {Kc L K c h : Nat} (e : K = Kc * L) (hc : c < Kc) (hh : h < L) : c + Kc * h < K := by
  rw [e]
  calc c + Kc * h < Kc + Kc * h := Nat.add_lt_add_right hc _
    _ = Kc * (h + 1) := by rw [Nat.mul_succ, Nat.add_comm]
    _ ≤ Kc * L := Nat.mul_le_mul_left _ hh

theorem mod_digit {Kc c h : Nat} (hc : c < Kc) : (c + Kc * h) % Kc = c := by
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hc]

/-- **The challenges read back off the digits.** -/
theorem cW4_Wof4 {K K1 K2 K3 K4 L1 L2 L3 L4 c1 c2 c3 c4 h1 h2 h3 h4 : Nat} (e1 : K = K1 * L1) (e2 : K = K2 * L2)
    (e3 : K = K3 * L3) (e4 : K = K4 * L4) (hc1 : c1 < K1) (hc2 : c2 < K2) (hc3 : c3 < K3) (hc4 : c4 < K4)
    (hh1 : h1 < L1) (hh2 : h2 < L2) (hh3 : h3 < L3) (hh4 : h4 < L4) :
    cW4 K K1 K2 K3 K4 (Wof4 K K1 K2 K3 K4 c1 c2 c3 c4 h1 h2 h3 h4) = (c1, c2, c3, c4) := by
  have d1 := digit_lt e1 hc1 hh1
  have d2 := digit_lt e2 hc2 hh2
  have d3 := digit_lt e3 hc3 hh3
  have d4 := digit_lt e4 hc4 hh4
  have hK : 0 < K := Nat.lt_of_le_of_lt (Nat.zero_le _) d1
  unfold cW4 Wof4
  have r0 : ∀ a b, a < K → rget K 0 (a + K * b) = a := fun a b ha => by
    rw [rget_zero', Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha]
  have rs : ∀ j a b, a < K → rget K (j + 1) (a + K * b) = rget K j b := fun j a b ha => by
    rw [rget_succ', Nat.add_mul_div_left _ _ hK, Nat.div_eq_of_lt ha, Nat.zero_add]
  rw [r0 _ _ d1, rs 0 _ _ d1, r0 _ _ d2, rs 1 _ _ d1, rs 0 _ _ d2, r0 _ _ d3, rs 2 _ _ d1, rs 1 _ _ d2, rs 0 _ _ d3,
    rget_zero', Nat.mod_eq_of_lt d4, mod_digit hc1, mod_digit hc2, mod_digit hc3, mod_digit hc4]

/-- A sum over `W < K^4` of a function of the challenges read off `W` and
    of `W`: the challenges and high parts, the challenges summed `c4` first
    then `c1`, `c2`, `c3`. -/
theorem sum_W4c {K K1 K2 K3 K4 L1 L2 L3 L4 : Nat} (e1 : K = K1 * L1) (e2 : K = K2 * L2) (e3 : K = K3 * L3)
    (e4 : K = K4 * L4) (F : Nat → Nat × Nat × Nat × Nat → Nat) :
    sumTo (K ^ 4) (fun W => F W (cW4 K K1 K2 K3 K4 W)) =
      sumTo L4 (fun h4 => sumTo L3 (fun h3 => sumTo L2 (fun h2 => sumTo L1 (fun h1 =>
        sumTo K4 (fun c4 => sumTo K1 (fun c1 => sumTo K2 (fun c2 => sumTo K3 (fun c3 =>
          F (Wof4 K K1 K2 K3 K4 c1 c2 c3 c4 h1 h2 h3 h4) (c1, c2, c3, c4))))))))) := by
  rw [sum_W4 e1 e2 e3 e4]
  refine sumTo_congr _ (fun h4 hh4 => sumTo_congr _ (fun h3 hh3 => sumTo_congr _ (fun h2 hh2 => sumTo_congr _
    (fun h1 hh1 => sumTo_congr _ (fun c4 hc4 => ?_)))))
  rw [sum3_rev]
  refine sumTo_congr _ (fun c1 hc1 => sumTo_congr _ (fun c2 hc2 => sumTo_congr _ (fun c3 hc3 => ?_)))
  rw [cW4_Wof4 e1 e2 e3 e4 hc1 hc2 hc3 hc4 hh1 hh2 hh3 hh4]

/-- **The challenges lifted to full states.**  A bound with four uniform
    challenges, each `K_j` values, gives the bound with four uniform states
    below `K = K_j L_j`, the challenges their low parts, its error times
    the high parts' count. -/
theorem hypW_of_hypC {X V : Type} {K K1 K2 K3 K4 L1 L2 L3 L4 TT ε : Nat} (e1 : K = K1 * L1) (e2 : K = K2 * L2)
    (e3 : K = K3 * L3) (e4 : K = K4 * L4) (sm : (X → Nat) → Nat) (hsm : Lin sm)
    (rvc svc : Nat × Nat × Nat × Nat → X → V)
    (hC : ∀ D : Nat × Nat × Nat × Nat → V → Bool,
      TT * sm (fun x => sumTo K4 (fun c4 => sumTo K1 (fun c1 => sumTo K2 (fun c2 => sumTo K3 (fun c3 =>
        indB (D (c1, c2, c3, c4) (rvc (c1, c2, c3, c4) x))))))) ≤
      TT * sumTo K4 (fun c4 => sumTo K1 (fun c1 => sumTo K2 (fun c2 => sumTo K3 (fun c3 =>
        sm (fun x => indB (D (c1, c2, c3, c4) (svc (c1, c2, c3, c4) x))))))) + ε)
    (D' : Nat → V → Bool) :
    TT * sm (fun x => sumTo (K ^ 4) (fun W => indB (D' W (rvc (cW4 K K1 K2 K3 K4 W) x)))) ≤
      TT * sm (fun x => sumTo (K ^ 4) (fun W => indB (D' W (svc (cW4 K K1 K2 K3 K4 W) x)))) +
        L4 * (L3 * (L2 * (L1 * ε))) := by
  have lsm : ∀ (N : Nat) (f : Nat → X → Nat), sm (fun x => sumTo N (fun i => f i x)) = sumTo N (fun i => sm (f i)) :=
    fun N f => hsm N f
  have hs := fun (h1 h2 h3 h4 : Nat) => hC (fun c v => D' (Wof4 K K1 K2 K3 K4 c.1 c.2.1 c.2.2.1 c.2.2.2 h1 h2 h3 h4) v)
  -- both sides as sums over the high parts
  have eL : TT * sm (fun x => sumTo (K ^ 4) (fun W => indB (D' W (rvc (cW4 K K1 K2 K3 K4 W) x)))) =
      sumTo L4 (fun h4 => sumTo L3 (fun h3 => sumTo L2 (fun h2 => sumTo L1 (fun h1 =>
        TT * sm (fun x => sumTo K4 (fun c4 => sumTo K1 (fun c1 => sumTo K2 (fun c2 => sumTo K3 (fun c3 =>
          indB (D' (Wof4 K K1 K2 K3 K4 c1 c2 c3 c4 h1 h2 h3 h4) (rvc (c1, c2, c3, c4) x))))))))))) := by
    rw [show (fun x => sumTo (K ^ 4) (fun W => indB (D' W (rvc (cW4 K K1 K2 K3 K4 W) x)))) = fun x =>
        sumTo L4 (fun h4 => sumTo L3 (fun h3 => sumTo L2 (fun h2 => sumTo L1 (fun h1 =>
          sumTo K4 (fun c4 => sumTo K1 (fun c1 => sumTo K2 (fun c2 => sumTo K3 (fun c3 =>
            indB (D' (Wof4 K K1 K2 K3 K4 c1 c2 c3 c4 h1 h2 h3 h4) (rvc (c1, c2, c3, c4) x)))))))))) from
      funext fun x => sum_W4c e1 e2 e3 e4 (fun W c => indB (D' W (rvc c x)))]
    rw [lsm, sumTo_mul]
    refine sumTo_congr _ (fun h4 _ => ?_); rw [lsm, sumTo_mul]
    refine sumTo_congr _ (fun h3 _ => ?_); rw [lsm, sumTo_mul]
    refine sumTo_congr _ (fun h2 _ => ?_); rw [lsm, sumTo_mul]
  have eR : TT * sm (fun x => sumTo (K ^ 4) (fun W => indB (D' W (svc (cW4 K K1 K2 K3 K4 W) x)))) =
      sumTo L4 (fun h4 => sumTo L3 (fun h3 => sumTo L2 (fun h2 => sumTo L1 (fun h1 =>
        TT * sumTo K4 (fun c4 => sumTo K1 (fun c1 => sumTo K2 (fun c2 => sumTo K3 (fun c3 =>
          sm (fun x => indB (D' (Wof4 K K1 K2 K3 K4 c1 c2 c3 c4 h1 h2 h3 h4) (svc (c1, c2, c3, c4) x))))))))))) := by
    rw [show (fun x => sumTo (K ^ 4) (fun W => indB (D' W (svc (cW4 K K1 K2 K3 K4 W) x)))) = fun x =>
        sumTo L4 (fun h4 => sumTo L3 (fun h3 => sumTo L2 (fun h2 => sumTo L1 (fun h1 =>
          sumTo K4 (fun c4 => sumTo K1 (fun c1 => sumTo K2 (fun c2 => sumTo K3 (fun c3 =>
            indB (D' (Wof4 K K1 K2 K3 K4 c1 c2 c3 c4 h1 h2 h3 h4) (svc (c1, c2, c3, c4) x)))))))))) from
      funext fun x => sum_W4c e1 e2 e3 e4 (fun W c => indB (D' W (svc c x)))]
    rw [lsm, sumTo_mul]
    refine sumTo_congr _ (fun h4 _ => ?_); rw [lsm, sumTo_mul]
    refine sumTo_congr _ (fun h3 _ => ?_); rw [lsm, sumTo_mul]
    refine sumTo_congr _ (fun h2 _ => ?_); rw [lsm, sumTo_mul]
    refine sumTo_congr _ (fun h1 _ => ?_)
    congr 1
    rw [lsm]; refine sumTo_congr _ (fun c4 _ => ?_)
    rw [lsm]; refine sumTo_congr _ (fun c1 _ => ?_)
    rw [lsm]; refine sumTo_congr _ (fun c2 _ => ?_)
    rw [lsm]
  rw [eL, eR]
  refine Nat.le_trans (sumTo_mono _ (fun h4 _ => sumTo_mono _ (fun h3 _ => sumTo_mono _ (fun h2 _ =>
    sumTo_mono _ (fun h1 _ => hs h1 h2 h3 h4))))) (Nat.le_of_eq ?_)
  simp only [sumTo_add, sumTo_const]

/-- **A single four-challenge proof with every challenge squeezed from one
    duplex run.**  `hypC_of_read4T` (the tables summed down to uniform
    challenges), `hypW_of_hypC` (the challenges lifted to full states, the
    challenges their low parts) and `zk_duplexC` (the states squeezed from
    the run, the simulator programming the permutation at the squeezes):
    the real view reads each challenge as the low part of the run's
    squeezed answer, and the error gains the high parts' count times the
    composite's error and the run's exchanges, readbacks and stages. -/
theorem zk_duplex4 {X O : Type} {K K1 K2 K3 K4 L1 L2 L3 L4 N1 N2 N3 N4 ε : Nat} (hK : 0 < K) (hK1 : 0 < K1)
    (hK2 : 0 < K2) (hK3 : 0 < K3) (hK4 : 0 < K4) (e1 : K = K1 * L1) (e2 : K = K2 * L2) (e3 : K = K3 * L3)
    (e4 : K = K4 * L4) (sm : (X → Nat) → Nat) (hsm : Lin sm)
    (m1 : X → Nat) (m2 : Nat → X → Nat) (m3 : Nat → Nat → X → Nat) (q : Nat → Nat → Nat → X → Nat)
    (out : Nat × Nat × Nat × Nat → Nat → Nat → Nat → Nat → X → O)
    (pts : Nat × Nat × Nat × Nat → X → Nat × Nat × Nat × Nat)
    (sv : Nat × Nat × Nat × Nat → Nat × Nat × Nat × Nat → X → Nat × Nat × Nat × O)
    (hm1 : ∀ x, m1 x < N1) (hm2 : ∀ c x, m2 c x < N2) (hm3 : ∀ c1 c2 x, m3 c1 c2 x < N3)
    (hq : ∀ c1 c2 c3 x, q c1 c2 c3 x < N4)
    (hp1 : ∀ c x, (pts c x).1 < N1) (hp2 : ∀ c x, (pts c x).2.1 < N2) (hp3 : ∀ c x, (pts c x).2.2.1 < N3)
    (hp4 : ∀ c x, (pts c x).2.2.2 < N4)
    (hout : ∀ H H', out H = out H') (hsv : ∀ H H' c x, sv H c x = sv H' c x)
    (hsvp : ∀ H c x, (sv H c x).1 = (pts c x).1 ∧ (sv H c x).2.1 = (pts c x).2.1 ∧ (sv H c x).2.2.1 = (pts c x).2.2.1)
    (qV : Nat × Nat × Nat × O → Nat)
    (hqr : ∀ H c4 c1 c2 c3 x, qV (m1 x, m2 c1 x, m3 c1 c2 x, out H c4 c1 c2 c3 x) = q c1 c2 c3 x)
    (hqs : ∀ H c x, qV (sv H c x) = (pts c x).2.2.2)
    (h : ZKBT (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo (K4 ^ N4) (fun H4 => sumTo (K1 ^ N1) (fun H1 =>
        sumTo (K2 ^ N2) (fun H2 => sumTo (K3 ^ N3) (fun H3 => f (H1, H2, H3, H4))))))
      (K4 * (K1 * (K2 * K3))) sm
      (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo K4 (fun c4 => sumTo K1 (fun c1 =>
        sumTo K2 (fun c2 => sumTo K3 (fun c3 => f (c1, c2, c3, c4))))))
      (read4T K1 K2 K3 K4 m1 m2 m3 q out) (fun H c x => prog4 K1 K2 K3 K4 H (pts c x) c) sv ε)
    (nxt : X → List Nat → Nat) (hnx : ∀ x l, nxt x l < K) (times : Nat → Nat)
    (htimes : ∀ i j, i < j → times i < times j) (nxtV : Nat × Nat × Nat × O → List Nat → Nat)
    (hcons : ∀ x W l, consW K times 4 W l = true →
      nxtV (m1 x, m2 (cW4 K K1 K2 K3 K4 W).1 x, m3 (cW4 K K1 K2 K3 K4 W).1 (cW4 K K1 K2 K3 K4 W).2.1 x,
        out (0, 0, 0, 0) (cW4 K K1 K2 K3 K4 W).2.2.2 (cW4 K K1 K2 K3 K4 W).1 (cW4 K K1 K2 K3 K4 W).2.1
          (cW4 K K1 K2 K3 K4 W).2.2.1 x) l = nxt x l)
    (E : Nat → Nat × Nat × Nat × O → Bool) :
    let rvc := fun (c : Nat × Nat × Nat × Nat) (x : X) =>
      (m1 x, m2 c.1 x, m3 c.1 c.2.1 x, out (0, 0, 0, 0) c.2.2.2 c.1 c.2.1 c.2.2.1 x)
    let TT := K4 ^ N4 * (K1 ^ N1 * (K2 ^ N2 * K3 ^ N3))
    TT * (K ^ 4 * sm (fun x => sumTo (K ^ K) (fun P => indB (permB K P &&
        E P (rvc (cW4 K K1 K2 K3 K4 (WofR K (nxt x) times 4 P)) x))))) ≤
      TT * sm (fun x => sumTo (K ^ K) (fun P => indB (permB K P) * sumTo (K ^ 4) (fun W =>
        indB (E (progSeqN K (nxtV (sv (0, 0, 0, 0) (cW4 K K1 K2 K3 K4 W) x)) times 4 W P)
          (sv (0, 0, 0, 0) (cW4 K K1 K2 K3 K4 W) x))))) +
      sumTo (K ^ K) (fun P => indB (permB K P)) * (L4 * (L3 * (L2 * (L1 * ε)))) +
      TT * sm (fun x => 2 * badSeq K (nxt x) times 4 + sumTo 4 (fun j => K ^ (4 - j) * badSeq K (nxt x) times j)) := by
  intro rvc TT
  have hC := hypC_of_read4T hK1 hK2 hK3 hK4 sm hsm m1 m2 m3 q out pts sv hm1 hm2 hm3 hq hp1 hp2 hp3 hp4 hout hsv hsvp
    qV hqr hqs h
  have hW := fun (D' : Nat → Nat × Nat × Nat × O → Bool) => hypW_of_hypC (TT := TT) e1 e2 e3 e4 sm hsm rvc
    (fun c x => sv (0, 0, 0, 0) c x) hC D'
  have lsm : ∀ (N : Nat) (f : Nat → X → Nat), sm (fun x => sumTo N (fun i => f i x)) = sumTo N (fun i => sm (f i)) :=
    fun N f => hsm N f
  -- the bound in `zk_duplexC`'s form, summed over the permutation tables
  have hyp : ∀ D : Nat → Nat → Unit → Nat × Nat × Nat × O → Bool,
      TT * sm (fun x => sumTo (K ^ K) (fun P => indB (permB K P) * sumTo (K ^ 4) (fun W =>
        indB (D P W () (rvc (cW4 K K1 K2 K3 K4 W) x))))) ≤
      TT * sm (fun x => sumTo (K ^ K) (fun P => indB (permB K P) * sumTo (K ^ 4) (fun W =>
        indB (D P W () (sv (0, 0, 0, 0) (cW4 K K1 K2 K3 K4 W) x))))) +
        sumTo (K ^ K) (fun P => indB (permB K P)) * (L4 * (L3 * (L2 * (L1 * ε)))) := fun D => by
    rw [lsm, lsm, sumTo_mul, sumTo_mul,
      show sumTo (K ^ K) (fun P => indB (permB K P)) * (L4 * (L3 * (L2 * (L1 * ε)))) =
        sumTo (K ^ K) (fun P => indB (permB K P) * (L4 * (L3 * (L2 * (L1 * ε))))) from by
          rw [Nat.mul_comm, sumTo_mul]; exact sumTo_congr _ (fun _ _ => Nat.mul_comm _ _),
      ← sumTo_add]
    refine sumTo_mono _ (fun P _ => ?_)
    rw [smK sm hsm, smK sm hsm, Nat.mul_left_comm, Nat.mul_left_comm TT, ← Nat.mul_add]
    exact Nat.mul_le_mul_left _ (hW (fun W v => D P W () v))
  exact zk_duplexC (T := Unit) (C := Unit) (K4w := TT) hK (fun f => f ()) (fun _ _ => rfl) sm hsm (fun g => TT * g ())
    (fun _ x => nxt x) (fun _ x => hnx x) times htimes (fun _ x W => rvc (cW4 K K1 K2 K3 K4 W) x)
    (fun _ _ W _ _ => ((), W)) (fun _ _ W _ x => sv (0, 0, 0, 0) (cW4 K K1 K2 K3 K4 W) x) (fun _ v => nxtV v)
    (fun _ x W l hl => hcons x W l hl) hyp (fun P _ v => E P v)

end Circuit
