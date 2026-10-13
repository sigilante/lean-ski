import Ski.ZK.ROMFSRead2

/-!
# Four Fiat–Shamir rounds, the openings reading the tables

Plonky3's query indices are a fourth challenge, hashed at `φ` of the third
message and `oz` of the view (`fs_open4`).  After the fourth reprogramming
the openings read the fourth table set there (`fs_lastGT`), a function of
the commitments' values and the view, so the swap of `ROMFSRead2` runs
with each opening indexed by the view as well (`open_two_coreV`).  The
view is fixed while the salts vary, so the transcript bound still applies.
Three rounds with such openings, unguarded (`fs_zk3UT`, `fs_open3UT`),
then four (`fs_open4T`), and over the oracle's commitment with the
queries reading all four tables (`fs_open4ROMT`).  One direction;
`fs_open4ROM`'s other limits hold.
-/

set_option autoImplicit false
namespace Circuit
open ZKF

/-- The view event two salts give, each opening read at the view and at
    the other commitment's value. -/
def openEv2V {PV PB D1 O1 P1 D2 O2 P2 : Type} (Com1 : D1 → Nat → Nat) (Pf1 : TViewN PV PB → Nat → D1 → Nat → P1) (sd1 : O1 → D1)
    (d1 : D1) (ov1 : TViewN PV PB → Option O1) (Com2 : D2 → Nat → Nat) (Pf2 : TViewN PV PB → Nat → D2 → Nat → P2) (sd2 : O2 → D2)
    (d2 : D2) (ov2 : TViewN PV PB → Option O2)
    (F : Nat → Nat → Option P1 → Option P2 → TViewN PV PB → Bool) (σ1 σ2 : Nat) (v : TViewN PV PB) : Bool :=
  openEv Com1 (Pf1 v (openC Com2 sd2 d2 ov2 σ2 v)) sd1 d1 ov1
    (fun mm1 p1 w => F mm1 (openC Com2 sd2 d2 ov2 σ2 w) p1 ((ov2 w).map (fun o => Pf2 w mm1 (sd2 o) σ2)) w) σ1 v

theorem openEv2V_and {PV PB D1 O1 P1 D2 O2 P2 : Type} (Com1 : D1 → Nat → Nat) (Pf1 : TViewN PV PB → Nat → D1 → Nat → P1)
    (sd1 : O1 → D1) (d1 : D1) (ov1 : TViewN PV PB → Option O1) (Com2 : D2 → Nat → Nat) (Pf2 : TViewN PV PB → Nat → D2 → Nat → P2)
    (sd2 : O2 → D2) (d2 : D2) (ov2 : TViewN PV PB → Option O2) (b : Bool)
    (F : Nat → Nat → Option P1 → Option P2 → TViewN PV PB → Bool) (σ1 σ2 : Nat) (v : TViewN PV PB) :
    openEv2V Com1 Pf1 sd1 d1 ov1 Com2 Pf2 sd2 d2 ov2 (fun a b' p q w => b && F a b' p q w) σ1 σ2 v =
      (b && openEv2V Com1 Pf1 sd1 d1 ov1 Com2 Pf2 sd2 d2 ov2 F σ1 σ2 v) := by
  unfold openEv2V; rw [openEv_and]

theorem openEv2V_some {PV PB D1 O1 P1 D2 O2 P2 : Type} (Com1 : D1 → Nat → Nat) (Pf1 : TViewN PV PB → Nat → D1 → Nat → P1)
    (sd1 : O1 → D1) (d1 : D1) (ov1 : TViewN PV PB → Option O1) (Com2 : D2 → Nat → Nat) (Pf2 : TViewN PV PB → Nat → D2 → Nat → P2)
    (sd2 : O2 → D2) (d2 : D2) (ov2 : TViewN PV PB → Option O2)
    (F : Nat → Nat → Option P1 → Option P2 → TViewN PV PB → Bool) (σ1 σ2 : Nat) (v : TViewN PV PB) (o1 : O1)
    (o2 : O2) (h1 : ov1 v = some o1) (h2 : ov2 v = some o2) :
    openEv2V Com1 Pf1 sd1 d1 ov1 Com2 Pf2 sd2 d2 ov2 F σ1 σ2 v =
      F (Com1 (sd1 o1) σ1) (Com2 (sd2 o2) σ2) (some (Pf1 v (Com2 (sd2 o2) σ2) (sd1 o1) σ1))
        (some (Pf2 v (Com1 (sd1 o1) σ1) (sd2 o2) σ2)) v := by
  unfold openEv2V openEv openC; rw [h1]; dsimp only; rw [h2]; rfl

/-- **Two opened commitments beside a transcript, each opening read at
    the view and at the other commitment's value** (`open_two_core` with
    `Pf1 c w mm2`, `Pf2 c w mm1`): hiding given at every view and value.
    The view does not vary with the salts, so each swap holds it fixed. -/
theorem open_two_coreV {PV PB D1 O1 P1 D2 O2 P2 : Type} {NR m e1 e2 NS1 NS2 : Nat}
    (rv sv : EF → EF → Nat → (Nat → Tup) → TViewN PV PB)
    (hrv : ∀ α β r t, rv α β r t = none ∨ ∃ p x y, rv α β r t = some (p, α, β, x, y))
    (hsv : ∀ α β r t, ∃ p x y, sv α β r t = some (p, α, β, x, y))
    (h1 : ∀ E : TViewN PV PB → Bool, tsumN NR m (fun α β r t => indB (genB β && E (rv α β r t))) ≤
      tsumN NR m (fun α β r t => indB (genB β && E (sv α β r t))) + e1 + e2)
    (h2 : ∀ E : TViewN PV PB → Bool, tsumN NR m (fun α β r t => indB (genB β && E (sv α β r t))) ≤
      tsumN NR m (fun α β r t => indB (genB β && E (rv α β r t))) + e1 + e2)
    (Com1 : D1 → Nat → Nat) (Pf1 : Nat → TViewN PV PB → Nat → D1 → Nat → P1) (op1 : D1 → O1) (sd1 : O1 → D1) (d1 : D1)
    (hc1 : ComHides NS1 Com1) (hp1 : ∀ c w v, ComPfHides NS1 Com1 (Pf1 c w v) op1) (ov1 : TViewN PV PB → Option O1)
    (hov1 : ov1 none = none) (main1 : (Nat → Tup) → Nat → D1)
    (hsd1 : ∀ t r, op1 (sd1 (op1 (main1 t r))) = op1 (main1 t r))
    (Com2 : D2 → Nat → Nat) (Pf2 : Nat → TViewN PV PB → Nat → D2 → Nat → P2) (op2 : D2 → O2) (sd2 : O2 → D2) (d2 : D2)
    (hc2 : ComHides NS2 Com2) (hp2 : ∀ c w v, ComPfHides NS2 Com2 (Pf2 c w v) op2) (ov2 : TViewN PV PB → Option O2)
    (hov2 : ov2 none = none) (main2 : Nat → (Nat → Tup) → Nat → D2)
    (hsd2 : ∀ c t r, op2 (sd2 (op2 (main2 c t r))) = op2 (main2 c t r))
    (hvo1 : ∀ c r t, rv (efOf (c / Q4)) (efOf (c % Q4)) r t = none ∨
      ov1 (rv (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (op1 (main1 t r)))
    (hvo2 : ∀ c r t, rv (efOf (c / Q4)) (efOf (c % Q4)) r t = none ∨
      ov2 (rv (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (op2 (main2 c t r)))
    (sop1 : Nat → (Nat → Tup) → O1) (sop2 : Nat → Nat → (Nat → Tup) → O2)
    (hsvo1 : ∀ c r t, ov1 (sv (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (sop1 r t))
    (hsvo2 : ∀ c r t, ov2 (sv (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (sop2 c r t))
    (F : Nat → Nat → Nat → Option P1 → Option P2 → TViewN PV PB → Bool) :
    sumTo (Q4 * Q4) (fun c => sumTo NS1 (fun σ1 => sumTo NS2 (fun σ2 => sumTo NR (fun r => sumN m (fun t =>
      indB (genB (efOf (c % Q4)) && F c (Com1 (main1 t r) σ1) (Com2 (main2 c t r) σ2)
        ((ov1 (rv (efOf (c / Q4)) (efOf (c % Q4)) r t)).map
          (fun _ => Pf1 c (rv (efOf (c / Q4)) (efOf (c % Q4)) r t) (Com2 (main2 c t r) σ2) (main1 t r) σ1))
        ((ov2 (rv (efOf (c / Q4)) (efOf (c % Q4)) r t)).map
          (fun _ => Pf2 c (rv (efOf (c / Q4)) (efOf (c % Q4)) r t) (Com1 (main1 t r) σ1) (main2 c t r) σ2))
        (rv (efOf (c / Q4)) (efOf (c % Q4)) r t))))))) ≤
    sumTo (Q4 * Q4) (fun c => sumTo NS1 (fun σ1 => sumTo NS2 (fun σ2 => sumTo NR (fun r => sumN m (fun t =>
      indB (genB (efOf (c % Q4)) && F c (Com1 (sd1 (sop1 r t)) σ1) (Com2 (sd2 (sop2 c r t)) σ2)
        (some (Pf1 c (sv (efOf (c / Q4)) (efOf (c % Q4)) r t) (Com2 (sd2 (sop2 c r t)) σ2) (sd1 (sop1 r t)) σ1))
        (some (Pf2 c (sv (efOf (c / Q4)) (efOf (c % Q4)) r t) (Com1 (sd1 (sop1 r t)) σ1) (sd2 (sop2 c r t)) σ2))
        (sv (efOf (c / Q4)) (efOf (c % Q4)) r t))))))) + NS1 * (NS2 * (e1 + e2)) := by
  have h1' := fun E => Nat.le_trans (h1 E) (Nat.le_of_eq (Nat.add_assoc _ e1 e2))
  have h2' := fun E => Nat.le_trans (h2 E) (Nat.le_of_eq (Nat.add_assoc _ e1 e2))
  let G : Nat → Nat → Nat → TViewN PV PB → Bool := fun σ1 σ2 c w =>
    openEv2V Com1 (Pf1 c) sd1 d1 ov1 Com2 (Pf2 c) sd2 d2 ov2 (F c) σ1 σ2 w
  have hreal : ∀ c, sumTo NS1 (fun σ1 => sumTo NS2 (fun σ2 => sumTo NR (fun r => sumN m (fun t =>
      indB (genB (efOf (c % Q4)) && F c (Com1 (main1 t r) σ1) (Com2 (main2 c t r) σ2)
        ((ov1 (rv (efOf (c / Q4)) (efOf (c % Q4)) r t)).map
          (fun _ => Pf1 c (rv (efOf (c / Q4)) (efOf (c % Q4)) r t) (Com2 (main2 c t r) σ2) (main1 t r) σ1))
        ((ov2 (rv (efOf (c / Q4)) (efOf (c % Q4)) r t)).map
          (fun _ => Pf2 c (rv (efOf (c / Q4)) (efOf (c % Q4)) r t) (Com1 (main1 t r) σ1) (main2 c t r) σ2))
        (rv (efOf (c / Q4)) (efOf (c % Q4)) r t)))))) =
      sumTo NS2 (fun σ2 => sumTo NS1 (fun σ1 => sumTo NR (fun r => sumN m (fun t =>
        indB (genB (efOf (c % Q4)) && G σ1 σ2 c (rv (efOf (c / Q4)) (efOf (c % Q4)) r t)))))) := fun c => by
    -- the second commitment swapped, the first's value fixed by its salt
    rw [sumTo_congr _ (fun σ1 _ => open_real2T (NR := NR) (m := m) Com2
      (fun r t => Pf2 c (rv (efOf (c / Q4)) (efOf (c % Q4)) r t) (Com1 (main1 t r) σ1)) op2 sd2 d2 hc2
      (fun r t => hp2 c _ _) ov2 hov2 (main2 c) (hsd2 c)
      (fun r t => rv (efOf (c / Q4)) (efOf (c % Q4)) r t) (fun r t => hvo2 c r t)
      (fun r t mm2 p2 w => genB (efOf (c % Q4)) && F c (Com1 (main1 t r) σ1) mm2
        ((ov1 w).map (fun _ => Pf1 c w mm2 (main1 t r) σ1)) p2 w))]
    rw [sumTo_exch _ NS2 NS1]
    refine sumTo_congr _ (fun σ2 _ => ?_)
    -- then the first, the second's value read off the view
    have e := open_real2T (NR := NR) (m := m) Com1
      (fun r t => Pf1 c (rv (efOf (c / Q4)) (efOf (c % Q4)) r t)
        (openC Com2 sd2 d2 ov2 σ2 (rv (efOf (c / Q4)) (efOf (c % Q4)) r t))) op1 sd1 d1 hc1
      (fun r t => hp1 c _ _) ov1 hov1 main1 hsd1
      (fun r t => rv (efOf (c / Q4)) (efOf (c % Q4)) r t) (fun r t => hvo1 c r t)
      (fun _ _ mm1 p1 w => genB (efOf (c % Q4)) && F c mm1 (openC Com2 sd2 d2 ov2 σ2 w) p1
        ((ov2 w).map (fun o => Pf2 c w mm1 (sd2 o) σ2)) w)
    refine Eq.trans ?_ (e.trans ?_)
    · refine sumTo_congr _ (fun σ1 _ => sumTo_congr _ (fun r _ => Nat.le_antisymm
        (sumN_mono m (fun t => Nat.le_of_eq ?_)) (sumN_mono m (fun t => Nat.le_of_eq ?_))))
      all_goals (unfold openEv openC; cases ov2 (rv (efOf (c / Q4)) (efOf (c % Q4)) r t) <;> rfl)
    · have eq : ∀ σ1 r t, indB (openEv Com1
            (Pf1 c (rv (efOf (c / Q4)) (efOf (c % Q4)) r t) (openC Com2 sd2 d2 ov2 σ2 (rv (efOf (c / Q4)) (efOf (c % Q4)) r t))) sd1 d1 ov1
            (fun mm1 p1 w => genB (efOf (c % Q4)) && F c mm1 (openC Com2 sd2 d2 ov2 σ2 w) p1
              ((ov2 w).map (fun o => Pf2 c w mm1 (sd2 o) σ2)) w)
            σ1 (rv (efOf (c / Q4)) (efOf (c % Q4)) r t)) =
          indB (genB (efOf (c % Q4)) && G σ1 σ2 c (rv (efOf (c / Q4)) (efOf (c % Q4)) r t)) := fun σ1 r t => by
        show indB (openEv2V Com1 (Pf1 c) sd1 d1 ov1 Com2 (Pf2 c) sd2 d2 ov2
          (fun a b' p q w => genB (efOf (c % Q4)) && F c a b' p q w) σ1 σ2 _) = _
        rw [openEv2V_and]
      refine sumTo_congr _ (fun σ1 _ => sumTo_congr _ (fun r _ => Nat.le_antisymm
        (sumN_mono m (fun t => Nat.le_of_eq (eq σ1 r t))) (sumN_mono m (fun t => Nat.le_of_eq (eq σ1 r t).symm))))
  have hsim : ∀ c, sumTo NS1 (fun σ1 => sumTo NS2 (fun σ2 => sumTo NR (fun r => sumN m (fun t =>
      indB (genB (efOf (c % Q4)) && F c (Com1 (sd1 (sop1 r t)) σ1) (Com2 (sd2 (sop2 c r t)) σ2)
        (some (Pf1 c (sv (efOf (c / Q4)) (efOf (c % Q4)) r t) (Com2 (sd2 (sop2 c r t)) σ2) (sd1 (sop1 r t)) σ1))
        (some (Pf2 c (sv (efOf (c / Q4)) (efOf (c % Q4)) r t) (Com1 (sd1 (sop1 r t)) σ1) (sd2 (sop2 c r t)) σ2))
        (sv (efOf (c / Q4)) (efOf (c % Q4)) r t)))))) =
      sumTo NS2 (fun σ2 => sumTo NS1 (fun σ1 => sumTo NR (fun r => sumN m (fun t =>
        indB (genB (efOf (c % Q4)) && G σ1 σ2 c (sv (efOf (c / Q4)) (efOf (c % Q4)) r t)))))) := fun c => by
    rw [sumTo_exch _ NS2 NS1]
    refine sumTo_congr _ (fun σ2 _ => sumTo_congr _ (fun σ1 _ => sumTo_congr _ (fun r _ => Nat.le_antisymm
      (sumN_mono m (fun t => Nat.le_of_eq ?_)) (sumN_mono m (fun t => Nat.le_of_eq ?_)))))
    · show _ = indB (genB (efOf (c % Q4)) && openEv2V Com1 (Pf1 c) sd1 d1 ov1 Com2 (Pf2 c) sd2 d2 ov2 (F c) σ1 σ2 _)
      rw [openEv2V_some _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (hsvo1 c r t) (hsvo2 c r t)]
    · show indB (genB (efOf (c % Q4)) && openEv2V Com1 (Pf1 c) sd1 d1 ov1 Com2 (Pf2 c) sd2 d2 ov2 (F c) σ1 σ2 _) = _
      rw [openEv2V_some _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (hsvo1 c r t) (hsvo2 c r t)]
  have ex : ∀ (v : EF → EF → Nat → (Nat → Tup) → TViewN PV PB),
      sumTo (Q4 * Q4) (fun c => sumTo NS2 (fun σ2 => sumTo NS1 (fun σ1 => sumTo NR (fun r => sumN m (fun t =>
        indB (genB (efOf (c % Q4)) && G σ1 σ2 c (v (efOf (c / Q4)) (efOf (c % Q4)) r t))))))) =
      sumTo NS2 (fun σ2 => sumTo NS1 (fun σ1 => tsumN NR m (fun α β r t =>
        indB (genB β && G σ1 σ2 (efIdx β + Q4 * efIdx α) (v α β r t))))) := fun v => by
    rw [sumTo_exch _ NS2 (Q4 * Q4)]
    refine sumTo_congr _ (fun σ2 _ => ?_)
    rw [sumTo_exch _ NS1 (Q4 * Q4)]
    exact sumTo_congr _ (fun σ1 _ => csum_tsumN v (fun c w => G σ1 σ2 c w))
  rw [sumTo_congr _ (fun c _ => hreal c), sumTo_congr _ (fun c _ => hsim c), ex rv, ex sv]
  calc sumTo NS2 (fun σ2 => sumTo NS1 (fun σ1 => tsumN NR m (fun α β r t =>
        indB (genB β && G σ1 σ2 (efIdx β + Q4 * efIdx α) (rv α β r t)))))
      ≤ sumTo NS2 (fun σ2 => sumTo NS1 (fun σ1 => tsumN NR m (fun α β r t =>
        indB (genB β && G σ1 σ2 (efIdx β + Q4 * efIdx α) (sv α β r t))) + (e1 + e2))) :=
        sumTo_mono _ (fun σ2 _ => sumTo_mono _ (fun σ1 _ => (tsumN_ab rv sv hrv hsv h1' h2' _).1))
    _ = _ := by
      simp only [sumTo_add, sumTo_const, Nat.mul_add]
      ac_rfl

/-- **`fs_zk3U` with the views reading the three tables** (`fs_zk3T`
    unguarded): the guarded-out mass `B` in the bound. -/
theorem fs_zk3UT {X Vw : Type} {K1 K2 K3 n1 n2 n3 ε : Nat} (hK1 : 0 < K1) (hK2 : 0 < K2) (hK3 : 0 < K3)
    (sm : (X → Nat) → Nat)
    (hsm : ∀ (N : Nat) (f : Nat → X → Nat), sm (fun x => sumTo N (fun i => f i x)) = sumTo N (fun i => sm (f i)))
    (m1 : X → Nat) (m2 : Nat → X → Nat) (m3 : Nat → Nat → X → Nat) (hm1 : ∀ x, m1 x < n1)
    (hm2 : ∀ c x, m2 c x < n2) (hm3 : ∀ c c' x, m3 c c' x < n3)
    (s1 s2 s3 : Nat → Nat → Nat → X → Nat) (rvT svT : Nat → Nat → Nat → Nat → Nat → Nat → X → Vw)
    (gd : Nat → Nat → Nat → Bool)
    (h : ∀ (H1 H2 H3 : Nat) (F : Nat → Nat → Nat → Nat → Nat → Nat → Vw → Bool),
      sumTo K1 (fun c1 => sumTo K2 (fun c2 => sumTo K3 (fun c3 => sm (fun x =>
        indB (gd c1 c2 c3 && F c1 c2 c3 (m1 x) (m2 c1 x) (m3 c1 c2 x)
          (rvT (rset K1 (m1 x) H1 c1) (rset K2 (m2 c1 x) H2 c2) (rset K3 (m3 c1 c2 x) H3 c3) c1 c2 c3 x)))))) ≤
      sumTo K1 (fun c1 => sumTo K2 (fun c2 => sumTo K3 (fun c3 => sm (fun x =>
        indB (gd c1 c2 c3 && F c1 c2 c3 (s1 c1 c2 c3 x) (s2 c1 c2 c3 x) (s3 c1 c2 c3 x)
          (svT (rset K1 (s1 c1 c2 c3 x) H1 c1) (rset K2 (s2 c1 c2 c3 x) H2 c2) (rset K3 (s3 c1 c2 c3 x) H3 c3)
            c1 c2 c3 x)))))) + ε)
    (E : Nat → Nat → Nat → Nat → Nat → Nat → Vw → Bool) :
    let B := sumTo K1 (fun c1 => sumTo K2 (fun c2 => sumTo K3 (fun c3 => sm (fun _ => indB (!gd c1 c2 c3)))))
    K1 * (K2 * (K3 * sumTo (K1 ^ n1) (fun H1 => sumTo (K2 ^ n2) (fun H2 => sumTo (K3 ^ n3) (fun H3 => sm (fun x =>
      indB (E H1 H2 H3 (m1 x) (m2 (rget K1 (m1 x) H1) x) (m3 (rget K1 (m1 x) H1) (rget K2 (m2 (rget K1 (m1 x) H1) x) H2) x)
          (rvT H1 H2 H3 (rget K1 (m1 x) H1) (rget K2 (m2 (rget K1 (m1 x) H1) x) H2)
            (rget K3 (m3 (rget K1 (m1 x) H1) (rget K2 (m2 (rget K1 (m1 x) H1) x) H2) x) H3) x)))))))) ≤
    sumTo (K1 ^ n1) (fun H1 => sumTo (K2 ^ n2) (fun H2 => sumTo (K3 ^ n3) (fun H3 => sumTo K1 (fun c1 =>
      sumTo K2 (fun c2 => sumTo K3 (fun c3 => sm (fun x =>
        indB (E (rset K1 (s1 c1 c2 c3 x) H1 c1) (rset K2 (s2 c1 c2 c3 x) H2 c2)
          (rset K3 (s3 c1 c2 c3 x) H3 c3) (s1 c1 c2 c3 x) (s2 c1 c2 c3 x) (s3 c1 c2 c3 x)
          (svT (rset K1 (s1 c1 c2 c3 x) H1 c1) (rset K2 (s2 c1 c2 c3 x) H2 c2) (rset K3 (s3 c1 c2 c3 x) H3 c3)
            c1 c2 c3 x))))))))) +
      K1 ^ n1 * (K2 ^ n2 * (K3 ^ n3 * (ε + B))) := by
  intro B
  -- the real count splits at the guard
  have split : ∀ (G : X → Bool) (F : X → Bool), sm (fun x => indB (F x)) ≤
      sm (fun x => indB (G x && F x)) + sm (fun x => indB (!G x)) := fun G F => by
    rw [← sm_add sm hsm]
    exact sm_mono sm hsm (fun x => by cases G x <;> cases F x <;> decide)
  have hg := fs_zk3T hK1 hK2 hK3 sm hsm m1 m2 m3 hm1 hm2 hm3 s1 s2 s3 rvT svT gd h E
  have hb := fs_real3 (Vw := X) hK1 hK2 hK3 sm hsm m1 m2 m3 hm1 hm2 hm3 (fun _ _ _ x => x)
    (fun _ _ _ c1 c2 c3 _ _ _ _ => !gd c1 c2 c3)
  simp only [sumTo_const] at hb
  have hs : ∀ H1 H2 H3, sumTo K1 (fun c1 => sumTo K2 (fun c2 => sumTo K3 (fun c3 => sm (fun x =>
      indB (gd c1 c2 c3 && E (rset K1 (s1 c1 c2 c3 x) H1 c1) (rset K2 (s2 c1 c2 c3 x) H2 c2)
        (rset K3 (s3 c1 c2 c3 x) H3 c3) (s1 c1 c2 c3 x) (s2 c1 c2 c3 x) (s3 c1 c2 c3 x)
        (svT (rset K1 (s1 c1 c2 c3 x) H1 c1) (rset K2 (s2 c1 c2 c3 x) H2 c2) (rset K3 (s3 c1 c2 c3 x) H3 c3)
          c1 c2 c3 x)))))) ≤
      sumTo K1 (fun c1 => sumTo K2 (fun c2 => sumTo K3 (fun c3 => sm (fun x =>
      indB (E (rset K1 (s1 c1 c2 c3 x) H1 c1) (rset K2 (s2 c1 c2 c3 x) H2 c2)
        (rset K3 (s3 c1 c2 c3 x) H3 c3) (s1 c1 c2 c3 x) (s2 c1 c2 c3 x) (s3 c1 c2 c3 x)
        (svT (rset K1 (s1 c1 c2 c3 x) H1 c1) (rset K2 (s2 c1 c2 c3 x) H2 c2) (rset K3 (s3 c1 c2 c3 x) H3 c3)
          c1 c2 c3 x)))))) :=
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
          (rvT H1 H2 H3 (rget K1 (m1 x) H1) (rget K2 (m2 (rget K1 (m1 x) H1) x) H2)
            (rget K3 (m3 (rget K1 (m1 x) H1) (rget K2 (m2 (rget K1 (m1 x) H1) x) H2) x) H3) x)))))
  simp only [sumTo_add] at hR
  have hR' := Nat.mul_le_mul_left K1 (Nat.mul_le_mul_left K2 (Nat.mul_le_mul_left K3 hR))
  simp only [Nat.mul_add] at hR' ⊢
  rw [hb] at hR'
  exact Nat.le_trans (Nat.le_trans hR' (Nat.add_le_add_right (Nat.le_trans hg (Nat.add_le_add_right hS _)) _))
    (Nat.le_of_eq (Nat.add_assoc _ _ _))

/-- **`fs_open3U` with the openings reading the three tables, the third
    message and the view** (`Pf1T T1 T2 T3 M w`): hiding given at every
    choice.  The openings' extra arguments carry a fourth round's table
    read at a function of the third message and the view (`fs_open4T`). -/
theorem fs_open3UT {PV PB D1 O1 P1 D2 O2 P2 D3 O3 P3 : Type} {NR m e1 e2 NS1 NS2 NS3 K2 K3 n1 n2 n3 : Nat}
    (hK2 : 0 < K2) (hK3 : 0 < K3)
    (rv sv : Nat → Nat → EF → EF → Nat → (Nat → Tup) → TViewN PV PB) (gz : Nat → Nat → Bool)
    {Bz : Nat} (hgz : sumTo K2 (fun c2 => sumTo K3 (fun c3 => indB (!gz c2 c3))) ≤ Bz)
    (hrv : ∀ c2 c3 α β r t, rv c2 c3 α β r t = none ∨ ∃ p x y, rv c2 c3 α β r t = some (p, α, β, x, y))
    (hsv : ∀ c2 c3 α β r t, ∃ p x y, sv c2 c3 α β r t = some (p, α, β, x, y))
    (h1 : ∀ c2 c3, gz c2 c3 = true → ∀ E : TViewN PV PB → Bool,
      tsumN NR m (fun α β r t => indB (genB β && E (rv c2 c3 α β r t))) ≤
        tsumN NR m (fun α β r t => indB (genB β && E (sv c2 c3 α β r t))) + e1 + e2)
    (h2 : ∀ c2 c3, gz c2 c3 = true → ∀ E : TViewN PV PB → Bool,
      tsumN NR m (fun α β r t => indB (genB β && E (sv c2 c3 α β r t))) ≤
        tsumN NR m (fun α β r t => indB (genB β && E (rv c2 c3 α β r t))) + e1 + e2)
    (Com1 : D1 → Nat → Nat)
    (Pf1T : Nat → Nat → Nat → Nat → TViewN PV PB → D1 → Nat → P1) (op1 : D1 → O1) (sd1 : O1 → D1) (d1 : D1)
    (hc1 : ComHides NS1 Com1) (hp1 : ∀ T1 T2 T3 M w, ComPfHides NS1 Com1 (Pf1T T1 T2 T3 M w) op1) (hr1 : ∀ d σ, Com1 d σ < n1)
    (ov1 : TViewN PV PB → Option O1) (hov1 : ov1 none = none) (main1 : (Nat → Tup) → Nat → D1)
    (hsd1 : ∀ t r, op1 (sd1 (op1 (main1 t r))) = op1 (main1 t r))
    (Com2 : D2 → Nat → Nat)
    (Pf2T : Nat → Nat → Nat → Nat → TViewN PV PB → D2 → Nat → P2) (op2 : D2 → O2) (sd2 : O2 → D2) (d2 : D2)
    (hc2 : ComHides NS2 Com2) (hp2 : ∀ T1 T2 T3 M w, ComPfHides NS2 Com2 (Pf2T T1 T2 T3 M w) op2) (hr2 : ∀ d σ, Com2 d σ < n2)
    (ov2 : TViewN PV PB → Option O2) (hov2 : ov2 none = none) (main2 : Nat → (Nat → Tup) → Nat → D2)
    (hsd2 : ∀ c t r, op2 (sd2 (op2 (main2 c t r))) = op2 (main2 c t r))
    (Com3 : D3 → Nat → Nat)
    (Pf3T : Nat → Nat → Nat → Nat → TViewN PV PB → D3 → Nat → P3) (op3 : D3 → O3) (sd3 : O3 → D3) (d3 : D3)
    (hc3 : ComHides NS3 Com3) (hp3 : ∀ T1 T2 T3 M w, ComPfHides NS3 Com3 (Pf3T T1 T2 T3 M w) op3) (hr3 : ∀ d σ, Com3 d σ < n3)
    (ov3 : TViewN PV PB → Option O3) (hov3 : ov3 none = none) (main3 : Nat → Nat → (Nat → Tup) → Nat → D3)
    (hsd3 : ∀ c c' t r, op3 (sd3 (op3 (main3 c c' t r))) = op3 (main3 c c' t r))
    (hvo1 : ∀ c2 c3 c r t, rv c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t = none ∨
      ov1 (rv c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (op1 (main1 t r)))
    (hvo2 : ∀ c2 c3 c r t, rv c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t = none ∨
      ov2 (rv c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (op2 (main2 c t r)))
    (hvo3 : ∀ c2 c3 c r t, rv c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t = none ∨
      ov3 (rv c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (op3 (main3 c c2 t r)))
    (sop1 : Nat → Nat → Nat → (Nat → Tup) → O1) (sop2 : Nat → Nat → Nat → Nat → (Nat → Tup) → O2)
    (sop3 : Nat → Nat → Nat → Nat → (Nat → Tup) → O3)
    (hsvo1 : ∀ c2 c3 c r t, ov1 (sv c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (sop1 c2 c3 r t))
    (hsvo2 : ∀ c2 c3 c r t, ov2 (sv c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (sop2 c2 c3 c r t))
    (hsvo3 : ∀ c2 c3 c r t, ov3 (sv c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (sop3 c2 c3 c r t))
    (E : Nat → Nat → Nat → Nat → Nat → Nat → Option P1 × Option (P2 × P3) × TViewN PV PB → Bool) :
    let sm := fun (g : Nat × Nat × Nat × (Nat → Tup) → Nat) =>
      sumTo NS1 (fun σ1 => sumTo (NS2 * NS3) (fun σ => sumTo NR (fun r => sumN m (fun t => g (σ1, σ, r, t)))))
    let m1 := fun (x : Nat × Nat × Nat × (Nat → Tup)) => Com1 (main1 x.2.2.2 x.2.2.1) x.1
    let m2 := fun (c1 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      m1 x + n1 * Com2 (main2 c1 x.2.2.2 x.2.2.1) (x.2.1 % NS2)
    let m3 := fun (c1 c2 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      m1 x + n1 * comPair NS2 n2 Com2 Com3 (main2 c1 x.2.2.2 x.2.2.1, main3 c1 c2 x.2.2.2 x.2.2.1) x.2.1
    let rvo := fun (T1 T2 T3 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      ((ov1 (rv c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)).map (fun _ => Pf1T T1 T2 T3 (m3 c1 c2 x)
         (rv c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2) (main1 x.2.2.2 x.2.2.1) x.1),
       (ovPair ov2 ov3 (rv c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)).map
         (fun _ => pfPair NS2
           (Pf2T T1 T2 T3 (m3 c1 c2 x) (rv c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2))
           (Pf3T T1 T2 T3 (m3 c1 c2 x) (rv c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)) (main2 c1 x.2.2.2 x.2.2.1, main3 c1 c2 x.2.2.2 x.2.2.1) x.2.1),
       rv c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)
    let s1 := fun (_ c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) => Com1 (sd1 (sop1 c2 c3 x.2.2.1 x.2.2.2)) x.1
    let s2 := fun (c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      s1 c1 c2 c3 x + n1 * Com2 (sd2 (sop2 c2 c3 c1 x.2.2.1 x.2.2.2)) (x.2.1 % NS2)
    let s3 := fun (c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      s1 c1 c2 c3 x + n1 * comPair NS2 n2 Com2 Com3
        (sd2 (sop2 c2 c3 c1 x.2.2.1 x.2.2.2), sd3 (sop3 c2 c3 c1 x.2.2.1 x.2.2.2)) x.2.1
    let svo := fun (T1 T2 T3 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      (some (Pf1T T1 T2 T3 (s3 c1 c2 c3 x) (sv c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)
        (sd1 (sop1 c2 c3 x.2.2.1 x.2.2.2)) x.1),
       some (pfPair NS2
         (Pf2T T1 T2 T3 (s3 c1 c2 c3 x) (sv c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2))
         (Pf3T T1 T2 T3 (s3 c1 c2 c3 x) (sv c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)) (sd2 (sop2 c2 c3 c1 x.2.2.1 x.2.2.2), sd3 (sop3 c2 c3 c1 x.2.2.1 x.2.2.2)) x.2.1),
       sv c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)
    let gd := fun (c1 c2 c3 : Nat) => genB (efOf (c1 % Q4)) && gz c2 c3
    (Q4 * Q4) * (K2 * (K3 * sumTo ((Q4 * Q4) ^ n1) (fun H1 => sumTo (K2 ^ (n1 * n2)) (fun H2 =>
      sumTo (K3 ^ (n1 * (n2 * n3))) (fun H3 => sm (fun x =>
      indB (E H1 H2 H3 (m1 x) (m2 (rget (Q4 * Q4) (m1 x) H1) x)
          (m3 (rget (Q4 * Q4) (m1 x) H1) (rget K2 (m2 (rget (Q4 * Q4) (m1 x) H1) x) H2) x)
          (rvo H1 H2 H3 (rget (Q4 * Q4) (m1 x) H1) (rget K2 (m2 (rget (Q4 * Q4) (m1 x) H1) x) H2)
            (rget K3 (m3 (rget (Q4 * Q4) (m1 x) H1) (rget K2 (m2 (rget (Q4 * Q4) (m1 x) H1) x) H2) x) H3) x)))))))) ≤
    sumTo ((Q4 * Q4) ^ n1) (fun H1 => sumTo (K2 ^ (n1 * n2)) (fun H2 => sumTo (K3 ^ (n1 * (n2 * n3))) (fun H3 =>
      sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo K3 (fun c3 => sm (fun x =>
        indB (E (rset (Q4 * Q4) (s1 c1 c2 c3 x) H1 c1) (rset K2 (s2 c1 c2 c3 x) H2 c2)
          (rset K3 (s3 c1 c2 c3 x) H3 c3) (s1 c1 c2 c3 x) (s2 c1 c2 c3 x) (s3 c1 c2 c3 x)
          (svo (rset (Q4 * Q4) (s1 c1 c2 c3 x) H1 c1) (rset K2 (s2 c1 c2 c3 x) H2 c2) (rset K3 (s3 c1 c2 c3 x) H3 c3)
            c1 c2 c3 x))))))))) +
      (Q4 * Q4) ^ n1 * (K2 ^ (n1 * n2) * (K3 ^ (n1 * (n2 * n3)) *
        (K2 * (K3 * (NS1 * (NS2 * NS3 * (e1 + e2)))) +
          (Q4 * (P * P) * (K2 * K3) + Q4 * Q4 * Bz) * (NS1 * (NS2 * NS3 * (NR * (Q4 ^ m * 1))))))) := by
  intro sm m1 m2 m3 rvo s1 s2 s3 svo gd
  have hsm : ∀ (N : Nat) (f : Nat → Nat × Nat × Nat × (Nat → Tup) → Nat),
      sm (fun x => sumTo N (fun i => f i x)) = sumTo N (fun i => sm (f i)) := fun N f => by
    show sumTo NS1 (fun σ1 => sumTo (NS2 * NS3) (fun σ => sumTo NR (fun r => sumN m (fun t =>
      sumTo N (fun i => f i (σ1, σ, r, t)))))) = _
    rw [sumTo_congr _ (fun σ1 _ => sm_exch (NS := NS2 * NS3) (NR := NR) (m := m) (N := N)
      (fun i σ r t => f i (σ1, σ, r, t)))]
    exact sumTo_exch _ N NS1
  have hc23 : ∀ d σ, comPair NS2 n2 Com2 Com3 d σ < n2 * n3 := fun d σ => by
    unfold comPair; exact pair_lt (hr2 _ _) (hr3 _ _)
  refine Nat.le_trans (fs_zk3UT (K1 := Q4 * Q4) (K2 := K2) (K3 := K3) (n1 := n1) (n2 := n1 * n2) (n3 := n1 * (n2 * n3))
    (ε := K2 * (K3 * (NS1 * (NS2 * NS3 * (e1 + e2)))))
    (Nat.mul_pos Q4_pos Q4_pos) hK2 hK3 sm hsm m1 m2 m3 (fun x => hr1 _ _) (fun _ x => pair_lt (hr1 _ _) (hr2 _ _))
    (fun _ _ x => pair_lt (hr1 _ _) (hc23 _ _)) s1 s2 s3 rvo svo gd (fun H1 H2 H3 F => ?_) E) ?_
  rw [sumTo_exch _ K2 (Q4 * Q4), sumTo_exch _ K2 (Q4 * Q4)]
  rw [sumTo_congr _ (fun c2 _ => sumTo_exch _ K3 (Q4 * Q4)), sumTo_congr _ (fun c2 _ => sumTo_exch _ K3 (Q4 * Q4))]
  rw [← sumTo_const (K3 * (NS1 * (NS2 * NS3 * (e1 + e2)))) K2, ← sumTo_add]
  refine sumTo_mono _ (fun c2 _ => ?_)
  rw [← sumTo_const (NS1 * (NS2 * NS3 * (e1 + e2))) K3, ← sumTo_add]
  refine sumTo_mono _ (fun c3 _ => ?_)
  cases hg : gz c2 c3
  · simp only [gd, hg, Bool.and_false, Bool.false_and]
    exact Nat.le_add_right _ _
  · simp only [gd, hg, Bool.and_true]
    have hov23 : ovPair ov2 ov3 none = none := by unfold ovPair; rw [hov2, hov3]
    have hvo23 : ∀ c r t, rv c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t = none ∨
        ovPair ov2 ov3 (rv c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (op2 (main2 c t r), op3 (main3 c c2 t r)) :=
      fun c r t => by
        rcases hvo2 c2 c3 c r t with e | e
        · exact .inl e
        · rcases hvo3 c2 c3 c r t with e' | e'
          · exact .inl e'
          · exact .inr (by unfold ovPair; rw [e, e'])
    have hsvo23 : ∀ c r t, ovPair ov2 ov3 (sv c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) =
        some (sop2 c2 c3 c r t, sop3 c2 c3 c r t) := fun c r t => by
      unfold ovPair; rw [hsvo2 c2 c3 c r t, hsvo3 c2 c3 c r t]
    have core := open_two_coreV (NR := NR) (m := m) (rv c2 c3) (sv c2 c3) (hrv c2 c3) (hsv c2 c3) (h1 c2 c3 hg)
      (h2 c2 c3 hg) Com1
      (fun c w v d σ => Pf1T (rset (Q4 * Q4) (Com1 d σ) H1 c) (rset K2 (Com1 d σ + n1 * (v % n2)) H2 c2)
        (rset K3 (Com1 d σ + n1 * v) H3 c3) (Com1 d σ + n1 * v) w d σ) op1 sd1 d1 hc1
      (fun c w v => comPf_choose (Pf := fun T d σ => Pf1T (rset (Q4 * Q4) T H1 c) (rset K2 (T + n1 * (v % n2)) H2 c2)
        (rset K3 (T + n1 * v) H3 c3) (T + n1 * v) w d σ) (fun T => hp1 _ _ _ _ _) hr1 id)
      ov1 hov1 main1 hsd1
      (comPair NS2 n2 Com2 Com3)
      (fun c w v d σ => pfPair NS2
        (Pf2T (rset (Q4 * Q4) v H1 c) (rset K2 (v + n1 * (comPair NS2 n2 Com2 Com3 d σ % n2)) H2 c2)
          (rset K3 (v + n1 * comPair NS2 n2 Com2 Com3 d σ) H3 c3) (v + n1 * comPair NS2 n2 Com2 Com3 d σ) w)
        (Pf3T (rset (Q4 * Q4) v H1 c) (rset K2 (v + n1 * (comPair NS2 n2 Com2 Com3 d σ % n2)) H2 c2)
          (rset K3 (v + n1 * comPair NS2 n2 Com2 Com3 d σ) H3 c3) (v + n1 * comPair NS2 n2 Com2 Com3 d σ) w) d σ)
      (fun d => (op2 d.1, op3 d.2)) (fun o => (sd2 o.1, sd3 o.2))
      (d2, d3) (ComHides.prod hc2 hc3)
      (fun c w v => comPf_choose (Pf := fun T d σ => pfPair NS2
        (Pf2T (rset (Q4 * Q4) v H1 c) (rset K2 (v + n1 * (T % n2)) H2 c2) (rset K3 (v + n1 * T) H3 c3) (v + n1 * T) w)
        (Pf3T (rset (Q4 * Q4) v H1 c) (rset K2 (v + n1 * (T % n2)) H2 c2) (rset K3 (v + n1 * T) H3 c3) (v + n1 * T) w)
        d σ)
        (fun T => ComPfHides.prod (hp2 _ _ _ _ _) (hp3 _ _ _ _ _)) hc23 id)
      (ovPair ov2 ov3) hov23
      (fun c t r => (main2 c t r, main3 c c2 t r))
      (fun c t r => by show (op2 (sd2 (op2 (main2 c t r))), op3 (sd3 (op3 (main3 c c2 t r)))) = _; rw [hsd2, hsd3])
      (hvo1 c2 c3) hvo23 (sop1 c2 c3) (fun c r t => (sop2 c2 c3 c r t, sop3 c2 c3 c r t)) (hsvo1 c2 c3) hsvo23
      (fun c a b p q w => F c c2 c3 a (a + n1 * (b % n2)) (a + n1 * b) (p, q, w))
    simp only [comPair_mod Com3 hr2] at core
    exact core
  · refine Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _
      (Nat.add_le_add_left ?_ _)))) _
    have hk : ∀ k, sm (fun _ => k) = NS1 * (NS2 * NS3 * (NR * (Q4 ^ m * 1))) * k := fun k => by
      simp only [sm, sumN_const, sumTo_const, Nat.mul_one, Nat.mul_assoc]
    show sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo K3 (fun c3 =>
      sm (fun _ => indB (!(genB (efOf (c1 % Q4)) && gz c2 c3)))))) ≤ _
    simp only [hk, ← sumTo_mul]
    rw [Nat.mul_comm _ (NS1 * _)]
    exact Nat.mul_le_mul_left _ (bad3_count gz hgz)



/-- **`fs_lastG` with the views reading the fourth table**: after the
    reprogramming the view reads the table set at its message, so the
    bound `hb` is taken at each table. -/
theorem fs_lastGT {Y Vw : Type} {K4 n4 K ε B4 : Nat} (hK4 : 0 < K4) (sm : (Y → Nat) → Nat)
    (hsm : ∀ (N : Nat) (f : Nat → Y → Nat), sm (fun y => sumTo N (fun i => f i y)) = sumTo N (fun i => sm (f i)))
    (M : Y → Nat) (hM : ∀ y, M y < n4) (rvT : Nat → Nat → Y → Vw) (Sim : Nat → Nat → (Nat → Vw → Bool) → Nat)
    (g4 : Nat → Bool) (hB4 : sumTo K4 (fun c4 => indB (!g4 c4)) ≤ B4)
    (hb : ∀ c4, g4 c4 = true → ∀ (H4 : Nat) (G : Nat → Vw → Bool),
      K * sm (fun y => indB (G (M y) (rvT (rset K4 (M y) H4 c4) c4 y))) ≤ Sim H4 c4 G + ε)
    (E : Nat → Nat → Nat → Vw → Bool) :
    K4 * (K * sumTo (K4 ^ n4) (fun H4 => sm (fun y =>
      indB (E H4 (M y) (rget K4 (M y) H4) (rvT H4 (rget K4 (M y) H4) y))))) ≤
      sumTo (K4 ^ n4) (fun H4 => sumTo K4 (fun c4 => Sim H4 c4 (fun m v => E (rset K4 m H4 c4) m c4 v))) +
        K4 ^ n4 * (K4 * ε + B4 * (K * sm (fun _ => 1))) := by
  have hone : ∀ f : Y → Nat, (∀ y, f y ≤ 1) → K * sm f ≤ K * sm (fun _ => 1) := fun f hf =>
    Nat.mul_le_mul_left _ (sm_mono sm hsm hf)
  rw [Nat.mul_left_comm, fs_real (Vw := Y) hK4 sm hsm M hM (fun _ y => y) (fun H4 m c4 y => E H4 m c4 (rvT H4 c4 y)),
    sumTo_mul]
  calc sumTo (K4 ^ n4) (fun H4 => K * sumTo K4 (fun c4 => sm (fun y =>
        indB (E (rset K4 (M y) H4 c4) (M y) c4 (rvT (rset K4 (M y) H4 c4) c4 y)))))
      ≤ sumTo (K4 ^ n4) (fun H4 => sumTo K4 (fun c4 => Sim H4 c4 (fun m v => E (rset K4 m H4 c4) m c4 v) + ε +
          indB (!g4 c4) * (K * sm (fun _ => 1)))) :=
        sumTo_mono _ (fun H4 _ => by
          rw [sumTo_mul]
          refine sumTo_mono _ (fun c4 _ => ?_)
          cases hg : g4 c4
          · rw [Bool.not_false, show indB true = 1 from rfl, Nat.one_mul]
            exact Nat.le_trans (hone _ (fun y => indB_le _)) (Nat.le_add_left _ _)
          · rw [Bool.not_true, show indB false = 0 from rfl, Nat.zero_mul, Nat.add_zero]
            exact hb c4 hg H4 (fun m v => E (rset K4 m H4 c4) m c4 v))
    _ ≤ _ := by
      simp only [sumTo_add, sumTo_const, sumTo_mul_right]
      rw [Nat.mul_add (K4 ^ n4), ← Nat.add_assoc]
      exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hB4)) _

/-- **Fiat–Shamir over four rounds, every commitment opened, the openings
    reading all four oracle tables** (`fs_open4` over `fs_lastGT` and
    `fs_open3UT`): `Pf1T c4 T1 T2 T3 T4 M`, hiding given at every choice of
    tables and of `M`, the third message, whose low digit is the first
    commitment.  After the fourth reprogramming the openings read the fourth
    table set at `φ` of the third message and `oz` of the view; inside, the
    first three as in `fs_open3T`.  Unguarded; one proof per oracle. -/
theorem fs_open4T {PV PB D1 O1 P1 D2 O2 P2 D3 O3 P3 W : Type} {NR m e1 e2 NS1 NS2 NS3 K2 K3 K4 n1 n2 n3 : Nat}
    (hK2 : 0 < K2) (hK3 : 0 < K3) (hK4 : 0 < K4)
    (φ : Nat → W → Nat) {N4 : Nat} (hφ : ∀ m w, φ m w < N4)
    (rv sv : Nat → Nat → Nat → EF → EF → Nat → (Nat → Tup) → TViewN PV PB) (gz : Nat → Nat → Bool)
    {Bz : Nat} (hgz : sumTo K2 (fun c2 => sumTo K3 (fun c3 => indB (!gz c2 c3))) ≤ Bz)
    (g4 : Nat → Bool) {B4 : Nat} (hB4 : sumTo K4 (fun c4 => indB (!g4 c4)) ≤ B4)
    (hrv : ∀ c4 c2 c3 α β r t, rv c4 c2 c3 α β r t = none ∨ ∃ p x y, rv c4 c2 c3 α β r t = some (p, α, β, x, y))
    (hsv : ∀ c4 c2 c3 α β r t, ∃ p x y, sv c4 c2 c3 α β r t = some (p, α, β, x, y))
    (oz : TViewN PV PB → W) (hoz : ∀ c4 c2 c3 α β r t, oz (rv c4 c2 c3 α β r t) = oz (rv 0 c2 c3 α β r t))
    (h1 : ∀ c4 c2 c3, g4 c4 = true → gz c2 c3 = true → ∀ E : TViewN PV PB → Bool,
      tsumN NR m (fun α β r t => indB (genB β && E (rv c4 c2 c3 α β r t))) ≤
        tsumN NR m (fun α β r t => indB (genB β && E (sv c4 c2 c3 α β r t))) + e1 + e2)
    (h2 : ∀ c4 c2 c3, g4 c4 = true → gz c2 c3 = true → ∀ E : TViewN PV PB → Bool,
      tsumN NR m (fun α β r t => indB (genB β && E (sv c4 c2 c3 α β r t))) ≤
        tsumN NR m (fun α β r t => indB (genB β && E (rv c4 c2 c3 α β r t))) + e1 + e2)
    (Com1 : D1 → Nat → Nat) 
    (Pf1T : Nat → Nat → Nat → Nat → Nat → Nat → D1 → Nat → P1) (op1 : Nat → D1 → O1) (sd1 : Nat → O1 → D1) (d1 : D1)
    (hc1 : ComHides NS1 Com1) 
    (hp1 : ∀ c4 T1 T2 T3 T4 M, ComPfHides NS1 Com1 (Pf1T c4 T1 T2 T3 T4 M) (op1 c4)) (hr1 : ∀ d σ, Com1 d σ < n1)
    (ov1 : Nat → TViewN PV PB → Option O1) (hov1 : ∀ c4, ov1 c4 none = none) (main1 : (Nat → Tup) → Nat → D1)
    (hsd1 : ∀ c4 t r, op1 c4 (sd1 c4 (op1 c4 (main1 t r))) = op1 c4 (main1 t r))
    (Com2 : D2 → Nat → Nat) 
    (Pf2T : Nat → Nat → Nat → Nat → Nat → Nat → D2 → Nat → P2) (op2 : Nat → D2 → O2) (sd2 : Nat → O2 → D2) (d2 : D2)
    (hc2 : ComHides NS2 Com2) 
    (hp2 : ∀ c4 T1 T2 T3 T4 M, ComPfHides NS2 Com2 (Pf2T c4 T1 T2 T3 T4 M) (op2 c4)) (hr2 : ∀ d σ, Com2 d σ < n2)
    (ov2 : Nat → TViewN PV PB → Option O2) (hov2 : ∀ c4, ov2 c4 none = none) (main2 : Nat → (Nat → Tup) → Nat → D2)
    (hsd2 : ∀ c4 c t r, op2 c4 (sd2 c4 (op2 c4 (main2 c t r))) = op2 c4 (main2 c t r))
    (Com3 : D3 → Nat → Nat) 
    (Pf3T : Nat → Nat → Nat → Nat → Nat → Nat → D3 → Nat → P3) (op3 : Nat → D3 → O3) (sd3 : Nat → O3 → D3) (d3 : D3)
    (hc3 : ComHides NS3 Com3) 
    (hp3 : ∀ c4 T1 T2 T3 T4 M, ComPfHides NS3 Com3 (Pf3T c4 T1 T2 T3 T4 M) (op3 c4)) (hr3 : ∀ d σ, Com3 d σ < n3)
    (ov3 : Nat → TViewN PV PB → Option O3) (hov3 : ∀ c4, ov3 c4 none = none) (main3 : Nat → Nat → (Nat → Tup) → Nat → D3)
    (hsd3 : ∀ c4 c c' t r, op3 c4 (sd3 c4 (op3 c4 (main3 c c' t r))) = op3 c4 (main3 c c' t r))
    (hvo1 : ∀ c4 c2 c3 c r t, rv c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t = none ∨
      ov1 c4 (rv c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (op1 c4 (main1 t r)))
    (hvo2 : ∀ c4 c2 c3 c r t, rv c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t = none ∨
      ov2 c4 (rv c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (op2 c4 (main2 c t r)))
    (hvo3 : ∀ c4 c2 c3 c r t, rv c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t = none ∨
      ov3 c4 (rv c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (op3 c4 (main3 c c2 t r)))
    (sop1 : Nat → Nat → Nat → Nat → (Nat → Tup) → O1) (sop2 : Nat → Nat → Nat → Nat → Nat → (Nat → Tup) → O2)
    (sop3 : Nat → Nat → Nat → Nat → Nat → (Nat → Tup) → O3)
    (hsvo1 : ∀ c4 c2 c3 c r t, ov1 c4 (sv c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (sop1 c4 c2 c3 r t))
    (hsvo2 : ∀ c4 c2 c3 c r t, ov2 c4 (sv c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (sop2 c4 c2 c3 c r t))
    (hsvo3 : ∀ c4 c2 c3 c r t, ov3 c4 (sv c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (sop3 c4 c2 c3 c r t))
    (E : Nat → Nat → Nat → Nat → Nat → Nat → Nat → Option P1 × Option (P2 × P3) × TViewN PV PB → Bool) :
    let sm := fun (g : Nat × Nat × Nat × (Nat → Tup) → Nat) =>
      sumTo NS1 (fun σ1 => sumTo (NS2 * NS3) (fun σ => sumTo NR (fun r => sumN m (fun t => g (σ1, σ, r, t)))))
    let m1 := fun (x : Nat × Nat × Nat × (Nat → Tup)) => Com1 (main1 x.2.2.2 x.2.2.1) x.1
    let m2 := fun (c1 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      m1 x + n1 * Com2 (main2 c1 x.2.2.2 x.2.2.1) (x.2.1 % NS2)
    let m3 := fun (c1 c2 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      m1 x + n1 * comPair NS2 n2 Com2 Com3 (main2 c1 x.2.2.2 x.2.2.1, main3 c1 c2 x.2.2.2 x.2.2.1) x.2.1
    let rvo := fun (T1 T2 T3 T4 c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      ((ov1 c4 (rv c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)).map (fun _ => Pf1T c4 T1 T2 T3 T4 (m3 c1 c2 x) (main1 x.2.2.2 x.2.2.1) x.1),
       (ovPair (ov2 c4) (ov3 c4) (rv c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)).map
         (fun _ => pfPair NS2 (Pf2T c4 T1 T2 T3 T4 (m3 c1 c2 x)) (Pf3T c4 T1 T2 T3 T4 (m3 c1 c2 x)) (main2 c1 x.2.2.2 x.2.2.1, main3 c1 c2 x.2.2.2 x.2.2.1) x.2.1),
       rv c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)
    let s1 := fun (c4 _c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) => Com1 (sd1 c4 (sop1 c4 c2 c3 x.2.2.1 x.2.2.2)) x.1
    let s2 := fun (c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      s1 c4 c1 c2 c3 x + n1 * Com2 (sd2 c4 (sop2 c4 c2 c3 c1 x.2.2.1 x.2.2.2)) (x.2.1 % NS2)
    let s3 := fun (c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      s1 c4 c1 c2 c3 x + n1 * comPair NS2 n2 Com2 Com3
        (sd2 c4 (sop2 c4 c2 c3 c1 x.2.2.1 x.2.2.2), sd3 c4 (sop3 c4 c2 c3 c1 x.2.2.1 x.2.2.2)) x.2.1
    let svo := fun (T1 T2 T3 T4 c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      (some (Pf1T c4 T1 T2 T3 T4 (s3 c4 c1 c2 c3 x) (sd1 c4 (sop1 c4 c2 c3 x.2.2.1 x.2.2.2)) x.1),
       some (pfPair NS2 (Pf2T c4 T1 T2 T3 T4 (s3 c4 c1 c2 c3 x)) (Pf3T c4 T1 T2 T3 T4 (s3 c4 c1 c2 c3 x)) (sd2 c4 (sop2 c4 c2 c3 c1 x.2.2.1 x.2.2.2), sd3 c4 (sop3 c4 c2 c3 c1 x.2.2.1 x.2.2.2)) x.2.1),
       sv c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)
    let sm4 := fun (g : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup)) → Nat) =>
      sumTo ((Q4 * Q4) ^ n1) (fun H1 => sumTo (K2 ^ (n1 * n2)) (fun H2 =>
        sumTo (K3 ^ (n1 * (n2 * n3))) (fun H3 => sm (fun x => g (H1, H2, H3, x)))))
    let r1 := fun (y : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup))) => rget (Q4 * Q4) (m1 y.2.2.2) y.1
    let r2 := fun (y : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup))) => rget K2 (m2 (r1 y) y.2.2.2) y.2.1
    let r3 := fun (y : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup))) => rget K3 (m3 (r1 y) (r2 y) y.2.2.2) y.2.2.1
    let Mq := fun (y : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup))) => φ (m3 (r1 y) (r2 y) y.2.2.2)
      (oz (rv 0 (r2 y) (r3 y) (efOf (r1 y / Q4)) (efOf (r1 y % Q4)) y.2.2.2.2.2.1 y.2.2.2.2.2.2))
    K4 * (Q4 * Q4 * (K2 * K3) * sumTo (K4 ^ N4) (fun H4 => sm4 (fun y =>
      indB (E y.1 y.2.1 y.2.2.1 H4 (m1 y.2.2.2) (m2 (r1 y) y.2.2.2) (m3 (r1 y) (r2 y) y.2.2.2)
        (rvo y.1 y.2.1 y.2.2.1 H4 (rget K4 (Mq y) H4) (r1 y) (r2 y) (r3 y) y.2.2.2))))) ≤
    sumTo (K4 ^ N4) (fun H4 => sumTo K4 (fun c4 =>
      sumTo ((Q4 * Q4) ^ n1) (fun H1 => sumTo (K2 ^ (n1 * n2)) (fun H2 => sumTo (K3 ^ (n1 * (n2 * n3))) (fun H3 =>
      sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo K3 (fun c3 => sm (fun x =>
        indB (E (rset (Q4 * Q4) (s1 c4 c1 c2 c3 x) H1 c1) (rset K2 (s2 c4 c1 c2 c3 x) H2 c2)
          (rset K3 (s3 c4 c1 c2 c3 x) H3 c3) (rset K4 (φ (s3 c4 c1 c2 c3 x) (oz (sv c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2))) H4 c4)
          (s1 c4 c1 c2 c3 x) (s2 c4 c1 c2 c3 x) (s3 c4 c1 c2 c3 x)
          (svo (rset (Q4 * Q4) (s1 c4 c1 c2 c3 x) H1 c1) (rset K2 (s2 c4 c1 c2 c3 x) H2 c2)
            (rset K3 (s3 c4 c1 c2 c3 x) H3 c3)
            (rset K4 (φ (s3 c4 c1 c2 c3 x) (oz (sv c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2))) H4 c4)
            c4 c1 c2 c3 x))))))))))) +
      K4 ^ N4 * (K4 * ((Q4 * Q4) ^ n1 * (K2 ^ (n1 * n2) * (K3 ^ (n1 * (n2 * n3)) *
        (K2 * (K3 * (NS1 * (NS2 * NS3 * (e1 + e2)))) +
          (Q4 * (P * P) * (K2 * K3) + Q4 * Q4 * Bz) * (NS1 * (NS2 * NS3 * (NR * (Q4 ^ m * 1)))))))) +
          B4 * (Q4 * Q4 * (K2 * K3) * sm4 (fun _ => 1))) := by
  intro sm m1 m2 m3 rvo s1 s2 s3 svo sm4 r1 r2 r3 Mq
  have hsm : ∀ (N : Nat) (f : Nat → Nat × Nat × Nat × (Nat → Tup) → Nat),
      sm (fun x => sumTo N (fun i => f i x)) = sumTo N (fun i => sm (f i)) := fun N f => by
    show sumTo NS1 (fun σ1 => sumTo (NS2 * NS3) (fun σ => sumTo NR (fun r => sumN m (fun t =>
      sumTo N (fun i => f i (σ1, σ, r, t)))))) = _
    rw [sumTo_congr _ (fun σ1 _ => sm_exch (NS := NS2 * NS3) (NR := NR) (m := m) (N := N)
      (fun i σ r t => f i (σ1, σ, r, t)))]
    exact sumTo_exch _ N NS1
  have hc23 : ∀ d σ, comPair NS2 n2 Com2 Com3 d σ < n2 * n3 := fun d σ => by
    unfold comPair; exact pair_lt (hr2 _ _) (hr3 _ _)
  have hsm4 : ∀ (N : Nat) (f : Nat → Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup)) → Nat),
      sm4 (fun y => sumTo N (fun i => f i y)) = sumTo N (fun i => sm4 (f i)) := fun N f => by
    show sumTo ((Q4 * Q4) ^ n1) (fun H1 => sumTo (K2 ^ (n1 * n2)) (fun H2 =>
        sumTo (K3 ^ (n1 * (n2 * n3))) (fun H3 => sm (fun x => sumTo N (fun i => f i (H1, H2, H3, x)))))) = _
    simp only [hsm N]
    rw [sumTo_congr _ (fun H1 _ => sumTo_congr _ (fun H2 _ => sumTo_exch _ N (K3 ^ (n1 * (n2 * n3)))))]
    rw [sumTo_congr _ (fun H1 _ => sumTo_exch _ N (K2 ^ (n1 * n2)))]
    exact sumTo_exch _ N ((Q4 * Q4) ^ n1)
  refine fs_lastGT (K := Q4 * Q4 * (K2 * K3)) (n4 := N4) hK4 sm4 hsm4 Mq
    (fun y => hφ _ _)
    (fun T4 c4 y => (y.1, y.2.1, y.2.2.1, m1 y.2.2.2, m2 (r1 y) y.2.2.2, m3 (r1 y) (r2 y) y.2.2.2,
      rvo y.1 y.2.1 y.2.2.1 T4 c4 (r1 y) (r2 y) (r3 y) y.2.2.2))
    (fun H4 c4 G => sumTo ((Q4 * Q4) ^ n1) (fun H1 => sumTo (K2 ^ (n1 * n2)) (fun H2 => sumTo (K3 ^ (n1 * (n2 * n3)))
      (fun H3 => sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo K3 (fun c3 => sm (fun x =>
        indB (G (φ (s3 c4 c1 c2 c3 x) (oz (sv c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2))) (rset (Q4 * Q4) (s1 c4 c1 c2 c3 x) H1 c1, rset K2 (s2 c4 c1 c2 c3 x) H2 c2,
          rset K3 (s3 c4 c1 c2 c3 x) H3 c3, s1 c4 c1 c2 c3 x, s2 c4 c1 c2 c3 x, s3 c4 c1 c2 c3 x,
          svo (rset (Q4 * Q4) (s1 c4 c1 c2 c3 x) H1 c1) (rset K2 (s2 c4 c1 c2 c3 x) H2 c2) (rset K3 (s3 c4 c1 c2 c3 x) H3 c3)
            (rset K4 (φ (s3 c4 c1 c2 c3 x) (oz (sv c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2))) H4 c4)
            c4 c1 c2 c3 x))))))))))
    g4 hB4 (fun c4 hg4 H4 G => ?_) (fun H4 _ c4 v => E v.1 v.2.1 v.2.2.1 H4 v.2.2.2.1 v.2.2.2.2.1 v.2.2.2.2.2.1 v.2.2.2.2.2.2)
  have h3 := fs_open3UT hK2 hK3 (rv c4) (sv c4) gz hgz (hrv c4) (hsv c4) (fun c2 c3 hg => h1 c4 c2 c3 hg4 hg) (fun c2 c3 hg => h2 c4 c2 c3 hg4 hg)
    Com1 (fun T1 T2 T3 M w => Pf1T c4 T1 T2 T3 (rset K4 (φ M (oz w)) H4 c4) M) (op1 c4) (sd1 c4) d1 hc1
    (fun T1 T2 T3 M w => hp1 c4 T1 T2 T3 _ M) hr1 (ov1 c4) (hov1 c4) main1 (hsd1 c4)
    Com2 (fun T1 T2 T3 M w => Pf2T c4 T1 T2 T3 (rset K4 (φ M (oz w)) H4 c4) M) (op2 c4) (sd2 c4) d2 hc2
    (fun T1 T2 T3 M w => hp2 c4 T1 T2 T3 _ M) hr2 (ov2 c4) (hov2 c4) main2 (hsd2 c4)
    Com3 (fun T1 T2 T3 M w => Pf3T c4 T1 T2 T3 (rset K4 (φ M (oz w)) H4 c4) M) (op3 c4) (sd3 c4) d3 hc3
    (fun T1 T2 T3 M w => hp3 c4 T1 T2 T3 _ M) hr3 (ov3 c4) (hov3 c4) main3 (hsd3 c4)
    (hvo1 c4) (hvo2 c4) (hvo3 c4) (sop1 c4) (sop2 c4) (sop3 c4) (hsvo1 c4) (hsvo2 c4) (hsvo3 c4)
    (fun H1 H2 H3 a b c v => G (φ c (oz v.2.2)) (H1, H2, H3, a, b, c, v))
  simp only [Mq, ← hoz c4]
  rw [Nat.mul_assoc, Nat.mul_assoc K2]
  exact h3

/-- **Four Fiat–Shamir rounds, the first commitment drawn from the oracle,
    the distinguisher's queries and the later openings reading all four
    Fiat–Shamir tables** (`nxtT` at the tables each side uses): `fs_open4ROM` with the
    transfer at each choice of tables and `fs_open4T` at the ideal opening.
    One direction, with `fs_open4ROM`'s other limits. -/
theorem fs_open4ROMT {PV PB D O Pq D2 O2 P2 D3 O3 P3 W : Type}
    {K NR m e1 e2 NSh NSo s k n NS2 NS3 K2 K3 K4 n2 n3 : Nat}
    (hK : 0 < K) (hK2 : 0 < K2) (hK3 : 0 < K3) (hK4 : 0 < K4)
    (φ : Nat → W → Nat) {N4 : Nat} (hφ : ∀ m w, φ m w < N4)
    (rv sv : Nat → Nat → Nat → EF → EF → Nat → (Nat → Tup) → TViewN PV PB) (gz : Nat → Nat → Bool)
    {Bz : Nat} (hgz : sumTo K2 (fun c2 => sumTo K3 (fun c3 => indB (!gz c2 c3))) ≤ Bz)
    (g4 : Nat → Bool) {B4 : Nat} (hB4 : sumTo K4 (fun c4 => indB (!g4 c4)) ≤ B4)
    (hrv : ∀ c4 c2 c3 α β r t, rv c4 c2 c3 α β r t = none ∨ ∃ p x y, rv c4 c2 c3 α β r t = some (p, α, β, x, y))
    (hsv : ∀ c4 c2 c3 α β r t, ∃ p x y, sv c4 c2 c3 α β r t = some (p, α, β, x, y))
    (oz : TViewN PV PB → W) (hoz : ∀ c4 c2 c3 α β r t, oz (rv c4 c2 c3 α β r t) = oz (rv 0 c2 c3 α β r t))
    (h1 : ∀ c4 c2 c3, g4 c4 = true → gz c2 c3 = true → ∀ E : TViewN PV PB → Bool,
      tsumN NR m (fun α β r t => indB (genB β && E (rv c4 c2 c3 α β r t))) ≤
        tsumN NR m (fun α β r t => indB (genB β && E (sv c4 c2 c3 α β r t))) + e1 + e2)
    (h2 : ∀ c4 c2 c3, g4 c4 = true → gz c2 c3 = true → ∀ E : TViewN PV PB → Bool,
      tsumN NR m (fun α β r t => indB (genB β && E (sv c4 c2 c3 α β r t))) ≤
        tsumN NR m (fun α β r t => indB (genB β && E (rv c4 c2 c3 α β r t))) + e1 + e2)
    (pos : D → Nat → Nat → Nat) (hpos : ∀ d σo σh, pos d σo σh < n) (g : O → Nat → Pq)
    (hs : ∀ d σo v, sumTo NSh (fun σh => indB (decide (pos d σo σh = v))) ≤ s)
    (nxtT : Nat → Nat → Nat → Nat → Pq → Nat → List Nat → Nat) (op1 : Nat → D → O) (sd1 : Nat → O → D) (d1 : D)
    (ov1 : Nat → TViewN PV PB → Option O) (hov1 : ∀ c4, ov1 c4 none = none) (main1 : (Nat → Tup) → Nat → D)
    (hsd1 : ∀ c4 t r, op1 c4 (sd1 c4 (op1 c4 (main1 t r))) = op1 c4 (main1 t r))
    (Com2 : D2 → Nat → Nat) 
    (Pf2T : Nat → Nat → Nat → Nat → Nat → Nat → D2 → Nat → P2) (op2 : Nat → D2 → O2) (sd2 : Nat → O2 → D2) (d2 : D2)
    (hc2 : ComHides NS2 Com2) 
    (hp2 : ∀ c4 T1 T2 T3 T4 M, ComPfHides NS2 Com2 (Pf2T c4 T1 T2 T3 T4 M) (op2 c4)) (hr2 : ∀ d σ, Com2 d σ < n2)
    (ov2 : Nat → TViewN PV PB → Option O2) (hov2 : ∀ c4, ov2 c4 none = none) (main2 : Nat → (Nat → Tup) → Nat → D2)
    (hsd2 : ∀ c4 c t r, op2 c4 (sd2 c4 (op2 c4 (main2 c t r))) = op2 c4 (main2 c t r))
    (Com3 : D3 → Nat → Nat) 
    (Pf3T : Nat → Nat → Nat → Nat → Nat → Nat → D3 → Nat → P3) (op3 : Nat → D3 → O3) (sd3 : Nat → O3 → D3) (d3 : D3)
    (hc3 : ComHides NS3 Com3) 
    (hp3 : ∀ c4 T1 T2 T3 T4 M, ComPfHides NS3 Com3 (Pf3T c4 T1 T2 T3 T4 M) (op3 c4)) (hr3 : ∀ d σ, Com3 d σ < n3)
    (ov3 : Nat → TViewN PV PB → Option O3) (hov3 : ∀ c4, ov3 c4 none = none) (main3 : Nat → Nat → (Nat → Tup) → Nat → D3)
    (hsd3 : ∀ c4 c c' t r, op3 c4 (sd3 c4 (op3 c4 (main3 c c' t r))) = op3 c4 (main3 c c' t r))
    (hvo1 : ∀ c4 c2 c3 c r t, rv c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t = none ∨
      ov1 c4 (rv c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (op1 c4 (main1 t r)))
    (hvo2 : ∀ c4 c2 c3 c r t, rv c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t = none ∨
      ov2 c4 (rv c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (op2 c4 (main2 c t r)))
    (hvo3 : ∀ c4 c2 c3 c r t, rv c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t = none ∨
      ov3 c4 (rv c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (op3 c4 (main3 c c2 t r)))
    (sop1 : Nat → Nat → Nat → Nat → (Nat → Tup) → O) (sop2 : Nat → Nat → Nat → Nat → Nat → (Nat → Tup) → O2)
    (sop3 : Nat → Nat → Nat → Nat → Nat → (Nat → Tup) → O3)
    (hsvo1 : ∀ c4 c2 c3 c r t, ov1 c4 (sv c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (sop1 c4 c2 c3 r t))
    (hsvo2 : ∀ c4 c2 c3 c r t, ov2 c4 (sv c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (sop2 c4 c2 c3 c r t))
    (hsvo3 : ∀ c4 c2 c3 c r t, ov3 c4 (sv c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (sop3 c4 c2 c3 c r t))
    (E : Nat → Nat → Nat → Nat → Nat → Nat → Nat → Option (Pq × List Nat) × Option (P2 × P3) × TViewN PV PB → Bool) :
    let Com1 := comR K NSh NSo pos
    let Pf1 := fun c4 T1 T2 T3 T4 => pfR K NSh NSo k pos (op1 c4) g (nxtT T1 T2 T3 T4)
    let Cmi := comI K NSh NSo pos
    let Pfi := fun c4 T1 T2 T3 T4 => pfI K NSh NSo k pos (op1 c4) g (nxtT T1 T2 T3 T4)
    let smR := fun (f : Nat × Nat × Nat × (Nat → Tup) → Nat) =>
      sumTo (NSh * (NSo * K ^ n)) (fun σ1 => sumTo (NS2 * NS3) (fun σ => sumTo NR (fun r => sumN m (fun t =>
        f (σ1, σ, r, t)))))
    let smI := fun (f : Nat × Nat × Nat × (Nat → Tup) → Nat) =>
      sumTo (NSh * (NSo * K ^ n) * K) (fun σ1 => sumTo (NS2 * NS3) (fun σ => sumTo NR (fun r => sumN m (fun t =>
        f (σ1, σ, r, t)))))
    let m1 := fun (x : Nat × Nat × Nat × (Nat → Tup)) => Com1 (main1 x.2.2.2 x.2.2.1) x.1
    let m2 := fun (c1 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      m1 x + K * Com2 (main2 c1 x.2.2.2 x.2.2.1) (x.2.1 % NS2)
    let m3 := fun (c1 c2 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      m1 x + K * comPair NS2 n2 Com2 Com3 (main2 c1 x.2.2.2 x.2.2.1, main3 c1 c2 x.2.2.2 x.2.2.1) x.2.1
    let rvo := fun (T1 T2 T3 T4 c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      ((ov1 c4 (rv c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)).map (fun _ => Pf1 c4 T1 T2 T3 T4 (main1 x.2.2.2 x.2.2.1) x.1),
       (ovPair (ov2 c4) (ov3 c4) (rv c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)).map
         (fun _ => pfPair NS2 (Pf2T c4 T1 T2 T3 T4 (m3 c1 c2 x)) (Pf3T c4 T1 T2 T3 T4 (m3 c1 c2 x)) (main2 c1 x.2.2.2 x.2.2.1, main3 c1 c2 x.2.2.2 x.2.2.1) x.2.1),
       rv c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)
    let s1 := fun (c4 _c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) => Cmi (sd1 c4 (sop1 c4 c2 c3 x.2.2.1 x.2.2.2)) x.1
    let s2 := fun (c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      s1 c4 c1 c2 c3 x + K * Com2 (sd2 c4 (sop2 c4 c2 c3 c1 x.2.2.1 x.2.2.2)) (x.2.1 % NS2)
    let s3 := fun (c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      s1 c4 c1 c2 c3 x + K * comPair NS2 n2 Com2 Com3
        (sd2 c4 (sop2 c4 c2 c3 c1 x.2.2.1 x.2.2.2), sd3 c4 (sop3 c4 c2 c3 c1 x.2.2.1 x.2.2.2)) x.2.1
    let svo := fun (T1 T2 T3 T4 c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      (some (Pfi c4 T1 T2 T3 T4 (sd1 c4 (sop1 c4 c2 c3 x.2.2.1 x.2.2.2)) x.1),
       some (pfPair NS2 (Pf2T c4 T1 T2 T3 T4 (s3 c4 c1 c2 c3 x)) (Pf3T c4 T1 T2 T3 T4 (s3 c4 c1 c2 c3 x)) (sd2 c4 (sop2 c4 c2 c3 c1 x.2.2.1 x.2.2.2), sd3 c4 (sop3 c4 c2 c3 c1 x.2.2.1 x.2.2.2)) x.2.1),
       sv c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)
    let sm4 := fun (g : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup)) → Nat) =>
      sumTo ((Q4 * Q4) ^ K) (fun H1 => sumTo (K2 ^ (K * n2)) (fun H2 =>
        sumTo (K3 ^ (K * (n2 * n3))) (fun H3 => smR (fun x => g (H1, H2, H3, x)))))
    let sm4I := fun (g : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup)) → Nat) =>
      sumTo ((Q4 * Q4) ^ K) (fun H1 => sumTo (K2 ^ (K * n2)) (fun H2 =>
        sumTo (K3 ^ (K * (n2 * n3))) (fun H3 => smI (fun x => g (H1, H2, H3, x)))))
    let r1 := fun (y : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup))) => rget (Q4 * Q4) (m1 y.2.2.2) y.1
    let r2 := fun (y : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup))) => rget K2 (m2 (r1 y) y.2.2.2) y.2.1
    let r3 := fun (y : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup))) => rget K3 (m3 (r1 y) (r2 y) y.2.2.2) y.2.2.1
    let Mq := fun (y : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup))) => φ (m3 (r1 y) (r2 y) y.2.2.2)
      (oz (rv 0 (r2 y) (r3 y) (efOf (r1 y / Q4)) (efOf (r1 y % Q4)) y.2.2.2.2.2.1 y.2.2.2.2.2.2))
    K * (K4 * (Q4 * Q4 * (K2 * K3) * sumTo (K4 ^ N4) (fun H4 => sm4 (fun y =>
      indB (E y.1 y.2.1 y.2.2.1 H4 (m1 y.2.2.2) (m2 (r1 y) y.2.2.2) (m3 (r1 y) (r2 y) y.2.2.2)
        (rvo y.1 y.2.1 y.2.2.1 H4 (rget K4 (Mq y) H4) (r1 y) (r2 y) (r3 y) y.2.2.2)))))) ≤
    sumTo (K4 ^ N4) (fun H4 => sumTo K4 (fun c4 =>
      sumTo ((Q4 * Q4) ^ K) (fun H1 => sumTo (K2 ^ (K * n2)) (fun H2 => sumTo (K3 ^ (K * (n2 * n3))) (fun H3 =>
      sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo K3 (fun c3 => smI (fun x =>
        indB (E (rset (Q4 * Q4) (s1 c4 c1 c2 c3 x) H1 c1) (rset K2 (s2 c4 c1 c2 c3 x) H2 c2)
          (rset K3 (s3 c4 c1 c2 c3 x) H3 c3) (rset K4 (φ (s3 c4 c1 c2 c3 x) (oz (sv c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2))) H4 c4)
          (s1 c4 c1 c2 c3 x) (s2 c4 c1 c2 c3 x) (s3 c4 c1 c2 c3 x)
          (svo (rset (Q4 * Q4) (s1 c4 c1 c2 c3 x) H1 c1) (rset K2 (s2 c4 c1 c2 c3 x) H2 c2)
            (rset K3 (s3 c4 c1 c2 c3 x) H3 c3)
            (rset K4 (φ (s3 c4 c1 c2 c3 x) (oz (sv c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2))) H4 c4)
            c4 c1 c2 c3 x))))))))))) +
      K4 ^ N4 * (K4 * ((Q4 * Q4) ^ K * (K2 ^ (K * n2) * (K3 ^ (K * (n2 * n3)) *
        (K2 * (K3 * (NSh * (NSo * K ^ n) * K * (NS2 * NS3 * (e1 + e2)))) +
          (Q4 * (P * P) * (K2 * K3) + Q4 * Q4 * Bz) * (NSh * (NSo * K ^ n) * K * (NS2 * NS3 * (NR * (Q4 ^ m * 1)))))))) +
          B4 * (Q4 * Q4 * (K2 * K3) * sm4I (fun _ => 1))) +
      K4 * (Q4 * Q4 * (K2 * K3) * (K4 ^ N4 * ((Q4 * Q4) ^ K * (K2 ^ (K * n2) * (K3 ^ (K * (n2 * n3)) *
        (K * (NSo * (K ^ n * (s * k))) * (NS2 * NS3 * (NR * (Q4 ^ m * 1))))))))) := by
  intro Com1 Pf1 Cmi Pfi smR smI m1 m2 m3 rvo s1 s2 s3 svo sm4 sm4I r1 r2 r3 Mq
  have fo := fs_open4T (NS1 := NSh * (NSo * K ^ n) * K) (n1 := K) hK2 hK3 hK4 φ hφ rv sv gz hgz g4 hB4 hrv hsv oz hoz
    h1 h2 Cmi (fun c4 T1 T2 T3 T4 _ => Pfi c4 T1 T2 T3 T4) op1 sd1 d1 (comI_hides hK pos hpos) (fun c4 T1 T2 T3 T4 _ => pfI_hides hK pos hpos (op1 c4) g (nxtT T1 T2 T3 T4))
    (fun _ _ => Nat.mod_lt _ hK) ov1 hov1 main1 hsd1
    Com2 Pf2T op2 sd2 d2 hc2 hp2 hr2 ov2 hov2 main2 hsd2 Com3 Pf3T op3 sd3 d3 hc3 hp3 hr3 ov3 hov3 main3 hsd3
    hvo1 hvo2 hvo3 sop1 sop2 sop3 hsvo1 hsvo2 hsvo3 E
  -- the query challenge and the event, read off the first commitment's value `c`
  let c4f := fun (H1 H2 H3 H4 : Nat) (y : Nat × Nat × (Nat → Tup)) (c : Nat) =>
    let c1 := rget (Q4 * Q4) c H1
    let c2 := rget K2 (c + K * Com2 (main2 c1 y.2.2 y.2.1) (y.1 % NS2)) H2
    let mm3 := c + K * comPair NS2 n2 Com2 Com3 (main2 c1 y.2.2 y.2.1, main3 c1 c2 y.2.2 y.2.1) y.1
    let c3 := rget K3 mm3 H3
    rget K4 (φ mm3 (oz (rv 0 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) y.2.1 y.2.2))) H4
  let ev := fun (H1 H2 H3 H4 : Nat) (y : Nat × Nat × (Nat → Tup)) (c : Nat) (pf : Pq × List Nat) =>
    let c1 := rget (Q4 * Q4) c H1
    let mm2 := c + K * Com2 (main2 c1 y.2.2 y.2.1) (y.1 % NS2)
    let c2 := rget K2 mm2 H2
    let mm3 := c + K * comPair NS2 n2 Com2 Com3 (main2 c1 y.2.2 y.2.1, main3 c1 c2 y.2.2 y.2.1) y.1
    let c3 := rget K3 mm3 H3
    let c4 := c4f H1 H2 H3 H4 y c
    E H1 H2 H3 H4 c mm2 mm3
      ((ov1 c4 (rv c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) y.2.1 y.2.2)).map (fun _ => pf),
       (ovPair (ov2 c4) (ov3 c4) (rv c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) y.2.1 y.2.2)).map
         (fun _ => pfPair NS2 (Pf2T c4 H1 H2 H3 H4 mm3) (Pf3T c4 H1 H2 H3 H4 mm3) (main2 c1 y.2.2 y.2.1, main3 c1 c2 y.2.2 y.2.1) y.1),
       rv c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) y.2.1 y.2.2)
  have hso := smT_lin (NS2 * NS3) NR m
  have so1 := smT_one (NS2 * NS3) NR m
  have step : ∀ H4 H1 H2 H3,
      K * smR (fun x => indB (ev H1 H2 H3 H4 x.2 (Com1 (main1 x.2.2.2 x.2.2.1) x.1)
        (Pf1 (c4f H1 H2 H3 H4 x.2 (Com1 (main1 x.2.2.2 x.2.2.1) x.1)) H1 H2 H3 H4 (main1 x.2.2.2 x.2.2.1) x.1))) ≤
      smI (fun x => indB (ev H1 H2 H3 H4 x.2 (Cmi (main1 x.2.2.2 x.2.2.1) x.1)
        (Pfi (c4f H1 H2 H3 H4 x.2 (Cmi (main1 x.2.2.2 x.2.2.1) x.1)) H1 H2 H3 H4 (main1 x.2.2.2 x.2.2.1) x.1))) +
        K * (NSo * (K ^ n * (s * k))) * (NS2 * NS3 * (NR * (Q4 ^ m * 1))) := fun H4 H1 H2 H3 => by
    have tr := transferRc_in (n := n) (NSh := NSh) (NSo := NSo) (s := s) (k := k) hK (smT (NS2 * NS3) NR m) hso
      pos hpos op1 g hs (nxtT H1 H2 H3 H4) (fun y => main1 y.2.2 y.2.1) (fun y c => c4f H1 H2 H3 H4 y c)
      (fun y c pf => ev H1 H2 H3 H4 y c pf)
    rw [hso, hso, so1] at tr
    exact tr
  have hb : ∀ X : Nat → Nat → Nat → Nat → Nat, K * (K4 * (Q4 * Q4 * (K2 * K3) * sumTo (K4 ^ N4) (fun H4 =>
      sumTo ((Q4 * Q4) ^ K) (fun H1 => sumTo (K2 ^ (K * n2)) (fun H2 =>
        sumTo (K3 ^ (K * (n2 * n3))) (fun H3 => X H4 H1 H2 H3)))))) =
      K4 * (Q4 * Q4 * (K2 * K3) * sumTo (K4 ^ N4) (fun H4 =>
      sumTo ((Q4 * Q4) ^ K) (fun H1 => sumTo (K2 ^ (K * n2)) (fun H2 =>
        sumTo (K3 ^ (K * (n2 * n3))) (fun H3 => K * X H4 H1 H2 H3))))) := fun X => by
    rw [Nat.mul_left_comm K K4, Nat.mul_left_comm K (Q4 * Q4 * (K2 * K3)), sumTo_mul]
    exact congrArg (fun z => K4 * (Q4 * Q4 * (K2 * K3) * z)) (sumTo_congr _ (fun H4 _ =>
      (sumTo_mul _ _ _).trans (sumTo_congr _ (fun H1 _ =>
        (sumTo_mul _ _ _).trans (sumTo_congr _ (fun H2 _ => sumTo_mul _ _ _))))))
  rw [hb]
  refine Nat.le_trans (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _
    (sumTo_mono _ (fun H4 _ => sumTo_mono _ (fun H1 _ => sumTo_mono _ (fun H2 _ =>
      sumTo_mono _ (fun H3 _ => step H4 H1 H2 H3))))))) ?_
  simp only [sumTo_add, sumTo_const]
  rw [Nat.mul_add (Q4 * Q4 * (K2 * K3)), Nat.mul_add K4]
  exact Nat.add_le_add_right fo _

end Circuit
