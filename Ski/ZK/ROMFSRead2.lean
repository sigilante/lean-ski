import Ski.ZK.ROMFSRead

/-!
# Two and three Fiat–Shamir rounds, the openings reading the tables

`ROMFSRead` lets one round's opening read the Fiat–Shamir table.  Here
every opening reads every table.  After the reprogrammings
(`fs_zk2T`, `fs_zk3T`) each opening reads the tables set at the
messages, so its table choice is a function of the commitments' values.
Swapping the commitments one at a time (`open_two_coreT`) fixes the other
commitment's value, so each opening is chosen by its own commitment's
value (`comPf_choose`), with the other's value as an index.  So two rounds
(`fs_open2T`) and three (`fs_open3T`, the second and third commitments as
a pair) hold with hiding given at every choice of tables.  Over the
oracle's commitment the transfer runs at each choice of tables, the
distinguisher's queries `nxtT` chosen from them (`fs_open2ROMT`,
`fs_open3ROMT`).  The queries read the tables, the first commitment's
value and its opened data, so the first challenge too; they do not read
the later commitments, their openings or challenges, or the transcript.
One direction; `ROMHide`'s other limits hold.  `ROMFSRead4` opens four
rounds.
-/

set_option autoImplicit false
namespace Circuit
open ZKF


/-- `open_real2` with the opening indexed by the draw. -/
theorem open_real2T {PV PB D O Pp : Type} {NS NR m : Nat} (Com : D → Nat → Nat) (Pf : Nat → (Nat → Tup) → D → Nat → Pp)
    (op : D → O) (sd : O → D) (d0 : D) (hcom : ComHides NS Com) (hpf : ∀ r t, ComPfHides NS Com (Pf r t) op)
    (ov : TViewN PV PB → Option O) (hovn : ov none = none) (main : (Nat → Tup) → Nat → D)
    (hsd : ∀ t r, op (sd (op (main t r))) = op (main t r))
    (v : Nat → (Nat → Tup) → TViewN PV PB) (hvo : ∀ r t, v r t = none ∨ ov (v r t) = some (op (main t r)))
    (F : Nat → (Nat → Tup) → Nat → Option Pp → TViewN PV PB → Bool) :
    sumTo NS (fun σ => sumTo NR (fun r => sumN m (fun t =>
      indB (F r t (Com (main t r) σ) ((ov (v r t)).map (fun _ => Pf r t (main t r) σ)) (v r t))))) =
    sumTo NS (fun σ => sumTo NR (fun r => sumN m (fun t => indB (openEv Com (Pf r t) sd d0 ov (F r t) σ (v r t))))) := by
  have key : ∀ r t, sumTo NS (fun σ => indB (F r t (Com (main t r) σ) ((ov (v r t)).map (fun _ => Pf r t (main t r) σ))
      (v r t))) = sumTo NS (fun σ => indB (openEv Com (Pf r t) sd d0 ov (F r t) σ (v r t))) := by
    intro r t
    rcases hvo r t with e | e
    · rw [e]
      unfold openEv
      rw [hovn]
      exact hcom (main t r) d0 (fun mm => F r t mm none none)
    · unfold openEv
      rw [e]
      exact hpf r t (main t r) (sd (op (main t r))) (hsd t r).symm (fun mm p => F r t mm (some p) (v r t))
  rw [sig_in, sig_in]
  exact sumTo_congr _ (fun r _ => Nat.le_antisymm (sumN_mono m (fun t => Nat.le_of_eq (key r t)))
    (sumN_mono m (fun t => Nat.le_of_eq (key r t).symm)))

/-- The commitment value the view's opening fixes, or fixed data's. -/
def openC {PV PB D O : Type} (Com : D → Nat → Nat) (sd : O → D) (d0 : D) (ov : TViewN PV PB → Option O) (σ : Nat)
    (v : TViewN PV PB) : Nat :=
  match ov v with
  | some o => Com (sd o) σ
  | none => Com d0 σ

/-- The view event two salts give, each opening read at the other
    commitment's value. -/
def openEv2T {PV PB D1 O1 P1 D2 O2 P2 : Type} (Com1 : D1 → Nat → Nat) (Pf1 : Nat → D1 → Nat → P1) (sd1 : O1 → D1)
    (d1 : D1) (ov1 : TViewN PV PB → Option O1) (Com2 : D2 → Nat → Nat) (Pf2 : Nat → D2 → Nat → P2) (sd2 : O2 → D2)
    (d2 : D2) (ov2 : TViewN PV PB → Option O2)
    (F : Nat → Nat → Option P1 → Option P2 → TViewN PV PB → Bool) (σ1 σ2 : Nat) (v : TViewN PV PB) : Bool :=
  openEv Com1 (Pf1 (openC Com2 sd2 d2 ov2 σ2 v)) sd1 d1 ov1
    (fun mm1 p1 w => F mm1 (openC Com2 sd2 d2 ov2 σ2 w) p1 ((ov2 w).map (fun o => Pf2 mm1 (sd2 o) σ2)) w) σ1 v

theorem openEv2T_and {PV PB D1 O1 P1 D2 O2 P2 : Type} (Com1 : D1 → Nat → Nat) (Pf1 : Nat → D1 → Nat → P1)
    (sd1 : O1 → D1) (d1 : D1) (ov1 : TViewN PV PB → Option O1) (Com2 : D2 → Nat → Nat) (Pf2 : Nat → D2 → Nat → P2)
    (sd2 : O2 → D2) (d2 : D2) (ov2 : TViewN PV PB → Option O2) (b : Bool)
    (F : Nat → Nat → Option P1 → Option P2 → TViewN PV PB → Bool) (σ1 σ2 : Nat) (v : TViewN PV PB) :
    openEv2T Com1 Pf1 sd1 d1 ov1 Com2 Pf2 sd2 d2 ov2 (fun a b' p q w => b && F a b' p q w) σ1 σ2 v =
      (b && openEv2T Com1 Pf1 sd1 d1 ov1 Com2 Pf2 sd2 d2 ov2 F σ1 σ2 v) := by
  unfold openEv2T; rw [openEv_and]

theorem openEv2T_some {PV PB D1 O1 P1 D2 O2 P2 : Type} (Com1 : D1 → Nat → Nat) (Pf1 : Nat → D1 → Nat → P1)
    (sd1 : O1 → D1) (d1 : D1) (ov1 : TViewN PV PB → Option O1) (Com2 : D2 → Nat → Nat) (Pf2 : Nat → D2 → Nat → P2)
    (sd2 : O2 → D2) (d2 : D2) (ov2 : TViewN PV PB → Option O2)
    (F : Nat → Nat → Option P1 → Option P2 → TViewN PV PB → Bool) (σ1 σ2 : Nat) (v : TViewN PV PB) (o1 : O1)
    (o2 : O2) (h1 : ov1 v = some o1) (h2 : ov2 v = some o2) :
    openEv2T Com1 Pf1 sd1 d1 ov1 Com2 Pf2 sd2 d2 ov2 F σ1 σ2 v =
      F (Com1 (sd1 o1) σ1) (Com2 (sd2 o2) σ2) (some (Pf1 (Com2 (sd2 o2) σ2) (sd1 o1) σ1))
        (some (Pf2 (Com1 (sd1 o1) σ1) (sd2 o2) σ2)) v := by
  unfold openEv2T openEv openC; rw [h1]; dsimp only; rw [h2]; rfl
/-- **Two opened commitments beside a transcript, each opening read at
    the other commitment's value** (`open_two_core` with `Pf1 c mm2`,
    `Pf2 c mm1`): hiding given at every value read. -/
theorem open_two_coreT {PV PB D1 O1 P1 D2 O2 P2 : Type} {NR m e1 e2 NS1 NS2 : Nat}
    (rv sv : EF → EF → Nat → (Nat → Tup) → TViewN PV PB)
    (hrv : ∀ α β r t, rv α β r t = none ∨ ∃ p x y, rv α β r t = some (p, α, β, x, y))
    (hsv : ∀ α β r t, ∃ p x y, sv α β r t = some (p, α, β, x, y))
    (h1 : ∀ E : TViewN PV PB → Bool, tsumN NR m (fun α β r t => indB (genB β && E (rv α β r t))) ≤
      tsumN NR m (fun α β r t => indB (genB β && E (sv α β r t))) + e1 + e2)
    (h2 : ∀ E : TViewN PV PB → Bool, tsumN NR m (fun α β r t => indB (genB β && E (sv α β r t))) ≤
      tsumN NR m (fun α β r t => indB (genB β && E (rv α β r t))) + e1 + e2)
    (Com1 : D1 → Nat → Nat) (Pf1 : Nat → Nat → D1 → Nat → P1) (op1 : D1 → O1) (sd1 : O1 → D1) (d1 : D1)
    (hc1 : ComHides NS1 Com1) (hp1 : ∀ c v, ComPfHides NS1 Com1 (Pf1 c v) op1) (ov1 : TViewN PV PB → Option O1)
    (hov1 : ov1 none = none) (main1 : (Nat → Tup) → Nat → D1)
    (hsd1 : ∀ t r, op1 (sd1 (op1 (main1 t r))) = op1 (main1 t r))
    (Com2 : D2 → Nat → Nat) (Pf2 : Nat → Nat → D2 → Nat → P2) (op2 : D2 → O2) (sd2 : O2 → D2) (d2 : D2)
    (hc2 : ComHides NS2 Com2) (hp2 : ∀ c v, ComPfHides NS2 Com2 (Pf2 c v) op2) (ov2 : TViewN PV PB → Option O2)
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
          (fun _ => Pf1 c (Com2 (main2 c t r) σ2) (main1 t r) σ1))
        ((ov2 (rv (efOf (c / Q4)) (efOf (c % Q4)) r t)).map
          (fun _ => Pf2 c (Com1 (main1 t r) σ1) (main2 c t r) σ2))
        (rv (efOf (c / Q4)) (efOf (c % Q4)) r t))))))) ≤
    sumTo (Q4 * Q4) (fun c => sumTo NS1 (fun σ1 => sumTo NS2 (fun σ2 => sumTo NR (fun r => sumN m (fun t =>
      indB (genB (efOf (c % Q4)) && F c (Com1 (sd1 (sop1 r t)) σ1) (Com2 (sd2 (sop2 c r t)) σ2)
        (some (Pf1 c (Com2 (sd2 (sop2 c r t)) σ2) (sd1 (sop1 r t)) σ1))
        (some (Pf2 c (Com1 (sd1 (sop1 r t)) σ1) (sd2 (sop2 c r t)) σ2))
        (sv (efOf (c / Q4)) (efOf (c % Q4)) r t))))))) + NS1 * (NS2 * (e1 + e2)) := by
  have h1' := fun E => Nat.le_trans (h1 E) (Nat.le_of_eq (Nat.add_assoc _ e1 e2))
  have h2' := fun E => Nat.le_trans (h2 E) (Nat.le_of_eq (Nat.add_assoc _ e1 e2))
  let G : Nat → Nat → Nat → TViewN PV PB → Bool := fun σ1 σ2 c w =>
    openEv2T Com1 (Pf1 c) sd1 d1 ov1 Com2 (Pf2 c) sd2 d2 ov2 (F c) σ1 σ2 w
  have hreal : ∀ c, sumTo NS1 (fun σ1 => sumTo NS2 (fun σ2 => sumTo NR (fun r => sumN m (fun t =>
      indB (genB (efOf (c % Q4)) && F c (Com1 (main1 t r) σ1) (Com2 (main2 c t r) σ2)
        ((ov1 (rv (efOf (c / Q4)) (efOf (c % Q4)) r t)).map
          (fun _ => Pf1 c (Com2 (main2 c t r) σ2) (main1 t r) σ1))
        ((ov2 (rv (efOf (c / Q4)) (efOf (c % Q4)) r t)).map
          (fun _ => Pf2 c (Com1 (main1 t r) σ1) (main2 c t r) σ2))
        (rv (efOf (c / Q4)) (efOf (c % Q4)) r t)))))) =
      sumTo NS2 (fun σ2 => sumTo NS1 (fun σ1 => sumTo NR (fun r => sumN m (fun t =>
        indB (genB (efOf (c % Q4)) && G σ1 σ2 c (rv (efOf (c / Q4)) (efOf (c % Q4)) r t)))))) := fun c => by
    -- the second commitment swapped, the first's value fixed by its salt
    rw [sumTo_congr _ (fun σ1 _ => open_real2T (NR := NR) (m := m) Com2
      (fun r t => Pf2 c (Com1 (main1 t r) σ1)) op2 sd2 d2 hc2 (fun r t => hp2 c _) ov2 hov2 (main2 c) (hsd2 c)
      (fun r t => rv (efOf (c / Q4)) (efOf (c % Q4)) r t) (fun r t => hvo2 c r t)
      (fun r t mm2 p2 w => genB (efOf (c % Q4)) && F c (Com1 (main1 t r) σ1) mm2
        ((ov1 w).map (fun _ => Pf1 c mm2 (main1 t r) σ1)) p2 w))]
    rw [sumTo_exch _ NS2 NS1]
    refine sumTo_congr _ (fun σ2 _ => ?_)
    -- then the first, the second's value read off the view
    have e := open_real2T (NR := NR) (m := m) Com1
      (fun r t => Pf1 c (openC Com2 sd2 d2 ov2 σ2 (rv (efOf (c / Q4)) (efOf (c % Q4)) r t))) op1 sd1 d1 hc1
      (fun r t => hp1 c _) ov1 hov1 main1 hsd1
      (fun r t => rv (efOf (c / Q4)) (efOf (c % Q4)) r t) (fun r t => hvo1 c r t)
      (fun _ _ mm1 p1 w => genB (efOf (c % Q4)) && F c mm1 (openC Com2 sd2 d2 ov2 σ2 w) p1
        ((ov2 w).map (fun o => Pf2 c mm1 (sd2 o) σ2)) w)
    refine Eq.trans ?_ (e.trans ?_)
    · refine sumTo_congr _ (fun σ1 _ => sumTo_congr _ (fun r _ => Nat.le_antisymm
        (sumN_mono m (fun t => Nat.le_of_eq ?_)) (sumN_mono m (fun t => Nat.le_of_eq ?_))))
      all_goals (unfold openEv openC; cases ov2 (rv (efOf (c / Q4)) (efOf (c % Q4)) r t) <;> rfl)
    · have eq : ∀ σ1 r t, indB (openEv Com1
            (Pf1 c (openC Com2 sd2 d2 ov2 σ2 (rv (efOf (c / Q4)) (efOf (c % Q4)) r t))) sd1 d1 ov1
            (fun mm1 p1 w => genB (efOf (c % Q4)) && F c mm1 (openC Com2 sd2 d2 ov2 σ2 w) p1
              ((ov2 w).map (fun o => Pf2 c mm1 (sd2 o) σ2)) w)
            σ1 (rv (efOf (c / Q4)) (efOf (c % Q4)) r t)) =
          indB (genB (efOf (c % Q4)) && G σ1 σ2 c (rv (efOf (c / Q4)) (efOf (c % Q4)) r t)) := fun σ1 r t => by
        show indB (openEv2T Com1 (Pf1 c) sd1 d1 ov1 Com2 (Pf2 c) sd2 d2 ov2
          (fun a b' p q w => genB (efOf (c % Q4)) && F c a b' p q w) σ1 σ2 _) = _
        rw [openEv2T_and]
      refine sumTo_congr _ (fun σ1 _ => sumTo_congr _ (fun r _ => Nat.le_antisymm
        (sumN_mono m (fun t => Nat.le_of_eq (eq σ1 r t))) (sumN_mono m (fun t => Nat.le_of_eq (eq σ1 r t).symm))))
  have hsim : ∀ c, sumTo NS1 (fun σ1 => sumTo NS2 (fun σ2 => sumTo NR (fun r => sumN m (fun t =>
      indB (genB (efOf (c % Q4)) && F c (Com1 (sd1 (sop1 r t)) σ1) (Com2 (sd2 (sop2 c r t)) σ2)
        (some (Pf1 c (Com2 (sd2 (sop2 c r t)) σ2) (sd1 (sop1 r t)) σ1))
        (some (Pf2 c (Com1 (sd1 (sop1 r t)) σ1) (sd2 (sop2 c r t)) σ2))
        (sv (efOf (c / Q4)) (efOf (c % Q4)) r t)))))) =
      sumTo NS2 (fun σ2 => sumTo NS1 (fun σ1 => sumTo NR (fun r => sumN m (fun t =>
        indB (genB (efOf (c % Q4)) && G σ1 σ2 c (sv (efOf (c / Q4)) (efOf (c % Q4)) r t)))))) := fun c => by
    rw [sumTo_exch _ NS2 NS1]
    refine sumTo_congr _ (fun σ2 _ => sumTo_congr _ (fun σ1 _ => sumTo_congr _ (fun r _ => Nat.le_antisymm
      (sumN_mono m (fun t => Nat.le_of_eq ?_)) (sumN_mono m (fun t => Nat.le_of_eq ?_)))))
    · show _ = indB (genB (efOf (c % Q4)) && openEv2T Com1 (Pf1 c) sd1 d1 ov1 Com2 (Pf2 c) sd2 d2 ov2 (F c) σ1 σ2 _)
      rw [openEv2T_some _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (hsvo1 c r t) (hsvo2 c r t)]
    · show indB (genB (efOf (c % Q4)) && openEv2T Com1 (Pf1 c) sd1 d1 ov1 Com2 (Pf2 c) sd2 d2 ov2 (F c) σ1 σ2 _) = _
      rw [openEv2T_some _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (hsvo1 c r t) (hsvo2 c r t)]
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
/-- **Fiat–Shamir over two rounds, both commitments opened, the openings
    reading both oracle tables** (`fs_open2` over `fs_zk2T`): the openings
    `Pf1T H1 H2`, `Pf2T H1 H2` may read the tables (the distinguisher's
    queries chosen from them); hiding given at every pair of tables.  After
    both reprogrammings each opening reads the tables set at the two
    messages, a choice by the commitments' values (`comPf_choose`), each
    read at the other's value (`open_two_coreT`).  One direction. -/
theorem fs_open2T {PV PB D1 O1 P1 D2 O2 P2 : Type} {NR m e1 e2 NS1 NS2 K2 n1 n2 : Nat} (hK2 : 0 < K2)
    (rv sv : Nat → EF → EF → Nat → (Nat → Tup) → TViewN PV PB) (gz : Nat → Bool)
    (hrv : ∀ c2 α β r t, rv c2 α β r t = none ∨ ∃ p x y, rv c2 α β r t = some (p, α, β, x, y))
    (hsv : ∀ c2 α β r t, ∃ p x y, sv c2 α β r t = some (p, α, β, x, y))
    (h1 : ∀ c2, gz c2 = true → ∀ E : TViewN PV PB → Bool,
      tsumN NR m (fun α β r t => indB (genB β && E (rv c2 α β r t))) ≤
        tsumN NR m (fun α β r t => indB (genB β && E (sv c2 α β r t))) + e1 + e2)
    (h2 : ∀ c2, gz c2 = true → ∀ E : TViewN PV PB → Bool,
      tsumN NR m (fun α β r t => indB (genB β && E (sv c2 α β r t))) ≤
        tsumN NR m (fun α β r t => indB (genB β && E (rv c2 α β r t))) + e1 + e2)
    (Com1 : D1 → Nat → Nat) (Pf1T : Nat → Nat → D1 → Nat → P1) (op1 : D1 → O1) (sd1 : O1 → D1) (d1 : D1)
    (hc1 : ComHides NS1 Com1) (hp1 : ∀ T1 T2, ComPfHides NS1 Com1 (Pf1T T1 T2) op1) (hr1 : ∀ d σ, Com1 d σ < n1)
    (ov1 : TViewN PV PB → Option O1) (hov1 : ov1 none = none) (main1 : (Nat → Tup) → Nat → D1)
    (hsd1 : ∀ t r, op1 (sd1 (op1 (main1 t r))) = op1 (main1 t r))
    (Com2 : D2 → Nat → Nat) (Pf2T : Nat → Nat → D2 → Nat → P2) (op2 : D2 → O2) (sd2 : O2 → D2) (d2 : D2)
    (hc2 : ComHides NS2 Com2) (hp2 : ∀ T1 T2, ComPfHides NS2 Com2 (Pf2T T1 T2) op2) (hr2 : ∀ d σ, Com2 d σ < n2)
    (ov2 : TViewN PV PB → Option O2) (hov2 : ov2 none = none) (main2 : Nat → (Nat → Tup) → Nat → D2)
    (hsd2 : ∀ c t r, op2 (sd2 (op2 (main2 c t r))) = op2 (main2 c t r))
    (hvo1 : ∀ c2 c r t, rv c2 (efOf (c / Q4)) (efOf (c % Q4)) r t = none ∨
      ov1 (rv c2 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (op1 (main1 t r)))
    (hvo2 : ∀ c2 c r t, rv c2 (efOf (c / Q4)) (efOf (c % Q4)) r t = none ∨
      ov2 (rv c2 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (op2 (main2 c t r)))
    (sop1 : Nat → Nat → (Nat → Tup) → O1) (sop2 : Nat → Nat → Nat → (Nat → Tup) → O2)
    (hsvo1 : ∀ c2 c r t, ov1 (sv c2 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (sop1 c2 r t))
    (hsvo2 : ∀ c2 c r t, ov2 (sv c2 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (sop2 c2 c r t))
    (E : Nat → Nat → Nat → Nat → Option P1 × Option P2 × TViewN PV PB → Bool) :
    let sm := fun (g : Nat × Nat × Nat × (Nat → Tup) → Nat) =>
      sumTo NS1 (fun σ1 => sumTo NS2 (fun σ2 => sumTo NR (fun r => sumN m (fun t => g (σ1, σ2, r, t)))))
    let m1 := fun (x : Nat × Nat × Nat × (Nat → Tup)) => Com1 (main1 x.2.2.2 x.2.2.1) x.1
    let m2 := fun (c1 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      Com1 (main1 x.2.2.2 x.2.2.1) x.1 + n1 * Com2 (main2 c1 x.2.2.2 x.2.2.1) x.2.1
    let rvo := fun (T1 T2 c1 c2 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      ((ov1 (rv c2 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)).map
         (fun _ => Pf1T T1 T2 (main1 x.2.2.2 x.2.2.1) x.1),
       (ov2 (rv c2 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)).map
         (fun _ => Pf2T T1 T2 (main2 c1 x.2.2.2 x.2.2.1) x.2.1),
       rv c2 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)
    let s1 := fun (_ c2 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) => Com1 (sd1 (sop1 c2 x.2.2.1 x.2.2.2)) x.1
    let s2 := fun (c1 c2 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      s1 c1 c2 x + n1 * Com2 (sd2 (sop2 c2 c1 x.2.2.1 x.2.2.2)) x.2.1
    let svo := fun (T1 T2 c1 c2 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      (some (Pf1T T1 T2 (sd1 (sop1 c2 x.2.2.1 x.2.2.2)) x.1),
        some (Pf2T T1 T2 (sd2 (sop2 c2 c1 x.2.2.1 x.2.2.2)) x.2.1),
        sv c2 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)
    let gd := fun (c1 c2 : Nat) => genB (efOf (c1 % Q4)) && gz c2
    (Q4 * Q4) * (K2 * sumTo ((Q4 * Q4) ^ n1) (fun H1 => sumTo (K2 ^ (n1 * n2)) (fun H2 => sm (fun x =>
      indB (gd (rget (Q4 * Q4) (m1 x) H1) (rget K2 (m2 (rget (Q4 * Q4) (m1 x) H1) x) H2) &&
        E H1 H2 (m1 x) (m2 (rget (Q4 * Q4) (m1 x) H1) x)
          (rvo H1 H2 (rget (Q4 * Q4) (m1 x) H1) (rget K2 (m2 (rget (Q4 * Q4) (m1 x) H1) x) H2) x)))))) ≤
    sumTo ((Q4 * Q4) ^ n1) (fun H1 => sumTo (K2 ^ (n1 * n2)) (fun H2 => sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 =>
      sm (fun x => indB (gd c1 c2 && E (rset (Q4 * Q4) (s1 c1 c2 x) H1 c1) (rset K2 (s2 c1 c2 x) H2 c2)
        (s1 c1 c2 x) (s2 c1 c2 x)
        (svo (rset (Q4 * Q4) (s1 c1 c2 x) H1 c1) (rset K2 (s2 c1 c2 x) H2 c2) c1 c2 x))))))) +
      (Q4 * Q4) ^ n1 * (K2 ^ (n1 * n2) * (K2 * (NS1 * (NS2 * (e1 + e2))))) := by
  intro sm m1 m2 rvo s1 s2 svo gd
  have hsm : ∀ (N : Nat) (f : Nat → Nat × Nat × Nat × (Nat → Tup) → Nat),
      sm (fun x => sumTo N (fun i => f i x)) = sumTo N (fun i => sm (f i)) := fun N f => by
    show sumTo NS1 (fun σ1 => sumTo NS2 (fun σ2 => sumTo NR (fun r => sumN m (fun t =>
      sumTo N (fun i => f i (σ1, σ2, r, t)))))) = _
    rw [sumTo_congr _ (fun σ1 _ => sm_exch (NS := NS2) (NR := NR) (m := m) (N := N)
      (fun i σ2 r t => f i (σ1, σ2, r, t)))]
    exact sumTo_exch _ N NS1
  refine fs_zk2T (K1 := Q4 * Q4) (K2 := K2) (n1 := n1) (n2 := n1 * n2) (Nat.mul_pos Q4_pos Q4_pos) hK2 sm hsm m1 m2
    (fun x => hr1 _ _) (fun _ x => pair_lt (hr1 _ _) (hr2 _ _)) s1 s2 rvo svo gd (fun H1 H2 F => ?_) E
  show sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo NS1 (fun σ1 => sumTo NS2 (fun σ2 => sumTo NR (fun r =>
    sumN m (fun t => _)))))) ≤ _
  rw [sumTo_exch _ K2 (Q4 * Q4), sumTo_exch _ K2 (Q4 * Q4), ← sumTo_const (NS1 * (NS2 * (e1 + e2))) K2, ← sumTo_add]
  refine sumTo_mono _ (fun c2 _ => ?_)
  cases hg : gz c2
  · simp only [gd, hg, Bool.and_false, Bool.false_and]
    exact Nat.le_add_right _ _
  · simp only [gd, hg, Bool.and_true]
    exact open_two_coreT (rv c2) (sv c2) (hrv c2) (hsv c2) (h1 c2 hg) (h2 c2 hg)
      Com1 (fun c v d σ => Pf1T (rset (Q4 * Q4) (Com1 d σ) H1 c) (rset K2 (Com1 d σ + n1 * v) H2 c2) d σ)
      op1 sd1 d1 hc1
      (fun c v => comPf_choose (Pf := fun T d σ => Pf1T (rset (Q4 * Q4) T H1 c) (rset K2 (T + n1 * v) H2 c2) d σ)
        (fun T => hp1 _ _) hr1 id)
      ov1 hov1 main1 hsd1
      Com2 (fun c v d σ => Pf2T (rset (Q4 * Q4) v H1 c) (rset K2 (v + n1 * Com2 d σ) H2 c2) d σ)
      op2 sd2 d2 hc2
      (fun c v => comPf_choose (Pf := fun T d σ => Pf2T (rset (Q4 * Q4) v H1 c) (rset K2 (v + n1 * T) H2 c2) d σ)
        (fun T => hp2 _ _) hr2 id)
      ov2 hov2 main2 hsd2 (hvo1 c2) (hvo2 c2) (sop1 c2) (sop2 c2) (hsvo1 c2) (hsvo2 c2)
      (fun c1 a b p q w => F c1 c2 a (a + n1 * b) (p, q, w))
/-- **Two Fiat–Shamir rounds, the first commitment drawn from the oracle,
    the distinguisher's queries and the second opening reading both
    Fiat–Shamir tables** (`nxtT H1 H2`, `Pf2T H1 H2`): `fs_open2ROM` with
    the transfer at each pair of tables and `fs_open2T` at the ideal
    opening, whose queries read the tables the simulator programs.  One
    direction; the queries read the tables, the first commitment's value and
    its opened data, not the later commitments, their openings or the
    transcript. -/
theorem fs_open2ROMT {PV PB D O P D2 O2 P2 : Type} {K NR m e1 e2 NSh NSo s k n NS2 K2 n2 : Nat}
    (hK : 0 < K) (hK2 : 0 < K2)
    (rv sv : Nat → EF → EF → Nat → (Nat → Tup) → TViewN PV PB) (gz : Nat → Bool)
    (hrv : ∀ c2 α β r t, rv c2 α β r t = none ∨ ∃ p x y, rv c2 α β r t = some (p, α, β, x, y))
    (hsv : ∀ c2 α β r t, ∃ p x y, sv c2 α β r t = some (p, α, β, x, y))
    (h1 : ∀ c2, gz c2 = true → ∀ E : TViewN PV PB → Bool,
      tsumN NR m (fun α β r t => indB (genB β && E (rv c2 α β r t))) ≤
        tsumN NR m (fun α β r t => indB (genB β && E (sv c2 α β r t))) + e1 + e2)
    (h2 : ∀ c2, gz c2 = true → ∀ E : TViewN PV PB → Bool,
      tsumN NR m (fun α β r t => indB (genB β && E (sv c2 α β r t))) ≤
        tsumN NR m (fun α β r t => indB (genB β && E (rv c2 α β r t))) + e1 + e2)
    (pos : D → Nat → Nat → Nat) (hpos : ∀ d σo σh, pos d σo σh < n) (g : O → Nat → P)
    (hs : ∀ d σo v, sumTo NSh (fun σh => indB (decide (pos d σo σh = v))) ≤ s)
    (nxtT : Nat → Nat → P → Nat → List Nat → Nat) (op1 : D → O) (sd1 : O → D) (d1 : D)
    (ov1 : TViewN PV PB → Option O) (hov1 : ov1 none = none) (main1 : (Nat → Tup) → Nat → D)
    (hsd1 : ∀ t r, op1 (sd1 (op1 (main1 t r))) = op1 (main1 t r))
    (Com2 : D2 → Nat → Nat) (Pf2T : Nat → Nat → D2 → Nat → P2) (op2 : D2 → O2) (sd2 : O2 → D2) (d2 : D2)
    (hc2 : ComHides NS2 Com2) (hp2 : ∀ T1 T2, ComPfHides NS2 Com2 (Pf2T T1 T2) op2) (hr2 : ∀ d σ, Com2 d σ < n2)
    (ov2 : TViewN PV PB → Option O2) (hov2 : ov2 none = none) (main2 : Nat → (Nat → Tup) → Nat → D2)
    (hsd2 : ∀ c t r, op2 (sd2 (op2 (main2 c t r))) = op2 (main2 c t r))
    (hvo1 : ∀ c2 c r t, rv c2 (efOf (c / Q4)) (efOf (c % Q4)) r t = none ∨
      ov1 (rv c2 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (op1 (main1 t r)))
    (hvo2 : ∀ c2 c r t, rv c2 (efOf (c / Q4)) (efOf (c % Q4)) r t = none ∨
      ov2 (rv c2 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (op2 (main2 c t r)))
    (sop1 : Nat → Nat → (Nat → Tup) → O) (sop2 : Nat → Nat → Nat → (Nat → Tup) → O2)
    (hsvo1 : ∀ c2 c r t, ov1 (sv c2 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (sop1 c2 r t))
    (hsvo2 : ∀ c2 c r t, ov2 (sv c2 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (sop2 c2 c r t))
    (E : Nat → Nat → Nat → Nat → Option (P × List Nat) × Option P2 × TViewN PV PB → Bool) :
    let Com1 := comR K NSh NSo pos
    let Pf1 := fun T1 T2 => pfR K NSh NSo k pos op1 g (nxtT T1 T2)
    let Cmi := comI K NSh NSo pos
    let Pfi := fun T1 T2 => pfI K NSh NSo k pos op1 g (nxtT T1 T2)
    let smR := fun (f : Nat × Nat × Nat × (Nat → Tup) → Nat) =>
      sumTo (NSh * (NSo * K ^ n)) (fun σ1 => sumTo NS2 (fun σ2 => sumTo NR (fun r => sumN m (fun t => f (σ1, σ2, r, t)))))
    let smI := fun (f : Nat × Nat × Nat × (Nat → Tup) → Nat) =>
      sumTo (NSh * (NSo * K ^ n) * K) (fun σ1 => sumTo NS2 (fun σ2 => sumTo NR (fun r => sumN m (fun t =>
        f (σ1, σ2, r, t)))))
    let m1 := fun (x : Nat × Nat × Nat × (Nat → Tup)) => Com1 (main1 x.2.2.2 x.2.2.1) x.1
    let m2 := fun (c1 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      Com1 (main1 x.2.2.2 x.2.2.1) x.1 + K * Com2 (main2 c1 x.2.2.2 x.2.2.1) x.2.1
    let rvo := fun (T1 T2 c1 c2 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      ((ov1 (rv c2 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)).map (fun _ => Pf1 T1 T2 (main1 x.2.2.2 x.2.2.1) x.1),
       (ov2 (rv c2 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)).map
         (fun _ => Pf2T T1 T2 (main2 c1 x.2.2.2 x.2.2.1) x.2.1),
       rv c2 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)
    let s1 := fun (_c1 c2 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) => Cmi (sd1 (sop1 c2 x.2.2.1 x.2.2.2)) x.1
    let s2 := fun (c1 c2 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      s1 c1 c2 x + K * Com2 (sd2 (sop2 c2 c1 x.2.2.1 x.2.2.2)) x.2.1
    let svo := fun (T1 T2 c1 c2 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      (some (Pfi T1 T2 (sd1 (sop1 c2 x.2.2.1 x.2.2.2)) x.1), some (Pf2T T1 T2 (sd2 (sop2 c2 c1 x.2.2.1 x.2.2.2)) x.2.1),
        sv c2 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)
    let gd := fun (c1 c2 : Nat) => genB (efOf (c1 % Q4)) && gz c2
    K * ((Q4 * Q4) * (K2 * sumTo ((Q4 * Q4) ^ K) (fun H1 => sumTo (K2 ^ (K * n2)) (fun H2 => smR (fun x =>
      indB (gd (rget (Q4 * Q4) (m1 x) H1) (rget K2 (m2 (rget (Q4 * Q4) (m1 x) H1) x) H2) &&
        E H1 H2 (m1 x) (m2 (rget (Q4 * Q4) (m1 x) H1) x)
          (rvo H1 H2 (rget (Q4 * Q4) (m1 x) H1) (rget K2 (m2 (rget (Q4 * Q4) (m1 x) H1) x) H2) x))))))) ≤
    sumTo ((Q4 * Q4) ^ K) (fun H1 => sumTo (K2 ^ (K * n2)) (fun H2 => sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 =>
      smI (fun x => indB (gd c1 c2 && E (rset (Q4 * Q4) (s1 c1 c2 x) H1 c1) (rset K2 (s2 c1 c2 x) H2 c2)
        (s1 c1 c2 x) (s2 c1 c2 x)
        (svo (rset (Q4 * Q4) (s1 c1 c2 x) H1 c1) (rset K2 (s2 c1 c2 x) H2 c2) c1 c2 x))))))) +
      (Q4 * Q4) ^ K * (K2 ^ (K * n2) * (K2 * (NSh * (NSo * K ^ n) * K * (NS2 * (e1 + e2))))) +
      (Q4 * Q4) * (K2 * ((Q4 * Q4) ^ K * (K2 ^ (K * n2) *
        (K * (NSo * (K ^ n * (s * k))) * (NS2 * (NR * (Q4 ^ m * 1))))))) := by
  intro Com1 Pf1 Cmi Pfi smR smI m1 m2 rvo s1 s2 svo gd
  have fo := fs_open2T (NS1 := NSh * (NSo * K ^ n) * K) (n1 := K) hK2 rv sv gz hrv hsv h1 h2 Cmi Pfi op1 sd1 d1
    (comI_hides hK pos hpos) (fun T1 T2 => pfI_hides hK pos hpos op1 g (nxtT T1 T2)) (fun _ _ => Nat.mod_lt _ hK) ov1 hov1 main1 hsd1
    Com2 Pf2T op2 sd2 d2 hc2 hp2 hr2 ov2 hov2 main2 hsd2 hvo1 hvo2 sop1 sop2 hsvo1 hsvo2 E
  -- the other draws' count, and the transfer at each pair of tables
  have hso := smT_lin NS2 NR m
  have so1 := smT_one NS2 NR m
  have step : ∀ H1 H2, K * smR (fun x =>
      indB (gd (rget (Q4 * Q4) (m1 x) H1) (rget K2 (m2 (rget (Q4 * Q4) (m1 x) H1) x) H2) &&
        E H1 H2 (m1 x) (m2 (rget (Q4 * Q4) (m1 x) H1) x)
          (rvo H1 H2 (rget (Q4 * Q4) (m1 x) H1) (rget K2 (m2 (rget (Q4 * Q4) (m1 x) H1) x) H2) x))) ≤
      smI (fun x =>
      indB (gd (rget (Q4 * Q4) (Cmi (main1 x.2.2.2 x.2.2.1) x.1) H1)
          (rget K2 (Cmi (main1 x.2.2.2 x.2.2.1) x.1 + K * Com2 (main2 (rget (Q4 * Q4) (Cmi (main1 x.2.2.2 x.2.2.1) x.1) H1)
            x.2.2.2 x.2.2.1) x.2.1) H2) &&
        E H1 H2 (Cmi (main1 x.2.2.2 x.2.2.1) x.1)
          (Cmi (main1 x.2.2.2 x.2.2.1) x.1 + K * Com2 (main2 (rget (Q4 * Q4) (Cmi (main1 x.2.2.2 x.2.2.1) x.1) H1)
            x.2.2.2 x.2.2.1) x.2.1)
          ((ov1 (rv (rget K2 (Cmi (main1 x.2.2.2 x.2.2.1) x.1 + K * Com2 (main2 (rget (Q4 * Q4)
              (Cmi (main1 x.2.2.2 x.2.2.1) x.1) H1) x.2.2.2 x.2.2.1) x.2.1) H2)
              (efOf (rget (Q4 * Q4) (Cmi (main1 x.2.2.2 x.2.2.1) x.1) H1 / Q4))
              (efOf (rget (Q4 * Q4) (Cmi (main1 x.2.2.2 x.2.2.1) x.1) H1 % Q4)) x.2.2.1 x.2.2.2)).map
              (fun _ => Pfi H1 H2 (main1 x.2.2.2 x.2.2.1) x.1),
           (ov2 (rv (rget K2 (Cmi (main1 x.2.2.2 x.2.2.1) x.1 + K * Com2 (main2 (rget (Q4 * Q4)
              (Cmi (main1 x.2.2.2 x.2.2.1) x.1) H1) x.2.2.2 x.2.2.1) x.2.1) H2)
              (efOf (rget (Q4 * Q4) (Cmi (main1 x.2.2.2 x.2.2.1) x.1) H1 / Q4))
              (efOf (rget (Q4 * Q4) (Cmi (main1 x.2.2.2 x.2.2.1) x.1) H1 % Q4)) x.2.2.1 x.2.2.2)).map
              (fun _ => Pf2T H1 H2 (main2 (rget (Q4 * Q4) (Cmi (main1 x.2.2.2 x.2.2.1) x.1) H1) x.2.2.2 x.2.2.1) x.2.1),
           rv (rget K2 (Cmi (main1 x.2.2.2 x.2.2.1) x.1 + K * Com2 (main2 (rget (Q4 * Q4)
              (Cmi (main1 x.2.2.2 x.2.2.1) x.1) H1) x.2.2.2 x.2.2.1) x.2.1) H2)
              (efOf (rget (Q4 * Q4) (Cmi (main1 x.2.2.2 x.2.2.1) x.1) H1 / Q4))
              (efOf (rget (Q4 * Q4) (Cmi (main1 x.2.2.2 x.2.2.1) x.1) H1 % Q4)) x.2.2.1 x.2.2.2))) +
        K * (NSo * (K ^ n * (s * k))) * (NS2 * (NR * (Q4 ^ m * 1))) := fun H1 H2 => by
    have tr := (transferR_in (n := n) (NSh := NSh) (NSo := NSo) (s := s) (k := k) hK (smT NS2 NR m) hso pos hpos op1 g hs (nxtT H1 H2) (fun y => main1 y.2.2 y.2.1)
      (fun y c pf => gd (rget (Q4 * Q4) c H1)
          (rget K2 (c + K * Com2 (main2 (rget (Q4 * Q4) c H1) y.2.2 y.2.1) y.1) H2) &&
        E H1 H2 c (c + K * Com2 (main2 (rget (Q4 * Q4) c H1) y.2.2 y.2.1) y.1)
          ((ov1 (rv (rget K2 (c + K * Com2 (main2 (rget (Q4 * Q4) c H1) y.2.2 y.2.1) y.1) H2)
              (efOf (rget (Q4 * Q4) c H1 / Q4)) (efOf (rget (Q4 * Q4) c H1 % Q4)) y.2.1 y.2.2)).map (fun _ => pf),
           (ov2 (rv (rget K2 (c + K * Com2 (main2 (rget (Q4 * Q4) c H1) y.2.2 y.2.1) y.1) H2)
              (efOf (rget (Q4 * Q4) c H1 / Q4)) (efOf (rget (Q4 * Q4) c H1 % Q4)) y.2.1 y.2.2)).map
              (fun _ => Pf2T H1 H2 (main2 (rget (Q4 * Q4) c H1) y.2.2 y.2.1) y.1),
           rv (rget K2 (c + K * Com2 (main2 (rget (Q4 * Q4) c H1) y.2.2 y.2.1) y.1) H2)
              (efOf (rget (Q4 * Q4) c H1 / Q4)) (efOf (rget (Q4 * Q4) c H1 % Q4)) y.2.1 y.2.2))).1
    rw [hso, hso, so1] at tr
    exact tr
  have hb : K * ((Q4 * Q4) * (K2 * sumTo ((Q4 * Q4) ^ K) (fun H1 => sumTo (K2 ^ (K * n2)) (fun H2 => smR (fun x =>
      indB (gd (rget (Q4 * Q4) (m1 x) H1) (rget K2 (m2 (rget (Q4 * Q4) (m1 x) H1) x) H2) &&
        E H1 H2 (m1 x) (m2 (rget (Q4 * Q4) (m1 x) H1) x)
          (rvo H1 H2 (rget (Q4 * Q4) (m1 x) H1) (rget K2 (m2 (rget (Q4 * Q4) (m1 x) H1) x) H2) x))))))) =
      (Q4 * Q4) * (K2 * sumTo ((Q4 * Q4) ^ K) (fun H1 => sumTo (K2 ^ (K * n2)) (fun H2 => K * smR (fun x =>
      indB (gd (rget (Q4 * Q4) (m1 x) H1) (rget K2 (m2 (rget (Q4 * Q4) (m1 x) H1) x) H2) &&
        E H1 H2 (m1 x) (m2 (rget (Q4 * Q4) (m1 x) H1) x)
          (rvo H1 H2 (rget (Q4 * Q4) (m1 x) H1) (rget K2 (m2 (rget (Q4 * Q4) (m1 x) H1) x) H2) x)))))) := by
    rw [Nat.mul_left_comm K (Q4 * Q4), Nat.mul_left_comm K K2, sumTo_mul]
    exact congrArg (fun z => Q4 * Q4 * (K2 * z)) (sumTo_congr _ (fun H1 _ => sumTo_mul _ _ _))
  rw [hb]
  refine Nat.le_trans (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _
    (sumTo_mono _ (fun H1 _ => sumTo_mono _ (fun H2 _ => step H1 H2))))) ?_
  simp only [sumTo_add, sumTo_const]
  rw [Nat.mul_add K2, Nat.mul_add (Q4 * Q4)]
  exact Nat.add_le_add_right fo _

/-- **Fiat–Shamir over three rounds, the views reading the three tables**
    (`fs_zk3` as `fs_zk2T` takes `fs_zk2`). -/
theorem fs_zk3T {X Vw : Type} {K1 K2 K3 n1 n2 n3 ε : Nat} (hK1 : 0 < K1) (hK2 : 0 < K2) (hK3 : 0 < K3)
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
    K1 * (K2 * (K3 * sumTo (K1 ^ n1) (fun H1 => sumTo (K2 ^ n2) (fun H2 => sumTo (K3 ^ n3) (fun H3 => sm (fun x =>
      indB (gd (rget K1 (m1 x) H1) (rget K2 (m2 (rget K1 (m1 x) H1) x) H2)
          (rget K3 (m3 (rget K1 (m1 x) H1) (rget K2 (m2 (rget K1 (m1 x) H1) x) H2) x) H3) &&
        E H1 H2 H3 (m1 x) (m2 (rget K1 (m1 x) H1) x) (m3 (rget K1 (m1 x) H1) (rget K2 (m2 (rget K1 (m1 x) H1) x) H2) x)
          (rvT H1 H2 H3 (rget K1 (m1 x) H1) (rget K2 (m2 (rget K1 (m1 x) H1) x) H2)
            (rget K3 (m3 (rget K1 (m1 x) H1) (rget K2 (m2 (rget K1 (m1 x) H1) x) H2) x) H3) x)))))))) ≤
    sumTo (K1 ^ n1) (fun H1 => sumTo (K2 ^ n2) (fun H2 => sumTo (K3 ^ n3) (fun H3 => sumTo K1 (fun c1 =>
      sumTo K2 (fun c2 => sumTo K3 (fun c3 => sm (fun x =>
        indB (gd c1 c2 c3 && E (rset K1 (s1 c1 c2 c3 x) H1 c1) (rset K2 (s2 c1 c2 c3 x) H2 c2)
          (rset K3 (s3 c1 c2 c3 x) H3 c3) (s1 c1 c2 c3 x) (s2 c1 c2 c3 x) (s3 c1 c2 c3 x)
          (svT (rset K1 (s1 c1 c2 c3 x) H1 c1) (rset K2 (s2 c1 c2 c3 x) H2 c2) (rset K3 (s3 c1 c2 c3 x) H3 c3)
            c1 c2 c3 x))))))))) +
      K1 ^ n1 * (K2 ^ n2 * (K3 ^ n3 * ε)) := by
  rw [fs_real3 (Vw := X) hK1 hK2 hK3 sm hsm m1 m2 m3 hm1 hm2 hm3 (fun _ _ _ x => x)
    (fun H1 H2 H3 c1 c2 c3 a b c x => gd c1 c2 c3 && E H1 H2 H3 a b c (rvT H1 H2 H3 c1 c2 c3 x))]
  calc sumTo (K1 ^ n1) (fun H1 => sumTo (K2 ^ n2) (fun H2 => sumTo (K3 ^ n3) (fun H3 => sumTo K1 (fun c1 =>
        sumTo K2 (fun c2 => sumTo K3 (fun c3 => sm (fun x =>
          indB (gd c1 c2 c3 && E (rset K1 (m1 x) H1 c1) (rset K2 (m2 c1 x) H2 c2) (rset K3 (m3 c1 c2 x) H3 c3)
            (m1 x) (m2 c1 x) (m3 c1 c2 x)
            (rvT (rset K1 (m1 x) H1 c1) (rset K2 (m2 c1 x) H2 c2) (rset K3 (m3 c1 c2 x) H3 c3) c1 c2 c3 x)))))))))
      ≤ sumTo (K1 ^ n1) (fun H1 => sumTo (K2 ^ n2) (fun H2 => sumTo (K3 ^ n3) (fun H3 => sumTo K1 (fun c1 =>
        sumTo K2 (fun c2 => sumTo K3 (fun c3 => sm (fun x =>
          indB (gd c1 c2 c3 && E (rset K1 (s1 c1 c2 c3 x) H1 c1) (rset K2 (s2 c1 c2 c3 x) H2 c2)
            (rset K3 (s3 c1 c2 c3 x) H3 c3) (s1 c1 c2 c3 x) (s2 c1 c2 c3 x) (s3 c1 c2 c3 x)
            (svT (rset K1 (s1 c1 c2 c3 x) H1 c1) (rset K2 (s2 c1 c2 c3 x) H2 c2) (rset K3 (s3 c1 c2 c3 x) H3 c3)
              c1 c2 c3 x)))))) + ε))) :=
        sumTo_mono _ (fun H1 _ => sumTo_mono _ (fun H2 _ => sumTo_mono _ (fun H3 _ =>
          h H1 H2 H3 (fun c1 c2 c3 a b c v => E (rset K1 a H1 c1) (rset K2 b H2 c2) (rset K3 c H3 c3) a b c v))))
    _ = _ := by simp only [sumTo_add, sumTo_const]
/-- **Fiat–Shamir over three rounds, every commitment opened, the openings
    reading the three oracle tables** (`fs_open3` over `fs_zk3T`): hiding
    given at every triple of tables.  After the reprogrammings each opening
    reads the tables set at the three messages, a choice by the
    commitments' values (`comPf_choose`, the second and third as a pair),
    each read at the other's value (`open_two_coreT`).  One direction. -/
theorem fs_open3T {PV PB D1 O1 P1 D2 O2 P2 D3 O3 P3 : Type} {NR m e1 e2 NS1 NS2 NS3 K2 K3 n1 n2 n3 : Nat}
    (hK2 : 0 < K2) (hK3 : 0 < K3)
    (rv sv : Nat → Nat → EF → EF → Nat → (Nat → Tup) → TViewN PV PB) (gz : Nat → Nat → Bool)
    (hrv : ∀ c2 c3 α β r t, rv c2 c3 α β r t = none ∨ ∃ p x y, rv c2 c3 α β r t = some (p, α, β, x, y))
    (hsv : ∀ c2 c3 α β r t, ∃ p x y, sv c2 c3 α β r t = some (p, α, β, x, y))
    (h1 : ∀ c2 c3, gz c2 c3 = true → ∀ E : TViewN PV PB → Bool,
      tsumN NR m (fun α β r t => indB (genB β && E (rv c2 c3 α β r t))) ≤
        tsumN NR m (fun α β r t => indB (genB β && E (sv c2 c3 α β r t))) + e1 + e2)
    (h2 : ∀ c2 c3, gz c2 c3 = true → ∀ E : TViewN PV PB → Bool,
      tsumN NR m (fun α β r t => indB (genB β && E (sv c2 c3 α β r t))) ≤
        tsumN NR m (fun α β r t => indB (genB β && E (rv c2 c3 α β r t))) + e1 + e2)
    (Com1 : D1 → Nat → Nat) (Pf1T : Nat → Nat → Nat → D1 → Nat → P1) (op1 : D1 → O1) (sd1 : O1 → D1) (d1 : D1)
    (hc1 : ComHides NS1 Com1) (hp1 : ∀ T1 T2 T3, ComPfHides NS1 Com1 (Pf1T T1 T2 T3) op1) (hr1 : ∀ d σ, Com1 d σ < n1)
    (ov1 : TViewN PV PB → Option O1) (hov1 : ov1 none = none) (main1 : (Nat → Tup) → Nat → D1)
    (hsd1 : ∀ t r, op1 (sd1 (op1 (main1 t r))) = op1 (main1 t r))
    (Com2 : D2 → Nat → Nat) (Pf2T : Nat → Nat → Nat → D2 → Nat → P2) (op2 : D2 → O2) (sd2 : O2 → D2) (d2 : D2)
    (hc2 : ComHides NS2 Com2) (hp2 : ∀ T1 T2 T3, ComPfHides NS2 Com2 (Pf2T T1 T2 T3) op2) (hr2 : ∀ d σ, Com2 d σ < n2)
    (ov2 : TViewN PV PB → Option O2) (hov2 : ov2 none = none) (main2 : Nat → (Nat → Tup) → Nat → D2)
    (hsd2 : ∀ c t r, op2 (sd2 (op2 (main2 c t r))) = op2 (main2 c t r))
    (Com3 : D3 → Nat → Nat) (Pf3T : Nat → Nat → Nat → D3 → Nat → P3) (op3 : D3 → O3) (sd3 : O3 → D3) (d3 : D3)
    (hc3 : ComHides NS3 Com3) (hp3 : ∀ T1 T2 T3, ComPfHides NS3 Com3 (Pf3T T1 T2 T3) op3) (hr3 : ∀ d σ, Com3 d σ < n3)
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
      ((ov1 (rv c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)).map (fun _ => Pf1T T1 T2 T3 (main1 x.2.2.2 x.2.2.1) x.1),
       (ovPair ov2 ov3 (rv c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)).map
         (fun _ => pfPair NS2 (Pf2T T1 T2 T3) (Pf3T T1 T2 T3) (main2 c1 x.2.2.2 x.2.2.1, main3 c1 c2 x.2.2.2 x.2.2.1) x.2.1),
       rv c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)
    let s1 := fun (_ c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) => Com1 (sd1 (sop1 c2 c3 x.2.2.1 x.2.2.2)) x.1
    let s2 := fun (c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      s1 c1 c2 c3 x + n1 * Com2 (sd2 (sop2 c2 c3 c1 x.2.2.1 x.2.2.2)) (x.2.1 % NS2)
    let s3 := fun (c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      s1 c1 c2 c3 x + n1 * comPair NS2 n2 Com2 Com3
        (sd2 (sop2 c2 c3 c1 x.2.2.1 x.2.2.2), sd3 (sop3 c2 c3 c1 x.2.2.1 x.2.2.2)) x.2.1
    let svo := fun (T1 T2 T3 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      (some (Pf1T T1 T2 T3 (sd1 (sop1 c2 c3 x.2.2.1 x.2.2.2)) x.1),
       some (pfPair NS2 (Pf2T T1 T2 T3) (Pf3T T1 T2 T3) (sd2 (sop2 c2 c3 c1 x.2.2.1 x.2.2.2), sd3 (sop3 c2 c3 c1 x.2.2.1 x.2.2.2)) x.2.1),
       sv c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)
    let gd := fun (c1 c2 c3 : Nat) => genB (efOf (c1 % Q4)) && gz c2 c3
    (Q4 * Q4) * (K2 * (K3 * sumTo ((Q4 * Q4) ^ n1) (fun H1 => sumTo (K2 ^ (n1 * n2)) (fun H2 =>
      sumTo (K3 ^ (n1 * (n2 * n3))) (fun H3 => sm (fun x =>
      indB (gd (rget (Q4 * Q4) (m1 x) H1) (rget K2 (m2 (rget (Q4 * Q4) (m1 x) H1) x) H2)
          (rget K3 (m3 (rget (Q4 * Q4) (m1 x) H1) (rget K2 (m2 (rget (Q4 * Q4) (m1 x) H1) x) H2) x) H3) &&
        E H1 H2 H3 (m1 x) (m2 (rget (Q4 * Q4) (m1 x) H1) x)
          (m3 (rget (Q4 * Q4) (m1 x) H1) (rget K2 (m2 (rget (Q4 * Q4) (m1 x) H1) x) H2) x)
          (rvo H1 H2 H3 (rget (Q4 * Q4) (m1 x) H1) (rget K2 (m2 (rget (Q4 * Q4) (m1 x) H1) x) H2)
            (rget K3 (m3 (rget (Q4 * Q4) (m1 x) H1) (rget K2 (m2 (rget (Q4 * Q4) (m1 x) H1) x) H2) x) H3) x)))))))) ≤
    sumTo ((Q4 * Q4) ^ n1) (fun H1 => sumTo (K2 ^ (n1 * n2)) (fun H2 => sumTo (K3 ^ (n1 * (n2 * n3))) (fun H3 =>
      sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo K3 (fun c3 => sm (fun x =>
        indB (gd c1 c2 c3 && E (rset (Q4 * Q4) (s1 c1 c2 c3 x) H1 c1) (rset K2 (s2 c1 c2 c3 x) H2 c2)
          (rset K3 (s3 c1 c2 c3 x) H3 c3) (s1 c1 c2 c3 x) (s2 c1 c2 c3 x) (s3 c1 c2 c3 x)
          (svo (rset (Q4 * Q4) (s1 c1 c2 c3 x) H1 c1) (rset K2 (s2 c1 c2 c3 x) H2 c2) (rset K3 (s3 c1 c2 c3 x) H3 c3)
            c1 c2 c3 x))))))))) +
      (Q4 * Q4) ^ n1 * (K2 ^ (n1 * n2) * (K3 ^ (n1 * (n2 * n3)) *
        (K2 * (K3 * (NS1 * (NS2 * NS3 * (e1 + e2))))))) := by
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
  refine fs_zk3T (K1 := Q4 * Q4) (K2 := K2) (K3 := K3) (n1 := n1) (n2 := n1 * n2) (n3 := n1 * (n2 * n3))
    (Nat.mul_pos Q4_pos Q4_pos) hK2 hK3 sm hsm m1 m2 m3 (fun x => hr1 _ _) (fun _ x => pair_lt (hr1 _ _) (hr2 _ _))
    (fun _ _ x => pair_lt (hr1 _ _) (hc23 _ _)) s1 s2 s3 rvo svo gd (fun H1 H2 H3 F => ?_) E
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
    have core := open_two_coreT (NR := NR) (m := m) (rv c2 c3) (sv c2 c3) (hrv c2 c3) (hsv c2 c3) (h1 c2 c3 hg)
      (h2 c2 c3 hg) Com1
      (fun c v d σ => Pf1T (rset (Q4 * Q4) (Com1 d σ) H1 c) (rset K2 (Com1 d σ + n1 * (v % n2)) H2 c2)
        (rset K3 (Com1 d σ + n1 * v) H3 c3) d σ) op1 sd1 d1 hc1
      (fun c v => comPf_choose (Pf := fun T d σ => Pf1T (rset (Q4 * Q4) T H1 c) (rset K2 (T + n1 * (v % n2)) H2 c2)
        (rset K3 (T + n1 * v) H3 c3) d σ) (fun T => hp1 _ _ _) hr1 id)
      ov1 hov1 main1 hsd1
      (comPair NS2 n2 Com2 Com3)
      (fun c v d σ => pfPair NS2
        (Pf2T (rset (Q4 * Q4) v H1 c) (rset K2 (v + n1 * (comPair NS2 n2 Com2 Com3 d σ % n2)) H2 c2)
          (rset K3 (v + n1 * comPair NS2 n2 Com2 Com3 d σ) H3 c3))
        (Pf3T (rset (Q4 * Q4) v H1 c) (rset K2 (v + n1 * (comPair NS2 n2 Com2 Com3 d σ % n2)) H2 c2)
          (rset K3 (v + n1 * comPair NS2 n2 Com2 Com3 d σ) H3 c3)) d σ)
      (fun d => (op2 d.1, op3 d.2)) (fun o => (sd2 o.1, sd3 o.2))
      (d2, d3) (ComHides.prod hc2 hc3)
      (fun c v => comPf_choose (Pf := fun T d σ => pfPair NS2
        (Pf2T (rset (Q4 * Q4) v H1 c) (rset K2 (v + n1 * (T % n2)) H2 c2) (rset K3 (v + n1 * T) H3 c3))
        (Pf3T (rset (Q4 * Q4) v H1 c) (rset K2 (v + n1 * (T % n2)) H2 c2) (rset K3 (v + n1 * T) H3 c3)) d σ)
        (fun T => ComPfHides.prod (hp2 _ _ _) (hp3 _ _ _)) hc23 id)
      (ovPair ov2 ov3) hov23
      (fun c t r => (main2 c t r, main3 c c2 t r))
      (fun c t r => by show (op2 (sd2 (op2 (main2 c t r))), op3 (sd3 (op3 (main3 c c2 t r)))) = _; rw [hsd2, hsd3])
      (hvo1 c2 c3) hvo23 (sop1 c2 c3) (fun c r t => (sop2 c2 c3 c r t, sop3 c2 c3 c r t)) (hsvo1 c2 c3) hsvo23
      (fun c a b p q w => F c c2 c3 a (a + n1 * (b % n2)) (a + n1 * b) (p, q, w))
    simp only [comPair_mod Com3 hr2] at core
    exact core


/-- **Three Fiat–Shamir rounds, the first commitment drawn from the oracle,
    the distinguisher's queries and the later openings reading the three
    Fiat–Shamir tables**: `fs_open3ROM` with the transfer at each triple of
    tables and `fs_open3T` at the ideal opening.  One direction, with
    `fs_open2ROMT`'s limits. -/
theorem fs_open3ROMT {PV PB D O P D2 O2 P2 D3 O3 P3 : Type}
    {K NR m e1 e2 NSh NSo s k n NS2 NS3 K2 K3 n2 n3 : Nat}
    (hK : 0 < K) (hK2 : 0 < K2) (hK3 : 0 < K3)
    (rv sv : Nat → Nat → EF → EF → Nat → (Nat → Tup) → TViewN PV PB) (gz : Nat → Nat → Bool)
    (hrv : ∀ c2 c3 α β r t, rv c2 c3 α β r t = none ∨ ∃ p x y, rv c2 c3 α β r t = some (p, α, β, x, y))
    (hsv : ∀ c2 c3 α β r t, ∃ p x y, sv c2 c3 α β r t = some (p, α, β, x, y))
    (h1 : ∀ c2 c3, gz c2 c3 = true → ∀ E : TViewN PV PB → Bool,
      tsumN NR m (fun α β r t => indB (genB β && E (rv c2 c3 α β r t))) ≤
        tsumN NR m (fun α β r t => indB (genB β && E (sv c2 c3 α β r t))) + e1 + e2)
    (h2 : ∀ c2 c3, gz c2 c3 = true → ∀ E : TViewN PV PB → Bool,
      tsumN NR m (fun α β r t => indB (genB β && E (sv c2 c3 α β r t))) ≤
        tsumN NR m (fun α β r t => indB (genB β && E (rv c2 c3 α β r t))) + e1 + e2)
    (pos : D → Nat → Nat → Nat) (hpos : ∀ d σo σh, pos d σo σh < n) (g : O → Nat → P)
    (hs : ∀ d σo v, sumTo NSh (fun σh => indB (decide (pos d σo σh = v))) ≤ s)
    (nxtT : Nat → Nat → Nat → P → Nat → List Nat → Nat) (op1 : D → O) (sd1 : O → D) (d1 : D)
    (ov1 : TViewN PV PB → Option O) (hov1 : ov1 none = none) (main1 : (Nat → Tup) → Nat → D)
    (hsd1 : ∀ t r, op1 (sd1 (op1 (main1 t r))) = op1 (main1 t r))
    (Com2 : D2 → Nat → Nat) (Pf2T : Nat → Nat → Nat → D2 → Nat → P2) (op2 : D2 → O2) (sd2 : O2 → D2) (d2 : D2)
    (hc2 : ComHides NS2 Com2) (hp2 : ∀ T1 T2 T3, ComPfHides NS2 Com2 (Pf2T T1 T2 T3) op2) (hr2 : ∀ d σ, Com2 d σ < n2)
    (ov2 : TViewN PV PB → Option O2) (hov2 : ov2 none = none) (main2 : Nat → (Nat → Tup) → Nat → D2)
    (hsd2 : ∀ c t r, op2 (sd2 (op2 (main2 c t r))) = op2 (main2 c t r))
    (Com3 : D3 → Nat → Nat) (Pf3T : Nat → Nat → Nat → D3 → Nat → P3) (op3 : D3 → O3) (sd3 : O3 → D3) (d3 : D3)
    (hc3 : ComHides NS3 Com3) (hp3 : ∀ T1 T2 T3, ComPfHides NS3 Com3 (Pf3T T1 T2 T3) op3) (hr3 : ∀ d σ, Com3 d σ < n3)
    (ov3 : TViewN PV PB → Option O3) (hov3 : ov3 none = none) (main3 : Nat → Nat → (Nat → Tup) → Nat → D3)
    (hsd3 : ∀ c c' t r, op3 (sd3 (op3 (main3 c c' t r))) = op3 (main3 c c' t r))
    (hvo1 : ∀ c2 c3 c r t, rv c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t = none ∨
      ov1 (rv c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (op1 (main1 t r)))
    (hvo2 : ∀ c2 c3 c r t, rv c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t = none ∨
      ov2 (rv c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (op2 (main2 c t r)))
    (hvo3 : ∀ c2 c3 c r t, rv c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t = none ∨
      ov3 (rv c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (op3 (main3 c c2 t r)))
    (sop1 : Nat → Nat → Nat → (Nat → Tup) → O) (sop2 : Nat → Nat → Nat → Nat → (Nat → Tup) → O2)
    (sop3 : Nat → Nat → Nat → Nat → (Nat → Tup) → O3)
    (hsvo1 : ∀ c2 c3 c r t, ov1 (sv c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (sop1 c2 c3 r t))
    (hsvo2 : ∀ c2 c3 c r t, ov2 (sv c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (sop2 c2 c3 c r t))
    (hsvo3 : ∀ c2 c3 c r t, ov3 (sv c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (sop3 c2 c3 c r t))
    (E : Nat → Nat → Nat → Nat → Nat → Nat → Option (P × List Nat) × Option (P2 × P3) × TViewN PV PB → Bool) :
    let Com1 := comR K NSh NSo pos
    let Pf1 := fun T1 T2 T3 => pfR K NSh NSo k pos op1 g (nxtT T1 T2 T3)
    let Cmi := comI K NSh NSo pos
    let Pfi := fun T1 T2 T3 => pfI K NSh NSo k pos op1 g (nxtT T1 T2 T3)
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
    let rvo := fun (T1 T2 T3 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      ((ov1 (rv c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)).map (fun _ => Pf1 T1 T2 T3 (main1 x.2.2.2 x.2.2.1) x.1),
       (ovPair ov2 ov3 (rv c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)).map
         (fun _ => pfPair NS2 (Pf2T T1 T2 T3) (Pf3T T1 T2 T3) (main2 c1 x.2.2.2 x.2.2.1, main3 c1 c2 x.2.2.2 x.2.2.1) x.2.1),
       rv c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)
    let s1 := fun (_c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) => Cmi (sd1 (sop1 c2 c3 x.2.2.1 x.2.2.2)) x.1
    let s2 := fun (c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      s1 c1 c2 c3 x + K * Com2 (sd2 (sop2 c2 c3 c1 x.2.2.1 x.2.2.2)) (x.2.1 % NS2)
    let s3 := fun (c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      s1 c1 c2 c3 x + K * comPair NS2 n2 Com2 Com3
        (sd2 (sop2 c2 c3 c1 x.2.2.1 x.2.2.2), sd3 (sop3 c2 c3 c1 x.2.2.1 x.2.2.2)) x.2.1
    let svo := fun (T1 T2 T3 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      (some (Pfi T1 T2 T3 (sd1 (sop1 c2 c3 x.2.2.1 x.2.2.2)) x.1),
       some (pfPair NS2 (Pf2T T1 T2 T3) (Pf3T T1 T2 T3) (sd2 (sop2 c2 c3 c1 x.2.2.1 x.2.2.2), sd3 (sop3 c2 c3 c1 x.2.2.1 x.2.2.2)) x.2.1),
       sv c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)
    let gd := fun (c1 c2 c3 : Nat) => genB (efOf (c1 % Q4)) && gz c2 c3
    K * ((Q4 * Q4) * (K2 * (K3 * sumTo ((Q4 * Q4) ^ K) (fun H1 => sumTo (K2 ^ (K * n2)) (fun H2 =>
      sumTo (K3 ^ (K * (n2 * n3))) (fun H3 => smR (fun x =>
      indB (gd (rget (Q4 * Q4) (m1 x) H1) (rget K2 (m2 (rget (Q4 * Q4) (m1 x) H1) x) H2)
          (rget K3 (m3 (rget (Q4 * Q4) (m1 x) H1) (rget K2 (m2 (rget (Q4 * Q4) (m1 x) H1) x) H2) x) H3) &&
        E H1 H2 H3 (m1 x) (m2 (rget (Q4 * Q4) (m1 x) H1) x)
          (m3 (rget (Q4 * Q4) (m1 x) H1) (rget K2 (m2 (rget (Q4 * Q4) (m1 x) H1) x) H2) x)
          (rvo H1 H2 H3 (rget (Q4 * Q4) (m1 x) H1) (rget K2 (m2 (rget (Q4 * Q4) (m1 x) H1) x) H2)
            (rget K3 (m3 (rget (Q4 * Q4) (m1 x) H1) (rget K2 (m2 (rget (Q4 * Q4) (m1 x) H1) x) H2) x) H3) x))))))))) ≤
    sumTo ((Q4 * Q4) ^ K) (fun H1 => sumTo (K2 ^ (K * n2)) (fun H2 => sumTo (K3 ^ (K * (n2 * n3))) (fun H3 =>
      sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo K3 (fun c3 => smI (fun x =>
        indB (gd c1 c2 c3 && E (rset (Q4 * Q4) (s1 c1 c2 c3 x) H1 c1) (rset K2 (s2 c1 c2 c3 x) H2 c2)
          (rset K3 (s3 c1 c2 c3 x) H3 c3) (s1 c1 c2 c3 x) (s2 c1 c2 c3 x) (s3 c1 c2 c3 x)
          (svo (rset (Q4 * Q4) (s1 c1 c2 c3 x) H1 c1) (rset K2 (s2 c1 c2 c3 x) H2 c2) (rset K3 (s3 c1 c2 c3 x) H3 c3)
            c1 c2 c3 x))))))))) +
      (Q4 * Q4) ^ K * (K2 ^ (K * n2) * (K3 ^ (K * (n2 * n3)) *
        (K2 * (K3 * (NSh * (NSo * K ^ n) * K * (NS2 * NS3 * (e1 + e2))))))) +
      (Q4 * Q4) * (K2 * (K3 * ((Q4 * Q4) ^ K * (K2 ^ (K * n2) * (K3 ^ (K * (n2 * n3)) *
        (K * (NSo * (K ^ n * (s * k))) * (NS2 * NS3 * (NR * (Q4 ^ m * 1))))))))) := by
  intro Com1 Pf1 Cmi Pfi smR smI m1 m2 m3 rvo s1 s2 s3 svo gd
  have fo := fs_open3T (NS1 := NSh * (NSo * K ^ n) * K) (n1 := K) hK2 hK3 rv sv gz hrv hsv h1 h2 Cmi Pfi op1 sd1 d1
    (comI_hides hK pos hpos) (fun T1 T2 T3 => pfI_hides hK pos hpos op1 g (nxtT T1 T2 T3)) (fun _ _ => Nat.mod_lt _ hK) ov1 hov1 main1 hsd1
    Com2 Pf2T op2 sd2 d2 hc2 hp2 hr2 ov2 hov2 main2 hsd2 Com3 Pf3T op3 sd3 d3 hc3 hp3 hr3 ov3 hov3 main3 hsd3
    hvo1 hvo2 hvo3 sop1 sop2 sop3 hsvo1 hsvo2 hsvo3 E
  -- the event, read off the first commitment's value `c` and opening `pf`
  let ev := fun (H1 H2 H3 : Nat) (y : Nat × Nat × (Nat → Tup)) (c : Nat) (pf : P × List Nat) =>
    let c1 := rget (Q4 * Q4) c H1
    let mm2 := c + K * Com2 (main2 c1 y.2.2 y.2.1) (y.1 % NS2)
    let c2 := rget K2 mm2 H2
    let mm3 := c + K * comPair NS2 n2 Com2 Com3 (main2 c1 y.2.2 y.2.1, main3 c1 c2 y.2.2 y.2.1) y.1
    let c3 := rget K3 mm3 H3
    gd c1 c2 c3 && E H1 H2 H3 c mm2 mm3
      ((ov1 (rv c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) y.2.1 y.2.2)).map (fun _ => pf),
       (ovPair ov2 ov3 (rv c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) y.2.1 y.2.2)).map
         (fun _ => pfPair NS2 (Pf2T H1 H2 H3) (Pf3T H1 H2 H3) (main2 c1 y.2.2 y.2.1, main3 c1 c2 y.2.2 y.2.1) y.1),
       rv c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) y.2.1 y.2.2)
  have hso := smT_lin (NS2 * NS3) NR m
  have so1 := smT_one (NS2 * NS3) NR m
  have step : ∀ H1 H2 H3,
      K * smR (fun x => indB (ev H1 H2 H3 x.2 (Com1 (main1 x.2.2.2 x.2.2.1) x.1) (Pf1 H1 H2 H3 (main1 x.2.2.2 x.2.2.1) x.1))) ≤
      smI (fun x => indB (ev H1 H2 H3 x.2 (Cmi (main1 x.2.2.2 x.2.2.1) x.1) (Pfi H1 H2 H3 (main1 x.2.2.2 x.2.2.1) x.1))) +
        K * (NSo * (K ^ n * (s * k))) * (NS2 * NS3 * (NR * (Q4 ^ m * 1))) := fun H1 H2 H3 => by
    have tr := (transferR_in (n := n) (NSh := NSh) (NSo := NSo) (s := s) (k := k) hK (smT (NS2 * NS3) NR m) hso
      pos hpos op1 g hs (nxtT H1 H2 H3) (fun y => main1 y.2.2 y.2.1) (fun y c pf => ev H1 H2 H3 y c pf)).1
    rw [hso, hso, so1] at tr
    exact tr
  have hb : ∀ X : Nat → Nat → Nat → Nat, K * ((Q4 * Q4) * (K2 * (K3 * sumTo ((Q4 * Q4) ^ K) (fun H1 =>
      sumTo (K2 ^ (K * n2)) (fun H2 => sumTo (K3 ^ (K * (n2 * n3))) (fun H3 => X H1 H2 H3)))))) =
      (Q4 * Q4) * (K2 * (K3 * sumTo ((Q4 * Q4) ^ K) (fun H1 =>
      sumTo (K2 ^ (K * n2)) (fun H2 => sumTo (K3 ^ (K * (n2 * n3))) (fun H3 => K * X H1 H2 H3))))) := fun X => by
    rw [Nat.mul_left_comm K (Q4 * Q4), Nat.mul_left_comm K K2, Nat.mul_left_comm K K3, sumTo_mul]
    exact congrArg (fun z => Q4 * Q4 * (K2 * (K3 * z))) (sumTo_congr _ (fun H1 _ =>
      (sumTo_mul _ _ _).trans (sumTo_congr _ (fun H2 _ => sumTo_mul _ _ _))))
  rw [hb]
  refine Nat.le_trans (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _
    (sumTo_mono _ (fun H1 _ => sumTo_mono _ (fun H2 _ => sumTo_mono _ (fun H3 _ => step H1 H2 H3))))))) ?_
  simp only [sumTo_add, sumTo_const]
  rw [Nat.mul_add K3, Nat.mul_add K2, Nat.mul_add (Q4 * Q4)]
  exact Nat.add_le_add_right fo _

end Circuit
