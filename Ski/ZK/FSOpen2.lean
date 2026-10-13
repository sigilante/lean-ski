import Ski.ZK.FSRound2Inst

/-!
# Two Fiat–Shamir rounds, both commitments opened

`Ski/ZK/FSRound2.lean` hashes two commitments that the view never opens.
Here both are opened, each with its own hiding given the openings
(`ComPfHides`): the proof carries the first commitment `Com1 (main1 t r)
σ1`, the second `Com2 (main2 c1 t r) σ2` of data computed after the
first challenges, their openings where the proof does not abort, and the
view, whose opened values are the committed data's (`hvo1`, `hvo2`).
The simulator commits and opens data through the values its own view
shows, the second after drawing the challenges (`fs_zkc`'s licence).

`open_real2`: `open_real` with the event reading the draw, so the second
commitment's swap may leave the first's opening in it; two swaps then
reduce the real count to view events, one transcript count per pair of
salts (`open_two_core`), summed over the guarded second challenge in
`fs_open2`.
-/

namespace Circuit

open ZKF

/-- **`open_real` with the event reading the draw.** -/
theorem open_real2 {PV PB D O Pp : Type} {NS NR m : Nat} (Com : D → Nat → Nat) (Pf : D → Nat → Pp) (op : D → O)
    (sd : O → D) (d0 : D) (hcom : ComHides NS Com) (hpf : ComPfHides NS Com Pf op)
    (ov : TViewN PV PB → Option O) (hovn : ov none = none) (main : (Nat → Tup) → Nat → D)
    (hsd : ∀ t r, op (sd (op (main t r))) = op (main t r))
    (v : Nat → (Nat → Tup) → TViewN PV PB) (hvo : ∀ r t, v r t = none ∨ ov (v r t) = some (op (main t r)))
    (F : Nat → (Nat → Tup) → Nat → Option Pp → TViewN PV PB → Bool) :
    sumTo NS (fun σ => sumTo NR (fun r => sumN m (fun t =>
      indB (F r t (Com (main t r) σ) ((ov (v r t)).map (fun _ => Pf (main t r) σ)) (v r t))))) =
    sumTo NS (fun σ => sumTo NR (fun r => sumN m (fun t => indB (openEv Com Pf sd d0 ov (F r t) σ (v r t))))) := by
  have key : ∀ r t, sumTo NS (fun σ => indB (F r t (Com (main t r) σ) ((ov (v r t)).map (fun _ => Pf (main t r) σ))
      (v r t))) = sumTo NS (fun σ => indB (openEv Com Pf sd d0 ov (F r t) σ (v r t))) := by
    intro r t
    rcases hvo r t with e | e
    · rw [e]
      unfold openEv
      rw [hovn]
      exact hcom (main t r) d0 (fun mm => F r t mm none none)
    · unfold openEv
      rw [e]
      exact hpf (main t r) (sd (op (main t r))) (hsd t r).symm (fun mm p => F r t mm (some p) (v r t))
  rw [sig_in, sig_in]
  exact sumTo_congr _ (fun r _ => Nat.le_antisymm (sumN_mono m (fun t => Nat.le_of_eq (key r t)))
    (sumN_mono m (fun t => Nat.le_of_eq (key r t).symm)))

/-- The view event two salts give: each commitment and opening of the data
    the view's openings fix, or of fixed data where it shows nothing. -/
def openEv2 {PV PB D1 O1 P1 D2 O2 P2 : Type} (Com1 : D1 → Nat → Nat) (Pf1 : D1 → Nat → P1) (sd1 : O1 → D1)
    (d1 : D1) (ov1 : TViewN PV PB → Option O1) (Com2 : D2 → Nat → Nat) (Pf2 : D2 → Nat → P2) (sd2 : O2 → D2)
    (d2 : D2) (ov2 : TViewN PV PB → Option O2)
    (F : Nat → Nat → Option P1 → Option P2 → TViewN PV PB → Bool) (σ1 σ2 : Nat) (v : TViewN PV PB) : Bool :=
  openEv Com1 Pf1 sd1 d1 ov1 (fun mm1 p1 w => openEv Com2 Pf2 sd2 d2 ov2 (fun mm2 p2 w' => F mm1 mm2 p1 p2 w') σ2 w)
    σ1 v

theorem openEv2_and {PV PB D1 O1 P1 D2 O2 P2 : Type} (Com1 : D1 → Nat → Nat) (Pf1 : D1 → Nat → P1) (sd1 : O1 → D1)
    (d1 : D1) (ov1 : TViewN PV PB → Option O1) (Com2 : D2 → Nat → Nat) (Pf2 : D2 → Nat → P2) (sd2 : O2 → D2)
    (d2 : D2) (ov2 : TViewN PV PB → Option O2) (b : Bool)
    (F : Nat → Nat → Option P1 → Option P2 → TViewN PV PB → Bool) (σ1 σ2 : Nat) (v : TViewN PV PB) :
    openEv2 Com1 Pf1 sd1 d1 ov1 Com2 Pf2 sd2 d2 ov2 (fun a b' p q w => b && F a b' p q w) σ1 σ2 v =
      (b && openEv2 Com1 Pf1 sd1 d1 ov1 Com2 Pf2 sd2 d2 ov2 F σ1 σ2 v) := by
  unfold openEv2 openEv
  split <;> (dsimp only; split <;> rfl)

theorem openEv2_some {PV PB D1 O1 P1 D2 O2 P2 : Type} (Com1 : D1 → Nat → Nat) (Pf1 : D1 → Nat → P1) (sd1 : O1 → D1)
    (d1 : D1) (ov1 : TViewN PV PB → Option O1) (Com2 : D2 → Nat → Nat) (Pf2 : D2 → Nat → P2) (sd2 : O2 → D2)
    (d2 : D2) (ov2 : TViewN PV PB → Option O2)
    (F : Nat → Nat → Option P1 → Option P2 → TViewN PV PB → Bool) (σ1 σ2 : Nat) (v : TViewN PV PB) (o1 : O1)
    (o2 : O2) (h1 : ov1 v = some o1) (h2 : ov2 v = some o2) :
    openEv2 Com1 Pf1 sd1 d1 ov1 Com2 Pf2 sd2 d2 ov2 F σ1 σ2 v =
      F (Com1 (sd1 o1) σ1) (Com2 (sd2 o2) σ2) (some (Pf1 (sd1 o1) σ1)) (some (Pf2 (sd2 o2) σ2)) v := by
  unfold openEv2 openEv; rw [h1]; dsimp only; rw [h2]

/-- **Two opened commitments beside a transcript**, at one second
    challenge: the real count, both commitments and their openings shown,
    is within `NS1 · NS2 · (e1 + e2)` of the simulator's, which commits
    and opens data through its own view's openings. -/
theorem open_two_core {PV PB D1 O1 P1 D2 O2 P2 : Type} {NR m e1 e2 NS1 NS2 : Nat}
    (rv sv : EF → EF → Nat → (Nat → Tup) → TViewN PV PB)
    (hrv : ∀ α β r t, rv α β r t = none ∨ ∃ p x y, rv α β r t = some (p, α, β, x, y))
    (hsv : ∀ α β r t, ∃ p x y, sv α β r t = some (p, α, β, x, y))
    (h1 : ∀ E : TViewN PV PB → Bool, tsumN NR m (fun α β r t => indB (genB β && E (rv α β r t))) ≤
      tsumN NR m (fun α β r t => indB (genB β && E (sv α β r t))) + e1 + e2)
    (h2 : ∀ E : TViewN PV PB → Bool, tsumN NR m (fun α β r t => indB (genB β && E (sv α β r t))) ≤
      tsumN NR m (fun α β r t => indB (genB β && E (rv α β r t))) + e1 + e2)
    (Com1 : D1 → Nat → Nat) (Pf1 : D1 → Nat → P1) (op1 : D1 → O1) (sd1 : O1 → D1) (d1 : D1)
    (hc1 : ComHides NS1 Com1) (hp1 : ComPfHides NS1 Com1 Pf1 op1) (ov1 : TViewN PV PB → Option O1)
    (hov1 : ov1 none = none) (main1 : (Nat → Tup) → Nat → D1)
    (hsd1 : ∀ t r, op1 (sd1 (op1 (main1 t r))) = op1 (main1 t r))
    (Com2 : D2 → Nat → Nat) (Pf2 : D2 → Nat → P2) (op2 : D2 → O2) (sd2 : O2 → D2) (d2 : D2)
    (hc2 : ComHides NS2 Com2) (hp2 : ComPfHides NS2 Com2 Pf2 op2) (ov2 : TViewN PV PB → Option O2)
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
        ((ov1 (rv (efOf (c / Q4)) (efOf (c % Q4)) r t)).map (fun _ => Pf1 (main1 t r) σ1))
        ((ov2 (rv (efOf (c / Q4)) (efOf (c % Q4)) r t)).map (fun _ => Pf2 (main2 c t r) σ2))
        (rv (efOf (c / Q4)) (efOf (c % Q4)) r t))))))) ≤
    sumTo (Q4 * Q4) (fun c => sumTo NS1 (fun σ1 => sumTo NS2 (fun σ2 => sumTo NR (fun r => sumN m (fun t =>
      indB (genB (efOf (c % Q4)) && F c (Com1 (sd1 (sop1 r t)) σ1) (Com2 (sd2 (sop2 c r t)) σ2)
        (some (Pf1 (sd1 (sop1 r t)) σ1)) (some (Pf2 (sd2 (sop2 c r t)) σ2))
        (sv (efOf (c / Q4)) (efOf (c % Q4)) r t))))))) + NS1 * (NS2 * (e1 + e2)) := by
  have h1' := fun E => Nat.le_trans (h1 E) (Nat.le_of_eq (Nat.add_assoc _ e1 e2))
  have h2' := fun E => Nat.le_trans (h2 E) (Nat.le_of_eq (Nat.add_assoc _ e1 e2))
  let G : Nat → Nat → Nat → TViewN PV PB → Bool := fun σ1 σ2 c w =>
    openEv2 Com1 Pf1 sd1 d1 ov1 Com2 Pf2 sd2 d2 ov2 (F c) σ1 σ2 w
  -- the real side: both commitments swapped, a view event per pair of salts
  have hreal : ∀ c, sumTo NS1 (fun σ1 => sumTo NS2 (fun σ2 => sumTo NR (fun r => sumN m (fun t =>
      indB (genB (efOf (c % Q4)) && F c (Com1 (main1 t r) σ1) (Com2 (main2 c t r) σ2)
        ((ov1 (rv (efOf (c / Q4)) (efOf (c % Q4)) r t)).map (fun _ => Pf1 (main1 t r) σ1))
        ((ov2 (rv (efOf (c / Q4)) (efOf (c % Q4)) r t)).map (fun _ => Pf2 (main2 c t r) σ2))
        (rv (efOf (c / Q4)) (efOf (c % Q4)) r t)))))) =
      sumTo NS2 (fun σ2 => sumTo NS1 (fun σ1 => sumTo NR (fun r => sumN m (fun t =>
        indB (genB (efOf (c % Q4)) && G σ1 σ2 c (rv (efOf (c / Q4)) (efOf (c % Q4)) r t)))))) := fun c => by
    rw [sumTo_congr _ (fun σ1 _ => open_real2 Com2 Pf2 op2 sd2 d2 hc2 hp2 ov2 hov2 (main2 c) (hsd2 c)
      (fun r t => rv (efOf (c / Q4)) (efOf (c % Q4)) r t) (fun r t => hvo2 c r t)
      (fun r t mm2 p2 w => genB (efOf (c % Q4)) && F c (Com1 (main1 t r) σ1) mm2
        ((ov1 w).map (fun _ => Pf1 (main1 t r) σ1)) p2 w))]
    rw [sumTo_exch _ NS2 NS1]
    refine sumTo_congr _ (fun σ2 _ => ?_)
    have e := open_real2 (NR := NR) (m := m) Com1 Pf1 op1 sd1 d1 hc1 hp1 ov1 hov1 main1 hsd1
      (fun r t => rv (efOf (c / Q4)) (efOf (c % Q4)) r t) (fun r t => hvo1 c r t)
      (fun _ _ mm1 p1 w => openEv Com2 Pf2 sd2 d2 ov2 (fun mm2 p2 w' => genB (efOf (c % Q4)) && F c mm1 mm2 p1 p2 w')
        σ2 w)
    refine Eq.trans ?_ (e.trans ?_)
    · refine sumTo_congr _ (fun σ1 _ => sumTo_congr _ (fun r _ => Nat.le_antisymm
        (sumN_mono m (fun t => Nat.le_of_eq ?_)) (sumN_mono m (fun t => Nat.le_of_eq ?_))))
      all_goals (unfold openEv; cases ov2 (rv (efOf (c / Q4)) (efOf (c % Q4)) r t) <;> rfl)
    · have eq : ∀ σ1 r t, indB (openEv Com1 Pf1 sd1 d1 ov1 (fun mm1 p1 w =>
            openEv Com2 Pf2 sd2 d2 ov2 (fun mm2 p2 w' => genB (efOf (c % Q4)) && F c mm1 mm2 p1 p2 w') σ2 w)
            σ1 (rv (efOf (c / Q4)) (efOf (c % Q4)) r t)) =
          indB (genB (efOf (c % Q4)) && G σ1 σ2 c (rv (efOf (c / Q4)) (efOf (c % Q4)) r t)) := fun σ1 r t => by
        show indB (openEv2 Com1 Pf1 sd1 d1 ov1 Com2 Pf2 sd2 d2 ov2
          (fun a b' p q w => genB (efOf (c % Q4)) && F c a b' p q w) σ1 σ2 _) = _
        rw [openEv2_and]
      refine sumTo_congr _ (fun σ1 _ => sumTo_congr _ (fun r _ => Nat.le_antisymm
        (sumN_mono m (fun t => Nat.le_of_eq (eq σ1 r t))) (sumN_mono m (fun t => Nat.le_of_eq (eq σ1 r t).symm))))
  -- the simulated side: its commitments are the view event's
  have hsim : ∀ c, sumTo NS1 (fun σ1 => sumTo NS2 (fun σ2 => sumTo NR (fun r => sumN m (fun t =>
      indB (genB (efOf (c % Q4)) && F c (Com1 (sd1 (sop1 r t)) σ1) (Com2 (sd2 (sop2 c r t)) σ2)
        (some (Pf1 (sd1 (sop1 r t)) σ1)) (some (Pf2 (sd2 (sop2 c r t)) σ2))
        (sv (efOf (c / Q4)) (efOf (c % Q4)) r t)))))) =
      sumTo NS2 (fun σ2 => sumTo NS1 (fun σ1 => sumTo NR (fun r => sumN m (fun t =>
        indB (genB (efOf (c % Q4)) && G σ1 σ2 c (sv (efOf (c / Q4)) (efOf (c % Q4)) r t)))))) := fun c => by
    rw [sumTo_exch _ NS2 NS1]
    refine sumTo_congr _ (fun σ2 _ => sumTo_congr _ (fun σ1 _ => sumTo_congr _ (fun r _ => Nat.le_antisymm
      (sumN_mono m (fun t => Nat.le_of_eq ?_)) (sumN_mono m (fun t => Nat.le_of_eq ?_)))))
    · show _ = indB (genB (efOf (c % Q4)) && openEv2 Com1 Pf1 sd1 d1 ov1 Com2 Pf2 sd2 d2 ov2 (F c) σ1 σ2 _)
      rw [openEv2_some _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (hsvo1 c r t) (hsvo2 c r t)]
    · show indB (genB (efOf (c % Q4)) && openEv2 Com1 Pf1 sd1 d1 ov1 Com2 Pf2 sd2 d2 ov2 (F c) σ1 σ2 _) = _
      rw [openEv2_some _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (hsvo1 c r t) (hsvo2 c r t)]
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

/-- **Fiat–Shamir over two rounds, both commitments opened**, in the
    programmable random-oracle model: the real proof's first message
    `Com1 (main1 t r) σ1`, its LogUp challenges `c1 = H1` there, its second
    message the pair with `Com2 (main2 c1 t r) σ2`, `c2 = H2` there, and
    its output the openings where it does not abort and the view at
    `c2`'s transcript; the simulator commits and opens data through its
    own view's openings, draws both challenges and programs both tables.
    Where the transcript bound holds at each guarded `c2`, `Q4² K2` times
    the real count is within `(Q4²)^n1 K2^(n1 n2) K2 NS1 NS2 (e1 + e2)` of
    the simulator's. -/
theorem fs_open2 {PV PB D1 O1 P1 D2 O2 P2 : Type} {NR m e1 e2 NS1 NS2 K2 n1 n2 : Nat} (hK2 : 0 < K2)
    (rv sv : Nat → EF → EF → Nat → (Nat → Tup) → TViewN PV PB) (gz : Nat → Bool)
    (hrv : ∀ c2 α β r t, rv c2 α β r t = none ∨ ∃ p x y, rv c2 α β r t = some (p, α, β, x, y))
    (hsv : ∀ c2 α β r t, ∃ p x y, sv c2 α β r t = some (p, α, β, x, y))
    (h1 : ∀ c2, gz c2 = true → ∀ E : TViewN PV PB → Bool,
      tsumN NR m (fun α β r t => indB (genB β && E (rv c2 α β r t))) ≤
        tsumN NR m (fun α β r t => indB (genB β && E (sv c2 α β r t))) + e1 + e2)
    (h2 : ∀ c2, gz c2 = true → ∀ E : TViewN PV PB → Bool,
      tsumN NR m (fun α β r t => indB (genB β && E (sv c2 α β r t))) ≤
        tsumN NR m (fun α β r t => indB (genB β && E (rv c2 α β r t))) + e1 + e2)
    (Com1 : D1 → Nat → Nat) (Pf1 : D1 → Nat → P1) (op1 : D1 → O1) (sd1 : O1 → D1) (d1 : D1)
    (hc1 : ComHides NS1 Com1) (hp1 : ComPfHides NS1 Com1 Pf1 op1) (hr1 : ∀ d σ, Com1 d σ < n1)
    (ov1 : TViewN PV PB → Option O1) (hov1 : ov1 none = none) (main1 : (Nat → Tup) → Nat → D1)
    (hsd1 : ∀ t r, op1 (sd1 (op1 (main1 t r))) = op1 (main1 t r))
    (Com2 : D2 → Nat → Nat) (Pf2 : D2 → Nat → P2) (op2 : D2 → O2) (sd2 : O2 → D2) (d2 : D2)
    (hc2 : ComHides NS2 Com2) (hp2 : ComPfHides NS2 Com2 Pf2 op2) (hr2 : ∀ d σ, Com2 d σ < n2)
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
    let rvo := fun (c1 c2 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      ((ov1 (rv c2 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)).map (fun _ => Pf1 (main1 x.2.2.2 x.2.2.1) x.1),
       (ov2 (rv c2 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)).map
         (fun _ => Pf2 (main2 c1 x.2.2.2 x.2.2.1) x.2.1),
       rv c2 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)
    let s1 := fun (c1 c2 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) => Com1 (sd1 (sop1 c2 x.2.2.1 x.2.2.2)) x.1
    let s2 := fun (c1 c2 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      s1 c1 c2 x + n1 * Com2 (sd2 (sop2 c2 c1 x.2.2.1 x.2.2.2)) x.2.1
    let svo := fun (c1 c2 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      (some (Pf1 (sd1 (sop1 c2 x.2.2.1 x.2.2.2)) x.1), some (Pf2 (sd2 (sop2 c2 c1 x.2.2.1 x.2.2.2)) x.2.1),
        sv c2 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)
    let gd := fun (c1 c2 : Nat) => genB (efOf (c1 % Q4)) && gz c2
    (Q4 * Q4) * (K2 * sumTo ((Q4 * Q4) ^ n1) (fun H1 => sumTo (K2 ^ (n1 * n2)) (fun H2 => sm (fun x =>
      indB (gd (rget (Q4 * Q4) (m1 x) H1) (rget K2 (m2 (rget (Q4 * Q4) (m1 x) H1) x) H2) &&
        E H1 H2 (m1 x) (m2 (rget (Q4 * Q4) (m1 x) H1) x)
          (rvo (rget (Q4 * Q4) (m1 x) H1) (rget K2 (m2 (rget (Q4 * Q4) (m1 x) H1) x) H2) x)))))) ≤
    sumTo ((Q4 * Q4) ^ n1) (fun H1 => sumTo (K2 ^ (n1 * n2)) (fun H2 => sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 =>
      sm (fun x => indB (gd c1 c2 && E (rset (Q4 * Q4) (s1 c1 c2 x) H1 c1) (rset K2 (s2 c1 c2 x) H2 c2)
        (s1 c1 c2 x) (s2 c1 c2 x) (svo c1 c2 x))))))) +
      (Q4 * Q4) ^ n1 * (K2 ^ (n1 * n2) * (K2 * (NS1 * (NS2 * (e1 + e2))))) := by
  intro sm m1 m2 rvo s1 s2 svo gd
  have hsm : ∀ (N : Nat) (f : Nat → Nat × Nat × Nat × (Nat → Tup) → Nat),
      sm (fun x => sumTo N (fun i => f i x)) = sumTo N (fun i => sm (f i)) := fun N f => by
    show sumTo NS1 (fun σ1 => sumTo NS2 (fun σ2 => sumTo NR (fun r => sumN m (fun t =>
      sumTo N (fun i => f i (σ1, σ2, r, t)))))) = _
    rw [sumTo_congr _ (fun σ1 _ => sm_exch (NS := NS2) (NR := NR) (m := m) (N := N)
      (fun i σ2 r t => f i (σ1, σ2, r, t)))]
    exact sumTo_exch _ N NS1
  refine fs_zk2 (K1 := Q4 * Q4) (K2 := K2) (n1 := n1) (n2 := n1 * n2) (Nat.mul_pos Q4_pos Q4_pos) hK2 sm hsm m1 m2
    (fun x => hr1 _ _) (fun _ x => pair_lt (hr1 _ _) (hr2 _ _)) s1 s2 rvo svo gd (fun F => ?_) E
  show sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo NS1 (fun σ1 => sumTo NS2 (fun σ2 => sumTo NR (fun r =>
    sumN m (fun t => _)))))) ≤ _
  rw [sumTo_exch _ K2 (Q4 * Q4), sumTo_exch _ K2 (Q4 * Q4), ← sumTo_const (NS1 * (NS2 * (e1 + e2))) K2, ← sumTo_add]
  refine sumTo_mono _ (fun c2 _ => ?_)
  cases hg : gz c2
  · simp only [gd, hg, Bool.and_false, Bool.false_and]
    exact Nat.le_add_right _ _
  · simp only [gd, hg, Bool.and_true]
    exact open_two_core (rv c2) (sv c2) (hrv c2) (hsv c2) (h1 c2 hg) (h2 c2 hg) Com1 Pf1 op1 sd1 d1 hc1 hp1 ov1 hov1
      main1 hsd1 Com2 Pf2 op2 sd2 d2 hc2 hp2 ov2 hov2 main2 hsd2 (hvo1 c2) (hvo2 c2) (sop1 c2) (sop2 c2)
      (hsvo1 c2) (hsvo2 c2)
      (fun c1 a b p q w => F c1 c2 a (a + n1 * b) (p, q, w))

end Circuit
