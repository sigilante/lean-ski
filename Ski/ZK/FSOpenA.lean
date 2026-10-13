import Ski.ZK.FSQuery
import Ski.ZK.ROMHide

/-!
# Fiat–Shamir over several rounds, the first commitment hiding up to `η`

`fs_open4` takes every commitment to hide exactly (`ComHides`,
`ComPfHides`).  A Merkle commitment whose leaves may share a hash hides
only up to `η` (`ROMMerkleColl`'s `pfM_hidesC`).  Here the first
commitment hides up to `η` (`ComHidesA`, `ComPfHidesA`) and the bound
gains `η` at each draw of the other salts, the transcript randomness, the
challenges and the tables: `open_real2A`, `open_two_coreA`, `fs_open3UA`,
`fs_open4A`, one direction each.
-/

set_option autoImplicit false
namespace Circuit
open ZKF

/-- **`open_real2` with the commitment hiding up to `η`**: one direction. -/
theorem open_real2A {PV PB D O Pp : Type} {NS NR m η : Nat} (Com : D → Nat → Nat) (Pf : D → Nat → Pp) (op : D → O)
    (sd : O → D) (d0 : D) (hcom : ComHidesA NS η Com) (hpf : ComPfHidesA NS η Com Pf op)
    (ov : TViewN PV PB → Option O) (hovn : ov none = none) (main : (Nat → Tup) → Nat → D)
    (hsd : ∀ t r, op (sd (op (main t r))) = op (main t r))
    (v : Nat → (Nat → Tup) → TViewN PV PB) (hvo : ∀ r t, v r t = none ∨ ov (v r t) = some (op (main t r)))
    (F : Nat → (Nat → Tup) → Nat → Option Pp → TViewN PV PB → Bool) :
    sumTo NS (fun σ => sumTo NR (fun r => sumN m (fun t =>
      indB (F r t (Com (main t r) σ) ((ov (v r t)).map (fun _ => Pf (main t r) σ)) (v r t))))) ≤
    sumTo NS (fun σ => sumTo NR (fun r => sumN m (fun t => indB (openEv Com Pf sd d0 ov (F r t) σ (v r t))))) +
      NR * (Q4 ^ m * η) := by
  have key : ∀ r t, sumTo NS (fun σ => indB (F r t (Com (main t r) σ) ((ov (v r t)).map (fun _ => Pf (main t r) σ))
      (v r t))) ≤ sumTo NS (fun σ => indB (openEv Com Pf sd d0 ov (F r t) σ (v r t))) + η := by
    intro r t
    rcases hvo r t with e | e
    · rw [e]
      unfold openEv
      rw [hovn]
      exact hcom (main t r) d0 (fun mm => F r t mm none none)
    · unfold openEv
      rw [e]
      exact hpf (main t r) (sd (op (main t r))) (hsd t r).symm (fun mm p => F r t mm (some p) (v r t))
  rw [sig_in, sig_in, ← sumN_const m η, ← sumTo_const _ NR, ← sumTo_add]
  refine sumTo_mono _ (fun r _ => ?_)
  refine Nat.le_trans (sumN_mono m (fun t => key r t)) (Nat.le_of_eq ?_)
  exact sm_add (sumN m) (fun N f => (sumTo_sumN m N f).symm) _ _

/-- **`open_two_core` with the first commitment hiding up to `η`**: the
    real count is within `NS1 NS2 (e1 + e2) + Q4² NS2 NR Q4^m η` of the
    simulator's, the second commitment hiding exactly; one direction. -/
theorem open_two_coreA {PV PB D1 O1 P1 D2 O2 P2 : Type} {NR m e1 e2 NS1 NS2 η : Nat}
    (rv sv : EF → EF → Nat → (Nat → Tup) → TViewN PV PB)
    (hrv : ∀ α β r t, rv α β r t = none ∨ ∃ p x y, rv α β r t = some (p, α, β, x, y))
    (hsv : ∀ α β r t, ∃ p x y, sv α β r t = some (p, α, β, x, y))
    (h1 : ∀ E : TViewN PV PB → Bool, tsumN NR m (fun α β r t => indB (genB β && E (rv α β r t))) ≤
      tsumN NR m (fun α β r t => indB (genB β && E (sv α β r t))) + e1 + e2)
    (h2 : ∀ E : TViewN PV PB → Bool, tsumN NR m (fun α β r t => indB (genB β && E (sv α β r t))) ≤
      tsumN NR m (fun α β r t => indB (genB β && E (rv α β r t))) + e1 + e2)
    (Com1 : D1 → Nat → Nat) (Pf1 : D1 → Nat → P1) (op1 : D1 → O1) (sd1 : O1 → D1) (d1 : D1)
    (hc1 : ComHidesA NS1 η Com1) (hp1 : ComPfHidesA NS1 η Com1 Pf1 op1) (ov1 : TViewN PV PB → Option O1)
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
        (sv (efOf (c / Q4)) (efOf (c % Q4)) r t))))))) + NS1 * (NS2 * (e1 + e2)) +
      Q4 * Q4 * (NS2 * (NR * (Q4 ^ m * η))) := by
  have h1' := fun E => Nat.le_trans (h1 E) (Nat.le_of_eq (Nat.add_assoc _ e1 e2))
  have h2' := fun E => Nat.le_trans (h2 E) (Nat.le_of_eq (Nat.add_assoc _ e1 e2))
  let G : Nat → Nat → Nat → TViewN PV PB → Bool := fun σ1 σ2 c w =>
    openEv2 Com1 Pf1 sd1 d1 ov1 Com2 Pf2 sd2 d2 ov2 (F c) σ1 σ2 w
  -- the real side: both commitments swapped, a view event per pair of salts
  have hreal : ∀ c, sumTo NS1 (fun σ1 => sumTo NS2 (fun σ2 => sumTo NR (fun r => sumN m (fun t =>
      indB (genB (efOf (c % Q4)) && F c (Com1 (main1 t r) σ1) (Com2 (main2 c t r) σ2)
        ((ov1 (rv (efOf (c / Q4)) (efOf (c % Q4)) r t)).map (fun _ => Pf1 (main1 t r) σ1))
        ((ov2 (rv (efOf (c / Q4)) (efOf (c % Q4)) r t)).map (fun _ => Pf2 (main2 c t r) σ2))
        (rv (efOf (c / Q4)) (efOf (c % Q4)) r t)))))) ≤
      sumTo NS2 (fun σ2 => sumTo NS1 (fun σ1 => sumTo NR (fun r => sumN m (fun t =>
        indB (genB (efOf (c % Q4)) && G σ1 σ2 c (rv (efOf (c / Q4)) (efOf (c % Q4)) r t)))))) +
        NS2 * (NR * (Q4 ^ m * η)) := fun c => by
    rw [sumTo_congr _ (fun σ1 _ => open_real2 Com2 Pf2 op2 sd2 d2 hc2 hp2 ov2 hov2 (main2 c) (hsd2 c)
      (fun r t => rv (efOf (c / Q4)) (efOf (c % Q4)) r t) (fun r t => hvo2 c r t)
      (fun r t mm2 p2 w => genB (efOf (c % Q4)) && F c (Com1 (main1 t r) σ1) mm2
        ((ov1 w).map (fun _ => Pf1 (main1 t r) σ1)) p2 w))]
    rw [sumTo_exch _ NS2 NS1, ← sumTo_const (NR * (Q4 ^ m * η)) NS2, ← sumTo_add]
    refine sumTo_mono _ (fun σ2 _ => ?_)
    have e := open_real2A (NR := NR) (m := m) Com1 Pf1 op1 sd1 d1 hc1 hp1 ov1 hov1 main1 hsd1
      (fun r t => rv (efOf (c / Q4)) (efOf (c % Q4)) r t) (fun r t => hvo1 c r t)
      (fun _ _ mm1 p1 w => openEv Com2 Pf2 sd2 d2 ov2 (fun mm2 p2 w' => genB (efOf (c % Q4)) && F c mm1 mm2 p1 p2 w')
        σ2 w)
    refine Nat.le_trans (Nat.le_of_eq ?_) (Nat.le_trans e (Nat.le_of_eq (congrArg (· + NR * (Q4 ^ m * η)) ?_)))
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
  refine Nat.le_trans (sumTo_mono _ (fun c _ => hreal c)) ?_
  rw [sumTo_add, sumTo_const, sumTo_congr _ (fun c _ => hsim c), ex rv, ex sv]
  refine Nat.add_le_add_right ?_ _
  calc sumTo NS2 (fun σ2 => sumTo NS1 (fun σ1 => tsumN NR m (fun α β r t =>
        indB (genB β && G σ1 σ2 (efIdx β + Q4 * efIdx α) (rv α β r t)))))
      ≤ sumTo NS2 (fun σ2 => sumTo NS1 (fun σ1 => tsumN NR m (fun α β r t =>
        indB (genB β && G σ1 σ2 (efIdx β + Q4 * efIdx α) (sv α β r t))) + (e1 + e2))) :=
        sumTo_mono _ (fun σ2 _ => sumTo_mono _ (fun σ1 _ => (tsumN_ab rv sv hrv hsv h1' h2' _).1))
    _ = _ := by
      simp only [sumTo_add, sumTo_const, Nat.mul_add]
      ac_rfl

/-- **`fs_open3U` with the first commitment hiding up to `η`**: each
    second and third challenge's bound gains `Q4² NS2 NS3 NR Q4^m η`.
    `fs_open3` unguarded: the guard gone from both counts, the excluded
    draws' public-coin mass in the bound.  `β` fails the verifier's test at
    `P²` of the `Q4` draws (`genB_count`) and the later pair at most `Bz`
    of its `K2 K3` (`hgz`), so the bound gains `(Q4 P² K2 K3 + Q4² Bz)`
    times the randomness count, per table triple.  One proof per oracle,
    one direction. -/
theorem fs_open3UA {PV PB D1 O1 P1 D2 O2 P2 D3 O3 P3 : Type} {NR m e1 e2 NS1 NS2 NS3 K2 K3 n1 n2 n3 η : Nat}
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
    (Com1 : D1 → Nat → Nat) (Pf1 : D1 → Nat → P1) (op1 : D1 → O1) (sd1 : O1 → D1) (d1 : D1)
    (hc1 : ComHidesA NS1 η Com1) (hp1 : ComPfHidesA NS1 η Com1 Pf1 op1) (hr1 : ∀ d σ, Com1 d σ < n1)
    (ov1 : TViewN PV PB → Option O1) (hov1 : ov1 none = none) (main1 : (Nat → Tup) → Nat → D1)
    (hsd1 : ∀ t r, op1 (sd1 (op1 (main1 t r))) = op1 (main1 t r))
    (Com2 : D2 → Nat → Nat) (Pf2 : D2 → Nat → P2) (op2 : D2 → O2) (sd2 : O2 → D2) (d2 : D2)
    (hc2 : ComHides NS2 Com2) (hp2 : ComPfHides NS2 Com2 Pf2 op2) (hr2 : ∀ d σ, Com2 d σ < n2)
    (ov2 : TViewN PV PB → Option O2) (hov2 : ov2 none = none) (main2 : Nat → (Nat → Tup) → Nat → D2)
    (hsd2 : ∀ c t r, op2 (sd2 (op2 (main2 c t r))) = op2 (main2 c t r))
    (Com3 : D3 → Nat → Nat) (Pf3 : D3 → Nat → P3) (op3 : D3 → O3) (sd3 : O3 → D3) (d3 : D3)
    (hc3 : ComHides NS3 Com3) (hp3 : ComPfHides NS3 Com3 Pf3 op3) (hr3 : ∀ d σ, Com3 d σ < n3)
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
    let rvo := fun (c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      ((ov1 (rv c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)).map (fun _ => Pf1 (main1 x.2.2.2 x.2.2.1) x.1),
       (ovPair ov2 ov3 (rv c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)).map
         (fun _ => pfPair NS2 Pf2 Pf3 (main2 c1 x.2.2.2 x.2.2.1, main3 c1 c2 x.2.2.2 x.2.2.1) x.2.1),
       rv c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)
    let s1 := fun (c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) => Com1 (sd1 (sop1 c2 c3 x.2.2.1 x.2.2.2)) x.1
    let s2 := fun (c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      s1 c1 c2 c3 x + n1 * Com2 (sd2 (sop2 c2 c3 c1 x.2.2.1 x.2.2.2)) (x.2.1 % NS2)
    let s3 := fun (c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      s1 c1 c2 c3 x + n1 * comPair NS2 n2 Com2 Com3
        (sd2 (sop2 c2 c3 c1 x.2.2.1 x.2.2.2), sd3 (sop3 c2 c3 c1 x.2.2.1 x.2.2.2)) x.2.1
    let svo := fun (c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      (some (Pf1 (sd1 (sop1 c2 c3 x.2.2.1 x.2.2.2)) x.1),
       some (pfPair NS2 Pf2 Pf3 (sd2 (sop2 c2 c3 c1 x.2.2.1 x.2.2.2), sd3 (sop3 c2 c3 c1 x.2.2.1 x.2.2.2)) x.2.1),
       sv c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)
    let gd := fun (c1 c2 c3 : Nat) => genB (efOf (c1 % Q4)) && gz c2 c3
    (Q4 * Q4) * (K2 * (K3 * sumTo ((Q4 * Q4) ^ n1) (fun H1 => sumTo (K2 ^ (n1 * n2)) (fun H2 =>
      sumTo (K3 ^ (n1 * (n2 * n3))) (fun H3 => sm (fun x =>
      indB (E H1 H2 H3 (m1 x) (m2 (rget (Q4 * Q4) (m1 x) H1) x)
          (m3 (rget (Q4 * Q4) (m1 x) H1) (rget K2 (m2 (rget (Q4 * Q4) (m1 x) H1) x) H2) x)
          (rvo (rget (Q4 * Q4) (m1 x) H1) (rget K2 (m2 (rget (Q4 * Q4) (m1 x) H1) x) H2)
            (rget K3 (m3 (rget (Q4 * Q4) (m1 x) H1) (rget K2 (m2 (rget (Q4 * Q4) (m1 x) H1) x) H2) x) H3) x)))))))) ≤
    sumTo ((Q4 * Q4) ^ n1) (fun H1 => sumTo (K2 ^ (n1 * n2)) (fun H2 => sumTo (K3 ^ (n1 * (n2 * n3))) (fun H3 =>
      sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo K3 (fun c3 => sm (fun x =>
        indB (E (rset (Q4 * Q4) (s1 c1 c2 c3 x) H1 c1) (rset K2 (s2 c1 c2 c3 x) H2 c2)
          (rset K3 (s3 c1 c2 c3 x) H3 c3) (s1 c1 c2 c3 x) (s2 c1 c2 c3 x) (s3 c1 c2 c3 x) (svo c1 c2 c3 x))))))))) +
      (Q4 * Q4) ^ n1 * (K2 ^ (n1 * n2) * (K3 ^ (n1 * (n2 * n3)) *
        (K2 * (K3 * (NS1 * (NS2 * NS3 * (e1 + e2)) + (Q4 * Q4 * (NS2 * NS3 * (NR * (Q4 ^ m * η)))))) +
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
  refine Nat.le_trans (fs_zk3U (K1 := Q4 * Q4) (K2 := K2) (K3 := K3) (n1 := n1) (n2 := n1 * n2) (n3 := n1 * (n2 * n3))
    (ε := K2 * (K3 * (NS1 * (NS2 * NS3 * (e1 + e2)) + (Q4 * Q4 * (NS2 * NS3 * (NR * (Q4 ^ m * η)))))))
    (Nat.mul_pos Q4_pos Q4_pos) hK2 hK3 sm hsm m1 m2 m3 (fun x => hr1 _ _) (fun _ x => pair_lt (hr1 _ _) (hr2 _ _))
    (fun _ _ x => pair_lt (hr1 _ _) (hc23 _ _)) s1 s2 s3 rvo svo gd (fun F => ?_) E) ?_
  rw [sumTo_exch _ K2 (Q4 * Q4), sumTo_exch _ K2 (Q4 * Q4)]
  rw [sumTo_congr _ (fun c2 _ => sumTo_exch _ K3 (Q4 * Q4)), sumTo_congr _ (fun c2 _ => sumTo_exch _ K3 (Q4 * Q4))]
  rw [← sumTo_const (K3 * (NS1 * (NS2 * NS3 * (e1 + e2)) + (Q4 * Q4 * (NS2 * NS3 * (NR * (Q4 ^ m * η)))))) K2, ← sumTo_add]
  refine sumTo_mono _ (fun c2 _ => ?_)
  rw [← sumTo_const (NS1 * (NS2 * NS3 * (e1 + e2)) + (Q4 * Q4 * (NS2 * NS3 * (NR * (Q4 ^ m * η))))) K3, ← sumTo_add]
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
    have core := open_two_coreA (NR := NR) (m := m) (rv c2 c3) (sv c2 c3) (hrv c2 c3) (hsv c2 c3) (h1 c2 c3 hg)
      (h2 c2 c3 hg) Com1 Pf1 op1 sd1 d1 hc1 hp1 ov1 hov1 main1 hsd1
      (comPair NS2 n2 Com2 Com3) (pfPair NS2 Pf2 Pf3) (fun d => (op2 d.1, op3 d.2)) (fun o => (sd2 o.1, sd3 o.2))
      (d2, d3) (ComHides.prod hc2 hc3) (ComPfHides.prod hp2 hp3) (ovPair ov2 ov3) hov23
      (fun c t r => (main2 c t r, main3 c c2 t r))
      (fun c t r => by show (op2 (sd2 (op2 (main2 c t r))), op3 (sd3 (op3 (main3 c c2 t r)))) = _; rw [hsd2, hsd3])
      (hvo1 c2 c3) hvo23 (sop1 c2 c3) (fun c r t => (sop2 c2 c3 c r t, sop3 c2 c3 c r t)) (hsvo1 c2 c3) hsvo23
      (fun c a b p q w => F c c2 c3 a (a + n1 * (b % n2)) (a + n1 * b) (p, q, w))
    simp only [comPair_mod Com3 hr2] at core
    exact Nat.le_trans core (Nat.le_of_eq (Nat.add_assoc _ _ _))
  · refine Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _
      (Nat.add_le_add_left ?_ _)))) _
    have hk : ∀ k, sm (fun _ => k) = NS1 * (NS2 * NS3 * (NR * (Q4 ^ m * 1))) * k := fun k => by
      simp only [sm, sumN_const, sumTo_const, Nat.mul_one, Nat.mul_assoc]
    show sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo K3 (fun c3 =>
      sm (fun _ => indB (!(genB (efOf (c1 % Q4)) && gz c2 c3)))))) ≤ _
    simp only [hk, ← sumTo_mul]
    rw [Nat.mul_comm _ (NS1 * _)]
    exact Nat.mul_le_mul_left _ (bad3_count gz hgz)

/-- **`fs_open4` with the first commitment hiding up to `η`**
    (`fs_open3UA`): `fs_open4`'s four Fiat–Shamir rounds, the query points a
    fourth challenge `c4` hashed into a fourth table; the first commitment
    hides given its openings up to `η` at every `c4`, the others exactly,
    and the error gains `Q4² NS2 NS3 NR Q4^m η` at each draw of the
    challenges and tables.  One direction. -/
theorem fs_open4A {PV PB D1 O1 P1 D2 O2 P2 D3 O3 P3 W : Type} {NR m e1 e2 NS1 NS2 NS3 K2 K3 K4 n1 n2 n3 η : Nat}
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
    (Com1 : D1 → Nat → Nat) (Pf1 : Nat → D1 → Nat → P1) (op1 : Nat → D1 → O1) (sd1 : Nat → O1 → D1) (d1 : D1)
    (hc1 : ComHidesA NS1 η Com1) (hp1 : ∀ c4, ComPfHidesA NS1 η Com1 (Pf1 c4) (op1 c4)) (hr1 : ∀ d σ, Com1 d σ < n1)
    (ov1 : Nat → TViewN PV PB → Option O1) (hov1 : ∀ c4, ov1 c4 none = none) (main1 : (Nat → Tup) → Nat → D1)
    (hsd1 : ∀ c4 t r, op1 c4 (sd1 c4 (op1 c4 (main1 t r))) = op1 c4 (main1 t r))
    (Com2 : D2 → Nat → Nat) (Pf2 : Nat → D2 → Nat → P2) (op2 : Nat → D2 → O2) (sd2 : Nat → O2 → D2) (d2 : D2)
    (hc2 : ComHides NS2 Com2) (hp2 : ∀ c4, ComPfHides NS2 Com2 (Pf2 c4) (op2 c4)) (hr2 : ∀ d σ, Com2 d σ < n2)
    (ov2 : Nat → TViewN PV PB → Option O2) (hov2 : ∀ c4, ov2 c4 none = none) (main2 : Nat → (Nat → Tup) → Nat → D2)
    (hsd2 : ∀ c4 c t r, op2 c4 (sd2 c4 (op2 c4 (main2 c t r))) = op2 c4 (main2 c t r))
    (Com3 : D3 → Nat → Nat) (Pf3 : Nat → D3 → Nat → P3) (op3 : Nat → D3 → O3) (sd3 : Nat → O3 → D3) (d3 : D3)
    (hc3 : ComHides NS3 Com3) (hp3 : ∀ c4, ComPfHides NS3 Com3 (Pf3 c4) (op3 c4)) (hr3 : ∀ d σ, Com3 d σ < n3)
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
    let rvo := fun (c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      ((ov1 c4 (rv c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)).map (fun _ => Pf1 c4 (main1 x.2.2.2 x.2.2.1) x.1),
       (ovPair (ov2 c4) (ov3 c4) (rv c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)).map
         (fun _ => pfPair NS2 (Pf2 c4) (Pf3 c4) (main2 c1 x.2.2.2 x.2.2.1, main3 c1 c2 x.2.2.2 x.2.2.1) x.2.1),
       rv c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)
    let s1 := fun (c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) => Com1 (sd1 c4 (sop1 c4 c2 c3 x.2.2.1 x.2.2.2)) x.1
    let s2 := fun (c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      s1 c4 c1 c2 c3 x + n1 * Com2 (sd2 c4 (sop2 c4 c2 c3 c1 x.2.2.1 x.2.2.2)) (x.2.1 % NS2)
    let s3 := fun (c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      s1 c4 c1 c2 c3 x + n1 * comPair NS2 n2 Com2 Com3
        (sd2 c4 (sop2 c4 c2 c3 c1 x.2.2.1 x.2.2.2), sd3 c4 (sop3 c4 c2 c3 c1 x.2.2.1 x.2.2.2)) x.2.1
    let svo := fun (c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      (some (Pf1 c4 (sd1 c4 (sop1 c4 c2 c3 x.2.2.1 x.2.2.2)) x.1),
       some (pfPair NS2 (Pf2 c4) (Pf3 c4) (sd2 c4 (sop2 c4 c2 c3 c1 x.2.2.1 x.2.2.2), sd3 c4 (sop3 c4 c2 c3 c1 x.2.2.1 x.2.2.2)) x.2.1),
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
        (rvo (rget K4 (Mq y) H4) (r1 y) (r2 y) (r3 y) y.2.2.2))))) ≤
    sumTo (K4 ^ N4) (fun H4 => sumTo K4 (fun c4 =>
      sumTo ((Q4 * Q4) ^ n1) (fun H1 => sumTo (K2 ^ (n1 * n2)) (fun H2 => sumTo (K3 ^ (n1 * (n2 * n3))) (fun H3 =>
      sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo K3 (fun c3 => sm (fun x =>
        indB (E (rset (Q4 * Q4) (s1 c4 c1 c2 c3 x) H1 c1) (rset K2 (s2 c4 c1 c2 c3 x) H2 c2)
          (rset K3 (s3 c4 c1 c2 c3 x) H3 c3) (rset K4 (φ (s3 c4 c1 c2 c3 x) (oz (sv c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2))) H4 c4)
          (s1 c4 c1 c2 c3 x) (s2 c4 c1 c2 c3 x) (s3 c4 c1 c2 c3 x) (svo c4 c1 c2 c3 x))))))))))) +
      K4 ^ N4 * (K4 * ((Q4 * Q4) ^ n1 * (K2 ^ (n1 * n2) * (K3 ^ (n1 * (n2 * n3)) *
        (K2 * (K3 * (NS1 * (NS2 * NS3 * (e1 + e2)) + (Q4 * Q4 * (NS2 * NS3 * (NR * (Q4 ^ m * η)))))) +
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
  refine fs_lastG (K := Q4 * Q4 * (K2 * K3)) (n4 := N4) hK4 sm4 hsm4 Mq
    (fun y => hφ _ _)
    (fun c4 y => (y.1, y.2.1, y.2.2.1, m1 y.2.2.2, m2 (r1 y) y.2.2.2, m3 (r1 y) (r2 y) y.2.2.2, rvo c4 (r1 y) (r2 y) (r3 y) y.2.2.2))
    (fun c4 G => sumTo ((Q4 * Q4) ^ n1) (fun H1 => sumTo (K2 ^ (n1 * n2)) (fun H2 => sumTo (K3 ^ (n1 * (n2 * n3)))
      (fun H3 => sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo K3 (fun c3 => sm (fun x =>
        indB (G (φ (s3 c4 c1 c2 c3 x) (oz (sv c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2))) (rset (Q4 * Q4) (s1 c4 c1 c2 c3 x) H1 c1, rset K2 (s2 c4 c1 c2 c3 x) H2 c2,
          rset K3 (s3 c4 c1 c2 c3 x) H3 c3, s1 c4 c1 c2 c3 x, s2 c4 c1 c2 c3 x, s3 c4 c1 c2 c3 x, svo c4 c1 c2 c3 x))))))))))
    g4 hB4 (fun c4 hg4 G => ?_) (fun H4 _ c4 v => E v.1 v.2.1 v.2.2.1 H4 v.2.2.2.1 v.2.2.2.2.1 v.2.2.2.2.2.1 v.2.2.2.2.2.2)
  have h3 := fs_open3UA hK2 hK3 (rv c4) (sv c4) gz hgz (hrv c4) (hsv c4) (fun c2 c3 hg => h1 c4 c2 c3 hg4 hg) (fun c2 c3 hg => h2 c4 c2 c3 hg4 hg)
    Com1 (Pf1 c4) (op1 c4) (sd1 c4) d1 hc1 (hp1 c4) hr1 (ov1 c4) (hov1 c4) main1 (hsd1 c4)
    Com2 (Pf2 c4) (op2 c4) (sd2 c4) d2 hc2 (hp2 c4) hr2 (ov2 c4) (hov2 c4) main2 (hsd2 c4)
    Com3 (Pf3 c4) (op3 c4) (sd3 c4) d3 hc3 (hp3 c4) hr3 (ov3 c4) (hov3 c4) main3 (hsd3 c4)
    (hvo1 c4) (hvo2 c4) (hvo3 c4) (sop1 c4) (sop2 c4) (sop3 c4) (hsvo1 c4) (hsvo2 c4) (hsvo3 c4)
    (fun H1 H2 H3 a b c v => G (φ c (oz v.2.2)) (H1, H2, H3, a, b, c, v))
  simp only [Mq, ← hoz c4]
  rw [Nat.mul_assoc, Nat.mul_assoc K2]
  exact h3

end Circuit
