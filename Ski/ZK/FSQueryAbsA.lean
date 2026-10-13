import Ski.ZK.FSQueryA
import Ski.ZK.FSQueryAbs

/-!
# The four-round bounds as `ZKB`s, the first commitment hiding up to `η`

`fs_open4_abs` and its circuit instances with the first commitment hiding
up to `η` (`FSOpenA`'s `fs_open4A`): `fs_open4_absA`, `sud_fs_open4_absA`,
`wit_fs_open4_absA`, `comp_fs_open4_absA`; on each circuit's data, whose
error gains the `η` term (`sudFS4A`, `witFS4A`, `compFS4A`): `sud_fs4A`,
`wit_fs4A`, `comp_fs4A`; `n` statements of each (`fs4_powD`):
`sud_fs_open4_powDA`, `wit_fs_open4_powDA`, `comp_fs_open4_powDA`.  One
direction each.
-/

set_option autoImplicit false

namespace Circuit
open ZKF

/-- **`fs_open4_abs` with the first commitment hiding up to `η`**
    (`fs_open4A`): its first bound as a `ZKB` over the four tables, the error
    gaining `Q4² NS2 NS3 NR Q4^m η` at each draw of the challenges and
    tables.  One direction. -/
theorem fs_open4_absA {PV PB D1 O1 P1 D2 O2 P2 D3 O3 P3 W : Type} {NR m e1 e2 NS1 NS2 NS3 K2 K3 K4 n1 n2 n3 η : Nat}
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
    (hsvo3 : ∀ c4 c2 c3 c r t, ov3 c4 (sv c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (sop3 c4 c2 c3 c r t)) :
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
    let ST := fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo (K4 ^ N4) (fun H4 => sumTo ((Q4 * Q4) ^ n1) (fun H1 =>
      sumTo (K2 ^ (n1 * n2)) (fun H2 => sumTo (K3 ^ (n1 * (n2 * n3))) (fun H3 => f (H1, H2, H3, H4)))))
    let SC := fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo K4 (fun c4 => sumTo (Q4 * Q4) (fun c1 =>
      sumTo K2 (fun c2 => sumTo K3 (fun c3 => f (c1, c2, c3, c4)))))
    let rvT := fun (H : Nat × Nat × Nat × Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      (m1 x, m2 (r1 (H.1, H.2.1, H.2.2.1, x)) x, m3 (r1 (H.1, H.2.1, H.2.2.1, x)) (r2 (H.1, H.2.1, H.2.2.1, x)) x,
       rvo (rget K4 (Mq (H.1, H.2.1, H.2.2.1, x)) H.2.2.2) (r1 (H.1, H.2.1, H.2.2.1, x)) (r2 (H.1, H.2.1, H.2.2.1, x))
         (r3 (H.1, H.2.1, H.2.2.1, x)) x)
    let pgT := fun (H : Nat × Nat × Nat × Nat) (c : Nat × Nat × Nat × Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      (rset (Q4 * Q4) (s1 c.2.2.2 c.1 c.2.1 c.2.2.1 x) H.1 c.1, rset K2 (s2 c.2.2.2 c.1 c.2.1 c.2.2.1 x) H.2.1 c.2.1,
       rset K3 (s3 c.2.2.2 c.1 c.2.1 c.2.2.1 x) H.2.2.1 c.2.2.1,
       rset K4 (φ (s3 c.2.2.2 c.1 c.2.1 c.2.2.1 x) (oz (sv c.2.2.2 c.2.1 c.2.2.1 (efOf (c.1 / Q4)) (efOf (c.1 % Q4))
         x.2.2.1 x.2.2.2))) H.2.2.2 c.2.2.2)
    let svT := fun (c : Nat × Nat × Nat × Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      (s1 c.2.2.2 c.1 c.2.1 c.2.2.1 x, s2 c.2.2.2 c.1 c.2.1 c.2.2.1 x, s3 c.2.2.2 c.1 c.2.1 c.2.2.1 x,
       svo c.2.2.2 c.1 c.2.1 c.2.2.1 x)
    ∀ E : Nat × Nat × Nat × Nat → Nat × Nat × Nat × (Option P1 × Option (P2 × P3) × TViewN PV PB) → Bool,
    K4 * (Q4 * Q4 * (K2 * K3)) * ST (fun H => sm (fun x => indB (E H (rvT H x)))) ≤
    ST (fun H => SC (fun c => sm (fun x => indB (E (pgT H c x) (svT c x))))) +
      K4 ^ N4 * (K4 * ((Q4 * Q4) ^ n1 * (K2 ^ (n1 * n2) * (K3 ^ (n1 * (n2 * n3)) *
        (K2 * (K3 * (NS1 * (NS2 * NS3 * (e1 + e2)) + Q4 * Q4 * (NS2 * NS3 * (NR * (Q4 ^ m * η))))) +
          (Q4 * (P * P) * (K2 * K3) + Q4 * Q4 * Bz) * (NS1 * (NS2 * NS3 * (NR * (Q4 ^ m * 1)))))))) +
          B4 * (Q4 * Q4 * (K2 * K3) * sm4 (fun _ => 1))) := by
  intro sm m1 m2 m3 rvo s1 s2 s3 svo sm4 r1 r2 r3 Mq ST SC rvT pgT svT E
  have h := fs_open4A hK2 hK3 hK4 φ hφ rv sv gz hgz g4 hB4 hrv hsv oz hoz h1 h2 Com1 Pf1 op1 sd1 d1 hc1 hp1 hr1 ov1 hov1 main1 hsd1 Com2 Pf2 op2 sd2 d2 hc2 hp2 hr2 ov2 hov2 main2 hsd2 Com3 Pf3 op3 sd3 d3 hc3 hp3 hr3 ov3 hov3 main3 hsd3 hvo1 hvo2 hvo3 sop1 sop2 sop3 hsvo1 hsvo2 hsvo3 (fun H1 H2 H3 H4 a b c v => E (H1, H2, H3, H4) (a, b, c, v))
  rw [Nat.mul_assoc]
  refine Nat.le_trans h (Nat.add_le_add_right (Nat.le_of_eq ?_) _)
  refine sumTo_congr _ (fun H4 _ => ?_)
  rw [sumTo_exch _ ((Q4 * Q4) ^ n1) K4]
  refine sumTo_congr _ (fun H1 _ => ?_)
  rw [sumTo_exch _ (K2 ^ (n1 * n2)) K4]
  refine sumTo_congr _ (fun H2 _ => ?_)
  rw [sumTo_exch _ (K3 ^ (n1 * (n2 * n3))) K4]

section
open B Air Stmt Mach Sudoku SudokuText Compose CompM Wit

set_option maxRecDepth 100000 in
/-- **`sud_fs_open4_abs` with the first commitment hiding up to `η`**
    (`fs_open4_absA`).  One direction. -/
theorem sud_fs_open4_absA {V Wv P1 P2 P3 : Type} (off : EF → String → EF) {puzzle : List Nat} (hc : CluesOK (cluesOf puzzle))
    {ρ : Nat → Bool} {A : List Cell} {k : Nat} {row : Nat → Air.Row}
    (hA : AcceptsFrom A (stmtMachine ρ 729 (sudokuExpr (cluesOf puzzle)) ACC REJ) k row)
    (hacc : rd A (row (k - 1)).ctr (row (k - 1)).hd = some (.atom ACC))
    (hlen : A.length = 2 ^ 16) (hk : k ≤ 2 ^ 16)
    {tP : Nat} (htp : tP = progTp (stmtMachine (fun _ => false) 729 (sudokuExpr (cluesOf puzzle)) ACC REJ).heap)
    (S16 S10 SP : Nat → List F) (qv : EF → EF → List EF → F → List F → List F → List EF)
    (wm wc ww wp : Nat → List (EF → EF → List F)) {Lwm Lwc Lww Lwp : Nat} (hlwm : ∀ c, (wm c).length = Lwm)
    (hlwc : ∀ c, (wc c).length = Lwc) (hlww : ∀ c, (ww c).length = Lww) (hlwp : ∀ c, (wp c).length = Lwp)
    {K2 K4 : Nat} (hK2 : 0 < K2) (hK4 : 0 < K4)
    (φ : Nat → Option (List (List (List EF)) × List (List (List (List EF))) × List (List (List EF))) → Nat) {N4 : Nat} (hφ : ∀ m w, φ m w < N4)
    (hS16 : ∀ c4, ∀ x ∈ S16 c4, x ∉ cosetL 1 (bbGen 16) (2 ^ 16)) (hS10 : ∀ c4, ∀ x ∈ S10 c4, x ∉ cosetL 1 (bbGen 10) (2 ^ 10))
    (hSP : ∀ c4, ∀ x ∈ SP c4, x ∉ cosetL 1 (bbGen (tP + 1)) (2 ^ (tP + 1)))
    (hsz16 : ∀ c4, 2 * (S16 c4).length + 8 ≤ 2 ^ 16) (hsz : ∀ c4, 2 * (S10 c4).length + 8 ≤ 2 ^ 10)
    (hszP : ∀ c4, 2 * (SP c4).length + 8 ≤ 2 ^ (tP + 1)) {ncw : Nat} (αd : Nat → EF) {B4 : Nat}
    (hB4 : sumTo K4 (fun c4 => indB (!genB (αd c4))) ≤ B4) (fri : Nat → EF → EF → List (EF → EF) → V)
    (hncw : 4 ≤ ncw)
    (NR2 : Nat) (Rb : Nat → EF → EF → Nat → List (EF → EF)) (Ro : Nat → EF → EF → Nat → Wv)
    {NS1 NS2 NS3 n1 n2 n3 : Nat}
    (Com1 : List (List (List F)) → Nat → Nat) (Pf1 : Nat → List (List (List F)) → Nat → P1) {η : Nat} (hc1 : ComHidesA NS1 η Com1)
    (hp1 : ∀ c4, ComPfHidesA NS1 η Com1 (Pf1 c4) (opF ((sudGroups tP (S16 c4) (S10 c4) (SP c4) EF.zero qv).map (·.base.S)) [0, 2, 4, 6]))
    (hr1 : ∀ d σ, Com1 d σ < n1) (d1 : List (List (List F)))
    (Com2 : List (List (List F)) → Nat → Nat) (Pf2 : Nat → List (List (List F)) → Nat → P2) (hc2 : ComHides NS2 Com2)
    (hp2 : ∀ c4, ComPfHides NS2 Com2 (Pf2 c4) (opF ((sudGroups tP (S16 c4) (S10 c4) (SP c4) EF.zero qv).map (·.base.S)) [1, 3, 5, 7]))
    (hr2 : ∀ d σ, Com2 d σ < n2) (d2 : List (List (List F)))
    (Com3 : List (List (List (List F))) × List (List (List F)) → Nat → Nat)
    (Pf3 : Nat → List (List (List (List F))) × List (List (List F)) → Nat → P3) (hc3 : ComHides NS3 Com3)
    (hp3 : ∀ c4, ComPfHides NS3 Com3 (Pf3 c4) (fun d => (opQ (sudSsT (S16 c4) (S10 c4) (SP c4)) d.1, opCw (sudSsC tP (S16 c4) (S10 c4) (SP c4)) d.2)))
    (hr3 : ∀ d σ, Com3 d σ < n3) (d3 : List (List (List (List F))) × List (List (List F))) :
    let blank := stmtMachine (fun _ => false) 729 (sudokuExpr (cluesOf puzzle)) ACC REJ
    let C := cpuTableW A row k (2 ^ 16)
    let Pg := progTableS blank.heap
    let Wt := witTableS A
    let Mm := memTableC A (cpuAirS blank.hd blank.stk blank.heap.length ACC) (progAirS blank.heap) witAirS C Pg Wt
    let NR0 := sudNR off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt tP (S16 0) (S10 0) (SP 0) EF.zero qv (wm 0) (wc 0) (ww 0) (wp 0) ncw
    let pcsZ := fun (c4 c2 : Nat) (ζ : EF) t α β r => sudPcs off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt tP (S16 c4) (S10 c4) (SP c4) ζ qv (wm c2) (wc c2) (ww c2) (wp c2) ncw (αd c4)
      (friX (fri c4) (Rb c4) (Ro c4) (r / NR0)) t α β (r % NR0)
    let psimZ := fun (c4 c2 : Nat) (ζ : EF) α β v r => sudPsim off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt tP (S16 c4) (S10 c4) (SP c4) ζ qv (wm c2) (wc c2) (ww c2) (wp c2) ncw (αd c4)
      (friX (fri c4) (Rb c4) (Ro c4) (r / NR0)) α β v (r % NR0)
    let NR := NR0 * NR2
    let tabs := fun t : Nat → Tup => sudTables blank.hd blank.stk blank.heap.length blank.heap
      ((C.setBlind BLA (t 1)).setBlind BLB (t 0)) (Mm.setBlind 5 (t 0)) (progTableS blank.heap) (Wt.setBlind 1 (t 1))
    let tv := fun pre β t => sudViewN pre β blank.hd blank.stk blank.heap.length C Mm Wt t
    let tp := fun pre β => terminal pre β (progAirS blank.heap) (progTableS blank.heap)
    let M := (allEntries (sudTables blank.hd blank.stk blank.heap.length blank.heap C Mm (progTableS blank.heap) Wt)).length
    let q0 := sudGroups tP (S16 0) (S10 0) (SP 0) EF.zero qv
    let qZ := fun (c4 : Nat) (ζ : EF) => sudGroups tP (S16 c4) (S10 c4) (SP c4) ζ qv
    let Ss := fun c4 => (qZ c4 EF.zero).map (·.base.S)
    let ks := sudKs blank.hd blank.stk blank.heap.length blank.heap
    let cols := sudCols off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt
    let tqZ := fun (c4 c2 : Nat) (ζ : EF) => (sudTs off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt tP (S16 c4) (S10 c4) (SP c4) ζ qv (wm c2) (wc c2) (ww c2) (wp c2)).map Prod.fst
    let qdZ := fun (c4 c2 : Nat) (ζ : EF) (t : Nat → Tup) (α β : EF) (ms : List F) =>
      (sudTs off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt tP (S16 c4) (S10 c4) (SP c4) ζ qv (wm c2) (wc c2) (ww c2) (wp c2)).map (fun p => p.2 t α β ms)
    let SsT := fun c4 => (tqZ c4 0 EF.zero).map (·.S)
    let SsC := fun c4 => (tabsInfo ncw (tqZ c4 0 EF.zero)).map (·.S)
    let mk1 := [0, 2, 4, 6]
    let mk2 := [1, 3, 5, 7]
    let main1 := fun (t : Nat → Tup) (r : Nat) => mainF2 q0 ks cols (tqZ 0 0 EF.zero) ncw mk1 t (r % NR0)
    let main2 := fun (c1 : Nat) (t : Nat → Tup) (r : Nat) =>
      mainP2 q0 ks cols (tqZ 0 0 EF.zero) ncw mk2 t (efOf (c1 / Q4)) (efOf (c1 % Q4)) (r % NR0)
    let main3 := fun (c1 c2 : Nat) (t : Nat → Tup) (r : Nat) =>
      (tabsPolys (tqZ 0 c2 EF.zero) (qdZ 0 c2 EF.zero t (efOf (c1 / Q4)) (efOf (c1 % Q4))
          (msF q0 ks (tqZ 0 c2 EF.zero) ncw (r % NR0))) (crF q0 ks (tqZ 0 c2 EF.zero) ncw (r % NR0)),
       tabsCws ncw (tqZ 0 c2 EF.zero) (ccF q0 ks (tqZ 0 c2 EF.zero) ncw (r % NR0)))
    let vS := fun (α β : EF) (t : Nat → Tup) => viewT β (fun k => prefixOf α (off β) (chainBus k)) (fun _ => false)
      chainPar 3 (xrefN (tp (prefixOf α (off β)) β)) t
    let sop1 := fun (c4 c2 c3 r : Nat) (_ : Nat → Tup) =>
      opF (Ss c4) mk1 (mainZ2 (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw mk1 (r % NR0))
    let sop2 := fun (c4 c2 c3 _ r : Nat) (_ : Nat → Tup) =>
      opF (Ss c4) mk2 (mainZ2 (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw mk2 (r % NR0))
    let sop3 := fun (c4 c2 c3 c1 r : Nat) (t : Nat → Tup) =>
      (opQ (SsT c4) (tabsPolys (tqZ c4 c2 (efOf c3)) (canonT (tqZ c4 c2 (efOf c3)) (efOf (c1 / Q4)) (efOf (c1 % Q4))
         (vS (efOf (c1 / Q4)) (efOf (c1 % Q4)) t)
         (openMulti ((qZ c4 (efOf c3)).map QGroup.ext) ((((qZ c4 (efOf c3)).map QGroup.ext).zip ks).map
           (fun p => List.replicate p.2 (List.replicate p.1.n (0 : F))))
           (msF (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw (r % NR0))))
         (crF (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw (r % NR0))),
       opCw (SsC c4) (tabsCws ncw (tqZ c4 c2 (efOf c3)) (ccF (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw (r % NR0))))
    let ov1 : Nat → TViewN (SudPV (V × Wv)) EF → Option (List (List (List F))) := fun c4 v => match v with
      | some (pv, _) => some (ovF2 (Ss c4) mk1 pv)
      | none => none
    let ov2 : Nat → TViewN (SudPV (V × Wv)) EF → Option (List (List (List F))) := fun c4 v => match v with
      | some (pv, _) => some (ovF2 (Ss c4) mk2 pv)
      | none => none
    let ov3 : Nat → TViewN (SudPV (V × Wv)) EF → Option (List (List (List (List F))) × List (List (List F))) :=
      fun _ v => match v with
      | some (pv, _) => some (ovQ pv, cwQ 8 pv)
      | none => none
    let rvF := fun (c4 c2 c3 : Nat) (α β : EF) (r : Nat) (t : Nat → Tup) =>
      realVN off tabs tv tp (pcsZ c4 c2 (efOf c3)) α β r t
    let svF := fun (c4 c2 c3 : Nat) (α β : EF) (r : Nat) (t : Nat → Tup) =>
      simVN off tp chainBus (fun _ => false) chainPar 3 tp (psimZ c4 c2 (efOf c3)) α β r t
    let ozF : TViewN (SudPV (V × Wv)) EF → Option (List (List (List EF)) × List (List (List (List EF))) × List (List (List EF))) := fun v => match v with
      | some (pv, _) => some (pv.1.1.map (fun g => g.1.map Prod.snd), pv.1.2.map (List.map (List.map Prod.snd)),
        pv.2.1.map (List.map Prod.snd))
      | none => none
    let op3 := fun (c4 : Nat) (d : List (List (List (List F))) × List (List (List F))) =>
      (opQ (SsT c4) d.1, opCw (SsC c4) d.2)
    let sd3 := fun (c4 : Nat) (o : List (List (List (List F))) × List (List (List F))) =>
      (sdQ (SsT c4) o.1, sdCw (SsC c4) o.2)
    let sm := fun (g : Nat × Nat × Nat × (Nat → Tup) → Nat) =>
      sumTo NS1 (fun σ1 => sumTo (NS2 * NS3) (fun σ => sumTo NR (fun r => sumN 2 (fun t => g (σ1, σ, r, t)))))
    let m1 := fun (x : Nat × Nat × Nat × (Nat → Tup)) => Com1 (main1 x.2.2.2 x.2.2.1) x.1
    let m2 := fun (c1 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      m1 x + n1 * Com2 (main2 c1 x.2.2.2 x.2.2.1) (x.2.1 % NS2)
    let m3 := fun (c1 c2 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      m1 x + n1 * comPair NS2 n2 Com2 Com3 (main2 c1 x.2.2.2 x.2.2.1, main3 c1 c2 x.2.2.2 x.2.2.1) x.2.1
    let rvo := fun (c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      ((ov1 c4 (rvF c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)).map (fun _ => Pf1 c4 (main1 x.2.2.2 x.2.2.1) x.1),
       (ovPair (ov2 c4) (ov3 c4) (rvF c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)).map
         (fun _ => pfPair NS2 (Pf2 c4) (Pf3 c4) (main2 c1 x.2.2.2 x.2.2.1, main3 c1 c2 x.2.2.2 x.2.2.1) x.2.1),
       rvF c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)
    let s1 := fun (c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) => Com1 (sdF (Ss c4) mk1 (sop1 c4 c2 c3 x.2.2.1 x.2.2.2)) x.1
    let s2 := fun (c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      s1 c4 c1 c2 c3 x + n1 * Com2 (sdF (Ss c4) mk2 (sop2 c4 c2 c3 c1 x.2.2.1 x.2.2.2)) (x.2.1 % NS2)
    let s3 := fun (c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      s1 c4 c1 c2 c3 x + n1 * comPair NS2 n2 Com2 Com3
        (sdF (Ss c4) mk2 (sop2 c4 c2 c3 c1 x.2.2.1 x.2.2.2), sd3 c4 (sop3 c4 c2 c3 c1 x.2.2.1 x.2.2.2)) x.2.1
    let svo := fun (c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      (some (Pf1 c4 (sdF (Ss c4) mk1 (sop1 c4 c2 c3 x.2.2.1 x.2.2.2)) x.1),
       some (pfPair NS2 (Pf2 c4) (Pf3 c4) (sdF (Ss c4) mk2 (sop2 c4 c2 c3 c1 x.2.2.1 x.2.2.2), sd3 c4 (sop3 c4 c2 c3 c1 x.2.2.1 x.2.2.2)) x.2.1),
       svF c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)
    let sm4 := fun (g : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup)) → Nat) =>
      sumTo ((Q4 * Q4) ^ n1) (fun H1 => sumTo (K2 ^ (n1 * n2)) (fun H2 =>
        sumTo (Q4 ^ (n1 * (n2 * n3))) (fun H3 => sm (fun x => g (H1, H2, H3, x)))))
    let r1 := fun (y : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup))) => rget (Q4 * Q4) (m1 y.2.2.2) y.1
    let r2 := fun (y : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup))) => rget K2 (m2 (r1 y) y.2.2.2) y.2.1
    let r3 := fun (y : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup))) => rget Q4 (m3 (r1 y) (r2 y) y.2.2.2) y.2.2.1
    let Mq := fun (y : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup))) => φ (m3 (r1 y) (r2 y) y.2.2.2)
      (ozF (rvF 0 (r2 y) (r3 y) (efOf (r1 y / Q4)) (efOf (r1 y % Q4)) y.2.2.2.2.2.1 y.2.2.2.2.2.2))
    let ST := fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo (K4 ^ N4) (fun H4 => sumTo ((Q4 * Q4) ^ n1) (fun H1 =>
      sumTo (K2 ^ (n1 * n2)) (fun H2 => sumTo (Q4 ^ (n1 * (n2 * n3))) (fun H3 => f (H1, H2, H3, H4)))))
    let SC := fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo K4 (fun c4 => sumTo (Q4 * Q4) (fun c1 =>
      sumTo K2 (fun c2 => sumTo Q4 (fun c3 => f (c1, c2, c3, c4)))))
    let rvT := fun (H : Nat × Nat × Nat × Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      (m1 x, m2 (r1 (H.1, H.2.1, H.2.2.1, x)) x, m3 (r1 (H.1, H.2.1, H.2.2.1, x)) (r2 (H.1, H.2.1, H.2.2.1, x)) x,
       rvo (rget K4 (Mq (H.1, H.2.1, H.2.2.1, x)) H.2.2.2) (r1 (H.1, H.2.1, H.2.2.1, x)) (r2 (H.1, H.2.1, H.2.2.1, x))
         (r3 (H.1, H.2.1, H.2.2.1, x)) x)
    let pgT := fun (H : Nat × Nat × Nat × Nat) (c : Nat × Nat × Nat × Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      (rset (Q4 * Q4) (s1 c.2.2.2 c.1 c.2.1 c.2.2.1 x) H.1 c.1, rset K2 (s2 c.2.2.2 c.1 c.2.1 c.2.2.1 x) H.2.1 c.2.1,
       rset Q4 (s3 c.2.2.2 c.1 c.2.1 c.2.2.1 x) H.2.2.1 c.2.2.1,
       rset K4 (φ (s3 c.2.2.2 c.1 c.2.1 c.2.2.1 x) (ozF (svF c.2.2.2 c.2.1 c.2.2.1 (efOf (c.1 / Q4)) (efOf (c.1 % Q4))
         x.2.2.1 x.2.2.2))) H.2.2.2 c.2.2.2)
    let svT := fun (c : Nat × Nat × Nat × Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      (s1 c.2.2.2 c.1 c.2.1 c.2.2.1 x, s2 c.2.2.2 c.1 c.2.1 c.2.2.1 x, s3 c.2.2.2 c.1 c.2.1 c.2.2.1 x,
       svo c.2.2.2 c.1 c.2.1 c.2.2.1 x)
    ∀ E : Nat × Nat × Nat × Nat → Nat × Nat × Nat × (Option P1 × Option (P2 × P3) × TViewN (SudPV (V × Wv)) EF) → Bool,
    K4 * (Q4 * Q4 * (K2 * Q4)) * ST (fun H => sm (fun x => indB (E H (rvT H x)))) ≤
      ST (fun H => SC (fun c => sm (fun x => indB (E (pgT H c x) (svT c x))))) +
      (K4 ^ N4 * (K4 * ((Q4 * Q4) ^ n1 * (K2 ^ (n1 * n2) * (Q4 ^ (n1 * (n2 * n3)) *
          (K2 * (Q4 * (NS1 * (NS2 * NS3 * (Q4 * (NR * (Q4 ^ 2 * M)) + Q4 * (Q4 * (Q4 ^ 2 * 0)))) +
            Q4 * Q4 * (NS2 * NS3 * (NR * (Q4 ^ 2 * η))))) +
            (Q4 * (P * P) * (K2 * Q4) + Q4 * Q4 * (K2 * (P * P))) * (NS1 * (NS2 * NS3 * (NR * (Q4 ^ 2 * 1)))))))) +
            B4 * (Q4 * Q4 * (K2 * Q4) * sm4 (fun _ => 1)))) := by
  intro blank C Pg Wt Mm NR0 pcsZ psimZ NR tabs tv tp M q0 qZ Ss ks cols tqZ qdZ SsT SsC mk1 mk2 main1 main2 main3 vS sop1 sop2 sop3 ov1 ov2 ov3 rvF svF ozF op3 sd3
  obtain ⟨hbal, hun⟩ := sud_honest_zk hc hA hlen hk
  obtain ⟨sc, sms, sw⟩ := sud_run_sats hc hA hacc hlen hk
  obtain ⟨hP23, hPg⟩ := sud_prog_height hc hA hlen
  rw [← htp] at hP23 hPg
  have hSw := fun (c4 c2 c3 : Nat) => sud_same_w off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt tP (S16 c4) (S10 c4) (SP c4) (efOf c3) EF.zero qv (wm c2) (wc c2) (ww c2) (wp c2) (wm 0) (wc 0) (ww 0) (wp 0) ncw (by rw [hlwm, hlwm]) (by rw [hlwc, hlwc]) (by rw [hlww, hlww]) (by rw [hlwp, hlwp])
  have hSz := fun (c4 c2 c3 : Nat) => sud_same_w off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt tP (S16 c4) (S10 c4) (SP c4) (efOf c3) EF.zero qv (wm c2) (wc c2) (ww c2) (wp c2) (wm c2) (wc c2) (ww c2) (wp c2) ncw rfl rfl rfl rfl
  have hS0 := fun (c4 c2 : Nat) => sud_same_w off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt tP (S16 c4) (S10 c4) (SP c4) EF.zero EF.zero qv (wm c2) (wc c2) (ww c2) (wp c2) (wm 0) (wc 0) (ww 0) (wp 0) ncw (by rw [hlwm, hlwm]) (by rw [hlwc, hlwc]) (by rw [hlww, hlww]) (by rw [hlwp, hlwp])
  have hSd := fun (c4 c2 c3 : Nat) => sud_same_d off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt tP (S16 c4) (S10 c4) (SP c4) (S16 0) (S10 0) (SP 0) (efOf c3) EF.zero qv (wm c2) (wc c2) (ww c2) (wp c2) (wm 0) (wc 0) (ww 0) (wp 0) (by rw [hlwm, hlwm]) (by rw [hlwc, hlwc]) (by rw [hlww, hlww]) (by rw [hlwp, hlwp])
  have hSdz := fun (c4 c2 c3 : Nat) => sud_same_d off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt tP (S16 c4) (S10 c4) (SP c4) (S16 0) (S10 0) (SP 0) (efOf c3) EF.zero qv (wm c2) (wc c2) (ww c2) (wp c2) (wm c2) (wc c2) (ww c2) (wp c2) rfl rfl rfl rfl
  have hb : ∀ c4 c2 c3, genB (αd c4) = true → genB (efOf c3) = true →
      (∀ E' : TViewN (SudPV (V × Wv)) EF → Bool,
        tsumN NR 2 (fun α β r t => indB (genB β && E' (rvF c4 c2 c3 α β r t))) ≤
          tsumN NR 2 (fun α β r t => indB (genB β && E' (svF c4 c2 c3 α β r t))) + Q4 * (NR * (Q4 ^ 2 * M)) +
            Q4 * (Q4 * (Q4 ^ 2 * 0))) ∧
      (∀ E' : TViewN (SudPV (V × Wv)) EF → Bool,
        tsumN NR 2 (fun α β r t => indB (genB β && E' (svF c4 c2 c3 α β r t))) ≤
          tsumN NR 2 (fun α β r t => indB (genB β && E' (rvF c4 c2 c3 α β r t))) + Q4 * (NR * (Q4 ^ 2 * M)) +
            Q4 * (Q4 * (Q4 ^ 2 * 0))) := fun c4 c2 c3 hg4 hg => by
    have hgz := (genB_iff _).1 hg
    have hgα := (genB_iff _).1 hg4
    have hpcs := sud_pcsX (heap := blank.heap) (ζ := efOf c3) off sc sms sw (rfl : C.h = 2 ^ 16) hlen
      (rfl : Wt.h = 2 ^ 10) (by omega) hPg qv (wm c2) (wc c2) (ww c2) (wp c2) (hS16 c4) (hS10 c4) (hSP c4) (hsz16 c4) (hsz c4) (hszP c4)
      (generic_ofF_ne hgz) (mz_generic hgz) (fri c4) (mz_generic hgα) (generic_apow_ne hgα) hncw NR2 (Rb c4) (Ro c4)
    have hNR : sudNR off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt tP (S16 c4) (S10 c4) (SP c4) (efOf c3) qv (wm c2) (wc c2) (ww c2) (wp c2) ncw = sudNR off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt tP (S16 0) (S10 0) (SP 0) EF.zero qv (wm 0) (wc 0) (ww 0) (wp 0) ncw := by
      unfold sudNR; rw [(hSd c4 c2 c3).n1, (hSd c4 c2 c3).n2]
    rw [hNR] at hpcs
    exact ⟨fun E' => (sud_transcriptG off NR 0 (pcsZ c4 c2 (efOf c3)) (psimZ c4 c2 (efOf c3)) hbal hun hpcs E').1,
      fun E' => (sud_transcriptG off NR 0 (pcsZ c4 c2 (efOf c3)) (psimZ c4 c2 (efOf c3)) hbal hun hpcs E').2⟩
  have hlen8 : ∀ (c4 : Nat) (ζ : EF) t α β, (cols t α β).map List.length = (cols t EF.zero EF.zero).map List.length :=
    fun c4 ζ t α β => by
      rw [(sudCols_shaped off blank.hd blank.stk blank.heap.length (rfl : C.h = 2 ^ 16) hlen (rfl : Wt.h = 2 ^ 10) hPg
          (S16 c4) (S10 c4) (SP c4) ζ qv t α β).2,
        (sudCols_shaped off blank.hd blank.stk blank.heap.length (rfl : C.h = 2 ^ 16) hlen (rfl : Wt.h = 2 ^ 10) hPg
          (S16 c4) (S10 c4) (SP c4) ζ qv t EF.zero EF.zero).2]
  have hmk1 : ∀ k ∈ mk1, k < 8 ∧ ∀ t α β, k < (cols t α β).length ∧
      (cols t α β).getD k [] = (cols t EF.zero EF.zero).getD k [] := by
    intro k hk
    have hk' := hk
    simp only [mk1, List.mem_cons, List.not_mem_nil, or_false] at hk'
    have hkn : k < 8 := by rcases hk' with rfl | rfl | rfl | rfl <;> decide
    exact ⟨hkn, fun t α β => ⟨hkn, sudCols_main off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt t α β
      EF.zero EF.zero k hk⟩⟩
  have hmk2 : ∀ k ∈ mk2, k < 8 ∧ ∀ t α β, k < (cols t α β).length := by
    intro k hk
    simp only [mk2, List.mem_cons, List.not_mem_nil, or_false] at hk
    have hkn : k < 8 := by rcases hk with rfl | rfl | rfl | rfl <;> decide
    exact ⟨hkn, fun _ _ _ => hkn⟩
  have hvo1 : ∀ c4 c2 c3 c r t, rvF c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t = none ∨
      ov1 c4 (rvF c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (opF (Ss c4) mk1 (main1 t r)) := by
    intro c4 c2 c3 c r t
    show realVN off tabs tv tp (pcsZ c4 c2 (efOf c3)) _ _ r t = none ∨
      ov1 c4 (realVN off tabs tv tp (pcsZ c4 c2 (efOf c3)) _ _ r t) = _
    unfold realVN
    split
    · exact .inl rfl
    · have e := pcsFri_ov2 off (fun pre β t => sudViewN pre β blank.hd blank.stk blank.heap.length C Mm Wt t) (sudGroups tP (S16 c4) (S10 c4) (SP c4) (efOf c3) qv) ks cols ((sudTs off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt tP (S16 c4) (S10 c4) (SP c4) (efOf c3) qv (wm c2) (wc c2) (ww c2) (wp c2)).map Prod.fst) (fun t α β ms => (sudTs off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt tP (S16 c4) (S10 c4) (SP c4) (efOf c3) qv (wm c2) (wc c2) (ww c2) (wp c2)).map fun p => p.2 t α β ms) ncw (αd c4)
        (friX (fri c4) (Rb c4) (Ro c4) (r / NR0)) mk1 hmk1 (hlen8 c4 (efOf c3)) rfl t (efOf (c / Q4)) (efOf (c % Q4)) (r % NR0)
      rw [(hSd c4 c2 c3).dataF2 cols mk1 t (r % NR0), (hSw c4 c2 c3).S] at e
      exact .inr (congrArg some e)
  have hvo2 : ∀ c4 c2 c3 c r t, rvF c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t = none ∨
      ov2 c4 (rvF c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (opF (Ss c4) mk2 (main2 c t r)) := by
    intro c4 c2 c3 c r t
    show realVN off tabs tv tp (pcsZ c4 c2 (efOf c3)) _ _ r t = none ∨
      ov2 c4 (realVN off tabs tv tp (pcsZ c4 c2 (efOf c3)) _ _ r t) = _
    unfold realVN
    split
    · exact .inl rfl
    · have e := pcsFri_ovP off (fun pre β t => sudViewN pre β blank.hd blank.stk blank.heap.length C Mm Wt t) (sudGroups tP (S16 c4) (S10 c4) (SP c4) (efOf c3) qv) ks cols ((sudTs off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt tP (S16 c4) (S10 c4) (SP c4) (efOf c3) qv (wm c2) (wc c2) (ww c2) (wp c2)).map Prod.fst) (fun t α β ms => (sudTs off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt tP (S16 c4) (S10 c4) (SP c4) (efOf c3) qv (wm c2) (wc c2) (ww c2) (wp c2)).map fun p => p.2 t α β ms) ncw (αd c4)
        (friX (fri c4) (Rb c4) (Ro c4) (r / NR0)) mk2 hmk2 rfl t (efOf (c / Q4)) (efOf (c % Q4)) (r % NR0)
      rw [(hSd c4 c2 c3).dataP2 cols mk2 t _ _ (r % NR0), (hSw c4 c2 c3).S] at e
      exact .inr (congrArg some e)
  have hvo3 : ∀ c4 c2 c3 c r t, rvF c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t = none ∨
      ov3 c4 (rvF c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (op3 c4 (main3 c c2 t r)) := by
    intro c4 c2 c3 c r t
    show realVN off tabs tv tp (pcsZ c4 c2 (efOf c3)) _ _ r t = none ∨
      ov3 c4 (realVN off tabs tv tp (pcsZ c4 c2 (efOf c3)) _ _ r t) = _
    unfold realVN
    split
    · exact .inl rfl
    · rename_i hab
      have hab' : Aborts (prefixOf (efOf (c / Q4)) (off (efOf (c % Q4)))) (efOf (c % Q4)) (tabs t) = false := by
        cases h : Aborts (prefixOf (efOf (c / Q4)) (off (efOf (c % Q4)))) (efOf (c % Q4)) (tabs t)
        · rfl
        · exact absurd h hab
      have e0 := pcsFri_ovR2 off (fun pre β t => sudViewN pre β blank.hd blank.stk blank.heap.length C Mm Wt t) (sudGroups tP (S16 c4) (S10 c4) (SP c4) (efOf c3) qv) ks cols ((sudTs off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt tP (S16 c4) (S10 c4) (SP c4) (efOf c3) qv (wm c2) (wc c2) (ww c2) (wp c2)).map Prod.fst) (fun t α β ms => (sudTs off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt tP (S16 c4) (S10 c4) (SP c4) (efOf c3) qv (wm c2) (wc c2) (ww c2) (wp c2)).map fun p => p.2 t α β ms) ncw (αd c4)
        (friX (fri c4) (Rb c4) (Ro c4) (r / NR0)) mk2 hmk2 rfl t (efOf (c / Q4)) (efOf (c % Q4)) (r % NR0)
      have e := congrArg Prod.snd e0
      rw [(hSz c4 c2 c3).tS, (hSz c4 c2 c3).iS, tabsPolys_congr _ _ _ _ (hSdz c4 c2 c3).shape,
        tabsCws_congr ncw _ _ _ (hSdz c4 c2 c3).shape, (hSdz c4 c2 c3).cr (r % NR0), (hSdz c4 c2 c3).cc (r % NR0),
        (hSdz c4 c2 c3).ms (r % NR0), (hS0 c4 c2).tS, (hS0 c4 c2).iS,
        sud_data_q off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt tP (S16 c4) (S10 c4) (SP c4) (S16 0) (S10 0) (SP 0) (efOf c3) EF.zero
          qv (wm c2) (wc c2) (ww c2) (wp c2) t _ _ _ hab'] at e
      exact .inr (congrArg some e)
  have hsvo1 : ∀ c4 c2 c3 c r t, ov1 c4 (svF c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (sop1 c4 c2 c3 r t) :=
    fun c4 c2 c3 c r t => congrArg some (psimFri_ov2 (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw (αd c4) _ mk1
      (fun k hk => (hmk1 k hk).1) rfl _ _ _ (r % NR0))
  have hsvo2 : ∀ c4 c2 c3 c r t, ov2 c4 (svF c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) =
      some (sop2 c4 c2 c3 c r t) :=
    fun c4 c2 c3 c r t => congrArg some (psimFri_ov2 (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw (αd c4) _ mk2
      (fun k hk => (hmk2 k hk).1) rfl _ _ _ (r % NR0))
  have hsvo3 : ∀ c4 c2 c3 c r t, ov3 c4 (svF c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) =
      some (sop3 c4 c2 c3 c r t) := by
    intro c4 c2 c3 c r t
    have e0 := psimFri_ovR2 (sudGroups tP (S16 c4) (S10 c4) (SP c4) (efOf c3) qv) ks ((sudTs off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt tP (S16 c4) (S10 c4) (SP c4) (efOf c3) qv (wm c2) (wc c2) (ww c2) (wp c2)).map Prod.fst) ncw (αd c4) (friX (fri c4) (Rb c4) (Ro c4) (r / NR0)) mk2
      (fun k hk => (hmk2 k hk).1) rfl (efOf (c / Q4)) (efOf (c % Q4)) (vS (efOf (c / Q4)) (efOf (c % Q4)) t) (r % NR0)
    have e := congrArg Prod.snd e0
    rw [(hSw c4 c2 c3).tS, (hSw c4 c2 c3).iS] at e
    exact congrArg some e
  have hsd1 : ∀ c4 t r, opF (Ss c4) mk1 (sdF (Ss c4) mk1 (opF (Ss c4) mk1 (main1 t r))) = opF (Ss c4) mk1 (main1 t r) :=
    fun c4 t r => opF_sdF _ _ _
  have hsd2 : ∀ c4 c t r, opF (Ss c4) mk2 (sdF (Ss c4) mk2 (opF (Ss c4) mk2 (main2 c t r))) =
      opF (Ss c4) mk2 (main2 c t r) :=
    fun c4 c t r => opF_sdF _ _ _
  have hsd3 : ∀ c4 c c' t r, op3 c4 (sd3 c4 (op3 c4 (main3 c c' t r))) = op3 c4 (main3 c c' t r) := fun c4 c c' t r =>
    congrArg Prod.snd (op2_sd2 (Ss c4) [] (SsT c4) (SsC c4) (fun _ => []) (main3 c c' t r).1 (main3 c c' t r).2)
  have hp3' : ∀ c4, ComPfHides NS3 Com3 (Pf3 c4) (op3 c4) := by
    intro c4
    have e1 : SsT c4 = sudSsT (S16 c4) (S10 c4) (SP c4) := sud_SsT off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt tP (S16 c4) (S10 c4) (SP c4) EF.zero qv (wm 0) (wc 0) (ww 0) (wp 0)
    have e2 : SsC c4 = sudSsC tP (S16 c4) (S10 c4) (SP c4) := sud_SsC off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt tP (S16 c4) (S10 c4) (SP c4) EF.zero qv (wm 0) (wc 0) (ww 0) (wp 0) ncw
    show ComPfHides NS3 Com3 (Pf3 c4) (fun d => (opQ (SsT c4) d.1, opCw (SsC c4) d.2))
    rw [e1, e2]; exact hp3 c4
  have hoz : ∀ c4 c2 c3 α β r t, ozF (rvF c4 c2 c3 α β r t) = ozF (rvF 0 c2 c3 α β r t) := by
    intro c4 c2 c3 α β r t
    simp only [rvF]
    unfold realVN
    cases hA : Aborts (prefixOf α (off β)) β (tabs t)
    · simp only [Bool.false_eq_true, ↓reduceIte, ozF, Option.some.injEq, Prod.mk.injEq]
      have hd := sud_same_d off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt tP (S16 c4) (S10 c4) (SP c4) (S16 0) (S10 0) (SP 0) (efOf c3) (efOf c3) qv (wm c2) (wc c2) (ww c2) (wp c2) (wm c2) (wc c2) (ww c2) (wp c2) rfl rfl rfl rfl
      refine ⟨pcsFri_ood off (fun pre β t => sudViewN pre β blank.hd blank.stk blank.heap.length C Mm Wt t) (sudGroups tP (S16 c4) (S10 c4) (SP c4) (efOf c3) qv) (sudGroups tP (S16 0) (S10 0) (SP 0) (efOf c3) qv) ks cols
        ((sudTs off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt tP (S16 c4) (S10 c4) (SP c4) (efOf c3) qv (wm c2) (wc c2) (ww c2) (wp c2)).map Prod.fst) ((sudTs off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt tP (S16 0) (S10 0) (SP 0) (efOf c3) qv (wm c2) (wc c2) (ww c2) (wp c2)).map Prod.fst) _ _ ncw (αd c4) (αd 0) _ _
        hd rfl rfl t α β (r % NR0), pcsFri_oodT off (fun pre β t => sudViewN pre β blank.hd blank.stk blank.heap.length C Mm Wt t) (sudGroups tP (S16 c4) (S10 c4) (SP c4) (efOf c3) qv) (sudGroups tP (S16 0) (S10 0) (SP 0) (efOf c3) qv) ks cols
        ((sudTs off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt tP (S16 c4) (S10 c4) (SP c4) (efOf c3) qv (wm c2) (wc c2) (ww c2) (wp c2)).map Prod.fst) ((sudTs off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt tP (S16 0) (S10 0) (SP 0) (efOf c3) qv (wm c2) (wc c2) (ww c2) (wp c2)).map Prod.fst) _ _ ncw (αd c4) (αd 0) _ _
        hd (by simp only [sudTs, bbTab, airQTabG, List.map_cons, List.map_nil]) t α β (r % NR0)
        (sud_data_q off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt tP (S16 c4) (S10 c4) (SP c4) (S16 0) (S10 0) (SP 0) (efOf c3) (efOf c3) qv (wm c2) (wc c2) (ww c2) (wp c2) t _ _ _ hA),
        pcsFri_oodC off (fun pre β t => sudViewN pre β blank.hd blank.stk blank.heap.length C Mm Wt t) (sudGroups tP (S16 c4) (S10 c4) (SP c4) (efOf c3) qv) (sudGroups tP (S16 0) (S10 0) (SP 0) (efOf c3) qv) ks cols
        ((sudTs off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt tP (S16 c4) (S10 c4) (SP c4) (efOf c3) qv (wm c2) (wc c2) (ww c2) (wp c2)).map Prod.fst) ((sudTs off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt tP (S16 0) (S10 0) (SP 0) (efOf c3) qv (wm c2) (wc c2) (ww c2) (wp c2)).map Prod.fst) _ _ ncw (αd c4) (αd 0) _ _
        hd rfl (by simp only [sudTs, bbTab, airQTabG, List.map_cons, List.map_nil]) t α β (r % NR0)⟩
    · rfl
  have hgz : sumTo K2 (fun _ => sumTo Q4 (fun c3 => indB (!genB (efOf c3)))) ≤ K2 * (P * P) := by
    rw [genB_count, sumTo_const]; exact Nat.le_refl _
  exact fs_open4_absA hK2 Q4_pos hK4 φ hφ rvF svF (fun c2 c3 => genB (efOf c3)) hgz (fun c4 => genB (αd c4)) hB4
    (fun c4 c2 c3 α β r t => realVN_cases _ _ _ _ _ α β r t) (fun c4 c2 c3 α β r t => simVN_some _ _ _ _ _ _ _ _ α β r t)
    ozF hoz (fun c4 c2 c3 hg4 hg => (hb c4 c2 c3 hg4 hg).1) (fun c4 c2 c3 hg4 hg => (hb c4 c2 c3 hg4 hg).2)
    Com1 Pf1 (fun c4 => opF (Ss c4) mk1) (fun c4 => sdF (Ss c4) mk1) d1 hc1 hp1 hr1 ov1 (fun _ => rfl) main1 hsd1
    Com2 Pf2 (fun c4 => opF (Ss c4) mk2) (fun c4 => sdF (Ss c4) mk2) d2 hc2 hp2 hr2 ov2 (fun _ => rfl) main2 hsd2
    Com3 Pf3 op3 sd3 d3 hc3 hp3' hr3 ov3 (fun _ => rfl) main3 hsd3 hvo1 hvo2 hvo3 sop1 sop2 sop3 hsvo1 hsvo2 hsvo3

set_option maxRecDepth 100000 in
/-- `sudFS4` with the first commitment hiding up to `η`: its error gains
    `Q4² NS2 NS3 NR Q4² η` at each draw of the challenges and tables. -/
def sudFS4A {V Wv P1 P2 P3 : Type} (η : Nat) (off : EF → String → EF) (puzzle : List Nat) (A : List Cell) (k : Nat) (row : Nat → Air.Row) (tP : Nat) (S16 : Nat → List F) (S10 : Nat → List F) (SP : Nat → List F) (qv : EF → EF → List EF → F → List F → List F → List EF) (wm : Nat → List (EF → EF → List F)) (wc : Nat → List (EF → EF → List F)) (ww : Nat → List (EF → EF → List F)) (wp : Nat → List (EF → EF → List F)) (K2 : Nat) (K4 : Nat) (φ : Nat → Option (List (List (List EF)) × List (List (List (List EF))) × List (List (List EF))) → Nat) (N4 : Nat) (ncw : Nat) (αd : Nat → EF) (B4 : Nat) (fri : Nat → EF → EF → List (EF → EF) → V) (NR2 : Nat) (Rb : Nat → EF → EF → Nat → List (EF → EF)) (Ro : Nat → EF → EF → Nat → Wv) (NS1 : Nat) (NS2 : Nat) (NS3 : Nat) (n1 : Nat) (n2 : Nat) (n3 : Nat) (Com1 : List (List (List F)) → Nat → Nat) (Pf1 : Nat → List (List (List F)) → Nat → P1) (Com2 : List (List (List F)) → Nat → Nat) (Pf2 : Nat → List (List (List F)) → Nat → P2) (Com3 : List (List (List (List F))) × List (List (List F)) → Nat → Nat) (Pf3 : Nat → List (List (List (List F))) × List (List (List F)) → Nat → P3) : FS4D (Option P1 × Option (P2 × P3) × TViewN (SudPV (V × Wv)) EF) :=
    let blank := stmtMachine (fun _ => false) 729 (sudokuExpr (cluesOf puzzle)) ACC REJ
    let C := cpuTableW A row k (2 ^ 16)
    let Pg := progTableS blank.heap
    let Wt := witTableS A
    let Mm := memTableC A (cpuAirS blank.hd blank.stk blank.heap.length ACC) (progAirS blank.heap) witAirS C Pg Wt
    let NR0 := sudNR off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt tP (S16 0) (S10 0) (SP 0) EF.zero qv (wm 0) (wc 0) (ww 0) (wp 0) ncw
    let pcsZ := fun (c4 c2 : Nat) (ζ : EF) t α β r => sudPcs off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt tP (S16 c4) (S10 c4) (SP c4) ζ qv (wm c2) (wc c2) (ww c2) (wp c2) ncw (αd c4)
      (friX (fri c4) (Rb c4) (Ro c4) (r / NR0)) t α β (r % NR0)
    let psimZ := fun (c4 c2 : Nat) (ζ : EF) α β v r => sudPsim off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt tP (S16 c4) (S10 c4) (SP c4) ζ qv (wm c2) (wc c2) (ww c2) (wp c2) ncw (αd c4)
      (friX (fri c4) (Rb c4) (Ro c4) (r / NR0)) α β v (r % NR0)
    let NR := NR0 * NR2
    let tabs := fun t : Nat → Tup => sudTables blank.hd blank.stk blank.heap.length blank.heap
      ((C.setBlind BLA (t 1)).setBlind BLB (t 0)) (Mm.setBlind 5 (t 0)) (progTableS blank.heap) (Wt.setBlind 1 (t 1))
    let tv := fun pre β t => sudViewN pre β blank.hd blank.stk blank.heap.length C Mm Wt t
    let tp := fun pre β => terminal pre β (progAirS blank.heap) (progTableS blank.heap)
    let M := (allEntries (sudTables blank.hd blank.stk blank.heap.length blank.heap C Mm (progTableS blank.heap) Wt)).length
    let q0 := sudGroups tP (S16 0) (S10 0) (SP 0) EF.zero qv
    let qZ := fun (c4 : Nat) (ζ : EF) => sudGroups tP (S16 c4) (S10 c4) (SP c4) ζ qv
    let Ss := fun c4 => (qZ c4 EF.zero).map (·.base.S)
    let ks := sudKs blank.hd blank.stk blank.heap.length blank.heap
    let cols := sudCols off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt
    let tqZ := fun (c4 c2 : Nat) (ζ : EF) => (sudTs off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt tP (S16 c4) (S10 c4) (SP c4) ζ qv (wm c2) (wc c2) (ww c2) (wp c2)).map Prod.fst
    let qdZ := fun (c4 c2 : Nat) (ζ : EF) (t : Nat → Tup) (α β : EF) (ms : List F) =>
      (sudTs off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt tP (S16 c4) (S10 c4) (SP c4) ζ qv (wm c2) (wc c2) (ww c2) (wp c2)).map (fun p => p.2 t α β ms)
    let SsT := fun c4 => (tqZ c4 0 EF.zero).map (·.S)
    let SsC := fun c4 => (tabsInfo ncw (tqZ c4 0 EF.zero)).map (·.S)
    let mk1 := [0, 2, 4, 6]
    let mk2 := [1, 3, 5, 7]
    let main1 := fun (t : Nat → Tup) (r : Nat) => mainF2 q0 ks cols (tqZ 0 0 EF.zero) ncw mk1 t (r % NR0)
    let main2 := fun (c1 : Nat) (t : Nat → Tup) (r : Nat) =>
      mainP2 q0 ks cols (tqZ 0 0 EF.zero) ncw mk2 t (efOf (c1 / Q4)) (efOf (c1 % Q4)) (r % NR0)
    let main3 := fun (c1 c2 : Nat) (t : Nat → Tup) (r : Nat) =>
      (tabsPolys (tqZ 0 c2 EF.zero) (qdZ 0 c2 EF.zero t (efOf (c1 / Q4)) (efOf (c1 % Q4))
          (msF q0 ks (tqZ 0 c2 EF.zero) ncw (r % NR0))) (crF q0 ks (tqZ 0 c2 EF.zero) ncw (r % NR0)),
       tabsCws ncw (tqZ 0 c2 EF.zero) (ccF q0 ks (tqZ 0 c2 EF.zero) ncw (r % NR0)))
    let vS := fun (α β : EF) (t : Nat → Tup) => viewT β (fun k => prefixOf α (off β) (chainBus k)) (fun _ => false)
      chainPar 3 (xrefN (tp (prefixOf α (off β)) β)) t
    let sop1 := fun (c4 c2 c3 r : Nat) (_ : Nat → Tup) =>
      opF (Ss c4) mk1 (mainZ2 (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw mk1 (r % NR0))
    let sop2 := fun (c4 c2 c3 _ r : Nat) (_ : Nat → Tup) =>
      opF (Ss c4) mk2 (mainZ2 (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw mk2 (r % NR0))
    let sop3 := fun (c4 c2 c3 c1 r : Nat) (t : Nat → Tup) =>
      (opQ (SsT c4) (tabsPolys (tqZ c4 c2 (efOf c3)) (canonT (tqZ c4 c2 (efOf c3)) (efOf (c1 / Q4)) (efOf (c1 % Q4))
         (vS (efOf (c1 / Q4)) (efOf (c1 % Q4)) t)
         (openMulti ((qZ c4 (efOf c3)).map QGroup.ext) ((((qZ c4 (efOf c3)).map QGroup.ext).zip ks).map
           (fun p => List.replicate p.2 (List.replicate p.1.n (0 : F))))
           (msF (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw (r % NR0))))
         (crF (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw (r % NR0))),
       opCw (SsC c4) (tabsCws ncw (tqZ c4 c2 (efOf c3)) (ccF (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw (r % NR0))))
    let ov1 : Nat → TViewN (SudPV (V × Wv)) EF → Option (List (List (List F))) := fun c4 v => match v with
      | some (pv, _) => some (ovF2 (Ss c4) mk1 pv)
      | none => none
    let ov2 : Nat → TViewN (SudPV (V × Wv)) EF → Option (List (List (List F))) := fun c4 v => match v with
      | some (pv, _) => some (ovF2 (Ss c4) mk2 pv)
      | none => none
    let ov3 : Nat → TViewN (SudPV (V × Wv)) EF → Option (List (List (List (List F))) × List (List (List F))) :=
      fun _ v => match v with
      | some (pv, _) => some (ovQ pv, cwQ 8 pv)
      | none => none
    let rvF := fun (c4 c2 c3 : Nat) (α β : EF) (r : Nat) (t : Nat → Tup) =>
      realVN off tabs tv tp (pcsZ c4 c2 (efOf c3)) α β r t
    let svF := fun (c4 c2 c3 : Nat) (α β : EF) (r : Nat) (t : Nat → Tup) =>
      simVN off tp chainBus (fun _ => false) chainPar 3 tp (psimZ c4 c2 (efOf c3)) α β r t
    let ozF : TViewN (SudPV (V × Wv)) EF → Option (List (List (List EF)) × List (List (List (List EF))) × List (List (List EF))) := fun v => match v with
      | some (pv, _) => some (pv.1.1.map (fun g => g.1.map Prod.snd), pv.1.2.map (List.map (List.map Prod.snd)),
        pv.2.1.map (List.map Prod.snd))
      | none => none
    let op3 := fun (c4 : Nat) (d : List (List (List (List F))) × List (List (List F))) =>
      (opQ (SsT c4) d.1, opCw (SsC c4) d.2)
    let sd3 := fun (c4 : Nat) (o : List (List (List (List F))) × List (List (List F))) =>
      (sdQ (SsT c4) o.1, sdCw (SsC c4) o.2)
    let sm := fun (g : Nat × Nat × Nat × (Nat → Tup) → Nat) =>
      sumTo NS1 (fun σ1 => sumTo (NS2 * NS3) (fun σ => sumTo NR (fun r => sumN 2 (fun t => g (σ1, σ, r, t)))))
    let m1 := fun (x : Nat × Nat × Nat × (Nat → Tup)) => Com1 (main1 x.2.2.2 x.2.2.1) x.1
    let m2 := fun (c1 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      m1 x + n1 * Com2 (main2 c1 x.2.2.2 x.2.2.1) (x.2.1 % NS2)
    let m3 := fun (c1 c2 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      m1 x + n1 * comPair NS2 n2 Com2 Com3 (main2 c1 x.2.2.2 x.2.2.1, main3 c1 c2 x.2.2.2 x.2.2.1) x.2.1
    let rvo := fun (c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      ((ov1 c4 (rvF c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)).map (fun _ => Pf1 c4 (main1 x.2.2.2 x.2.2.1) x.1),
       (ovPair (ov2 c4) (ov3 c4) (rvF c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)).map
         (fun _ => pfPair NS2 (Pf2 c4) (Pf3 c4) (main2 c1 x.2.2.2 x.2.2.1, main3 c1 c2 x.2.2.2 x.2.2.1) x.2.1),
       rvF c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)
    let s1 := fun (c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) => Com1 (sdF (Ss c4) mk1 (sop1 c4 c2 c3 x.2.2.1 x.2.2.2)) x.1
    let s2 := fun (c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      s1 c4 c1 c2 c3 x + n1 * Com2 (sdF (Ss c4) mk2 (sop2 c4 c2 c3 c1 x.2.2.1 x.2.2.2)) (x.2.1 % NS2)
    let s3 := fun (c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      s1 c4 c1 c2 c3 x + n1 * comPair NS2 n2 Com2 Com3
        (sdF (Ss c4) mk2 (sop2 c4 c2 c3 c1 x.2.2.1 x.2.2.2), sd3 c4 (sop3 c4 c2 c3 c1 x.2.2.1 x.2.2.2)) x.2.1
    let svo := fun (c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      (some (Pf1 c4 (sdF (Ss c4) mk1 (sop1 c4 c2 c3 x.2.2.1 x.2.2.2)) x.1),
       some (pfPair NS2 (Pf2 c4) (Pf3 c4) (sdF (Ss c4) mk2 (sop2 c4 c2 c3 c1 x.2.2.1 x.2.2.2), sd3 c4 (sop3 c4 c2 c3 c1 x.2.2.1 x.2.2.2)) x.2.1),
       svF c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)
    let sm4 := fun (g : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup)) → Nat) =>
      sumTo ((Q4 * Q4) ^ n1) (fun H1 => sumTo (K2 ^ (n1 * n2)) (fun H2 =>
        sumTo (Q4 ^ (n1 * (n2 * n3))) (fun H3 => sm (fun x => g (H1, H2, H3, x)))))
    let r1 := fun (y : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup))) => rget (Q4 * Q4) (m1 y.2.2.2) y.1
    let r2 := fun (y : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup))) => rget K2 (m2 (r1 y) y.2.2.2) y.2.1
    let r3 := fun (y : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup))) => rget Q4 (m3 (r1 y) (r2 y) y.2.2.2) y.2.2.1
    let Mq := fun (y : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup))) => φ (m3 (r1 y) (r2 y) y.2.2.2)
      (ozF (rvF 0 (r2 y) (r3 y) (efOf (r1 y / Q4)) (efOf (r1 y % Q4)) y.2.2.2.2.2.1 y.2.2.2.2.2.2))
  ⟨NS1, NS2 * NS3, NR, m1, m2, m3,
    fun c1 c2 c3 x => φ (m3 c1 c2 x) (ozF (rvF 0 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)),
    rvo,
    fun c x => (s1 c.2.2.2 c.1 c.2.1 c.2.2.1 x, s2 c.2.2.2 c.1 c.2.1 c.2.2.1 x, s3 c.2.2.2 c.1 c.2.1 c.2.2.1 x,
      φ (s3 c.2.2.2 c.1 c.2.1 c.2.2.1 x) (ozF (svF c.2.2.2 c.2.1 c.2.2.1 (efOf (c.1 / Q4)) (efOf (c.1 % Q4)) x.2.2.1 x.2.2.2))),
    fun c x => (s1 c.2.2.2 c.1 c.2.1 c.2.2.1 x, s2 c.2.2.2 c.1 c.2.1 c.2.2.1 x, s3 c.2.2.2 c.1 c.2.1 c.2.2.1 x,
      svo c.2.2.2 c.1 c.2.1 c.2.2.1 x),
    K4 ^ N4 * (K4 * ((Q4 * Q4) ^ n1 * (K2 ^ (n1 * n2) * (Q4 ^ (n1 * (n2 * n3)) *
          (K2 * (Q4 * (NS1 * (NS2 * NS3 * (Q4 * (NR * (Q4 ^ 2 * M)) + Q4 * (Q4 * (Q4 ^ 2 * 0)))) +
            Q4 * Q4 * (NS2 * NS3 * (NR * (Q4 ^ 2 * η))))) +
            (Q4 * (P * P) * (K2 * Q4) + Q4 * Q4 * (K2 * (P * P))) * (NS1 * (NS2 * NS3 * (NR * (Q4 ^ 2 * 1)))))))) +
            B4 * (Q4 * Q4 * (K2 * Q4) * sm4 (fun _ => 1)))⟩

set_option maxRecDepth 100000 in
/-- **`sud_fs4` with the first commitment hiding up to `η`**
    (`sudFS4A`, `sud_fs_open4_absA`).  One direction. -/
theorem sud_fs4A {V Wv P1 P2 P3 : Type} (off : EF → String → EF) {puzzle : List Nat} (hc : CluesOK (cluesOf puzzle))
    {ρ : Nat → Bool} {A : List Cell} {k : Nat} {row : Nat → Air.Row}
    (hA : AcceptsFrom A (stmtMachine ρ 729 (sudokuExpr (cluesOf puzzle)) ACC REJ) k row)
    (hacc : rd A (row (k - 1)).ctr (row (k - 1)).hd = some (.atom ACC))
    (hlen : A.length = 2 ^ 16) (hk : k ≤ 2 ^ 16)
    {tP : Nat} (htp : tP = progTp (stmtMachine (fun _ => false) 729 (sudokuExpr (cluesOf puzzle)) ACC REJ).heap)
    (S16 S10 SP : Nat → List F) (qv : EF → EF → List EF → F → List F → List F → List EF)
    (wm wc ww wp : Nat → List (EF → EF → List F)) {Lwm Lwc Lww Lwp : Nat} (hlwm : ∀ c, (wm c).length = Lwm)
    (hlwc : ∀ c, (wc c).length = Lwc) (hlww : ∀ c, (ww c).length = Lww) (hlwp : ∀ c, (wp c).length = Lwp)
    {K2 K4 : Nat} (hK2 : 0 < K2) (hK4 : 0 < K4)
    (φ : Nat → Option (List (List (List EF)) × List (List (List (List EF))) × List (List (List EF))) → Nat) {N4 : Nat} (hφ : ∀ m w, φ m w < N4)
    (hS16 : ∀ c4, ∀ x ∈ S16 c4, x ∉ cosetL 1 (bbGen 16) (2 ^ 16)) (hS10 : ∀ c4, ∀ x ∈ S10 c4, x ∉ cosetL 1 (bbGen 10) (2 ^ 10))
    (hSP : ∀ c4, ∀ x ∈ SP c4, x ∉ cosetL 1 (bbGen (tP + 1)) (2 ^ (tP + 1)))
    (hsz16 : ∀ c4, 2 * (S16 c4).length + 8 ≤ 2 ^ 16) (hsz : ∀ c4, 2 * (S10 c4).length + 8 ≤ 2 ^ 10)
    (hszP : ∀ c4, 2 * (SP c4).length + 8 ≤ 2 ^ (tP + 1)) {ncw : Nat} (αd : Nat → EF) {B4 : Nat}
    (hB4 : sumTo K4 (fun c4 => indB (!genB (αd c4))) ≤ B4) (fri : Nat → EF → EF → List (EF → EF) → V)
    (hncw : 4 ≤ ncw)
    (NR2 : Nat) (Rb : Nat → EF → EF → Nat → List (EF → EF)) (Ro : Nat → EF → EF → Nat → Wv)
    {NS1 NS2 NS3 n1 n2 n3 : Nat}
    (Com1 : List (List (List F)) → Nat → Nat) (Pf1 : Nat → List (List (List F)) → Nat → P1) {η : Nat} (hc1 : ComHidesA NS1 η Com1)
    (hp1 : ∀ c4, ComPfHidesA NS1 η Com1 (Pf1 c4) (opF ((sudGroups tP (S16 c4) (S10 c4) (SP c4) EF.zero qv).map (·.base.S)) [0, 2, 4, 6]))
    (hr1 : ∀ d σ, Com1 d σ < n1) (d1 : List (List (List F)))
    (Com2 : List (List (List F)) → Nat → Nat) (Pf2 : Nat → List (List (List F)) → Nat → P2) (hc2 : ComHides NS2 Com2)
    (hp2 : ∀ c4, ComPfHides NS2 Com2 (Pf2 c4) (opF ((sudGroups tP (S16 c4) (S10 c4) (SP c4) EF.zero qv).map (·.base.S)) [1, 3, 5, 7]))
    (hr2 : ∀ d σ, Com2 d σ < n2) (d2 : List (List (List F)))
    (Com3 : List (List (List (List F))) × List (List (List F)) → Nat → Nat)
    (Pf3 : Nat → List (List (List (List F))) × List (List (List F)) → Nat → P3) (hc3 : ComHides NS3 Com3)
    (hp3 : ∀ c4, ComPfHides NS3 Com3 (Pf3 c4) (fun d => (opQ (sudSsT (S16 c4) (S10 c4) (SP c4)) d.1, opCw (sudSsC tP (S16 c4) (S10 c4) (SP c4)) d.2)))
    (hr3 : ∀ d σ, Com3 d σ < n3) (d3 : List (List (List (List F))) × List (List (List F))) :
    ZKB (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo (K4 ^ N4) (fun H4 => sumTo ((Q4 * Q4) ^ n1) (fun H1 =>
      sumTo (K2 ^ (n1 * n2)) (fun H2 => sumTo (Q4 ^ (n1 * (n2 * n3))) (fun H3 => f (H1, H2, H3, H4))))))
      (K4 * (Q4 * Q4 * (K2 * Q4))) ((sudFS4A η off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 φ N4 ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Pf1 Com2 Pf2 Com3 Pf3).sm 2)
      (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo K4 (fun c4 => sumTo (Q4 * Q4) (fun c1 =>
        sumTo K2 (fun c2 => sumTo Q4 (fun c3 => f (c1, c2, c3, c4))))))
      (read4 (Q4 * Q4) K2 Q4 K4 (sudFS4A η off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 φ N4 ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Pf1 Com2 Pf2 Com3 Pf3).m1 (sudFS4A η off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 φ N4 ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Pf1 Com2 Pf2 Com3 Pf3).m2 (sudFS4A η off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 φ N4 ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Pf1 Com2 Pf2 Com3 Pf3).m3 (sudFS4A η off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 φ N4 ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Pf1 Com2 Pf2 Com3 Pf3).q (sudFS4A η off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 φ N4 ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Pf1 Com2 Pf2 Com3 Pf3).out)
      (fun H c xx => prog4 (Q4 * Q4) K2 Q4 K4 H ((sudFS4A η off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 φ N4 ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Pf1 Com2 Pf2 Com3 Pf3).pts c xx) c) (sudFS4A η off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 φ N4 ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Pf1 Com2 Pf2 Com3 Pf3).sv (sudFS4A η off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 φ N4 ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Pf1 Com2 Pf2 Com3 Pf3).ε :=
  sud_fs_open4_absA off hc hA hacc hlen hk htp S16 S10 SP qv wm wc ww wp hlwm hlwc hlww hlwp hK2 hK4 φ hφ hS16 hS10 hSP hsz16 hsz hszP αd hB4 fri hncw NR2 Rb Ro Com1 Pf1 hc1 hp1 hr1 d1 Com2 Pf2 hc2 hp2 hr2 d2 Com3 Pf3 hc3 hp3 hr3 d3

set_option maxRecDepth 100000 in
/-- **`wit_fs_open4_abs` with the first commitment hiding up to `η`**
    (`fs_open4_absA`).  One direction. -/
theorem wit_fs_open4_absA {V Wv P1 P2 P3 : Type} (off : EF → String → EF) {Vt x : Term} {W : Nat} {ws : List Cell} (hwf : WF ws)
    (hwl : ws.length = W) (hW8 : W ≤ 2 ^ 8) {A : List Cell} {k : Nat} {row : Nat → Air.Row}
    (hA : AcceptsFrom A (wMachine ws (Vt ⬝ x)) k row)
    (hK : rd A (row (k - 1)).ctr (row (k - 1)).hd = some .K ∧ rd A (row (k - 1)).ctr (row (k - 1)).stk = some .nil)
    (hlen : A.length = 2 ^ 10) (hk : k ≤ 2 ^ 10)
    {tP : Nat} (htp : tP = progTpW (wMachine (List.replicate W .S) (Vt ⬝ x)).heap W)
    (S10 S9 SP : Nat → List F) (qv : EF → EF → List EF → F → List F → List F → List EF)
    (wm wc ww wp : Nat → List (EF → EF → List F)) {Lwm Lwc Lww Lwp : Nat} (hlwm : ∀ c, (wm c).length = Lwm)
    (hlwc : ∀ c, (wc c).length = Lwc) (hlww : ∀ c, (ww c).length = Lww) (hlwp : ∀ c, (wp c).length = Lwp)
    {K2 K4 : Nat} (hK2 : 0 < K2) (hK4 : 0 < K4)
    (φ : Nat → Option (List (List (List EF)) × List (List (List (List EF))) × List (List (List EF))) → Nat) {N4 : Nat} (hφ : ∀ m w, φ m w < N4)
    (hS10 : ∀ c4, ∀ x ∈ S10 c4, x ∉ cosetL 1 (bbGen 10) (2 ^ 10)) (hS9 : ∀ c4, ∀ x ∈ S9 c4, x ∉ cosetL 1 (bbGen 9) (2 ^ 9))
    (hSP : ∀ c4, ∀ x ∈ SP c4, x ∉ cosetL 1 (bbGen (tP + 1)) (2 ^ (tP + 1)))
    (hsz10 : ∀ c4, 2 * (S10 c4).length + 8 ≤ 2 ^ 10) (hsz9 : ∀ c4, 2 * (S9 c4).length + 8 ≤ 2 ^ 9)
    (hszP : ∀ c4, 2 * (SP c4).length + 8 ≤ 2 ^ (tP + 1)) {ncw : Nat} (αd : Nat → EF) {B4 : Nat}
    (hB4 : sumTo K4 (fun c4 => indB (!genB (αd c4))) ≤ B4) (fri : Nat → EF → EF → List (EF → EF) → V) (hncw : 4 ≤ ncw)
    (NR2 : Nat) (Rb : Nat → EF → EF → Nat → List (EF → EF)) (Ro : Nat → EF → EF → Nat → Wv)
    {NS1 NS2 NS3 n1 n2 n3 : Nat}
    (Com1 : List (List (List F)) → Nat → Nat) (Pf1 : Nat → List (List (List F)) → Nat → P1) {η : Nat} (hc1 : ComHidesA NS1 η Com1)
    (hp1 : ∀ c4, ComPfHidesA NS1 η Com1 (Pf1 c4) (opF ((wGroups tP (S10 c4) (S9 c4) (SP c4) EF.zero qv).map (·.base.S)) [0, 2, 4, 6]))
    (hr1 : ∀ d σ, Com1 d σ < n1) (d1 : List (List (List F)))
    (Com2 : List (List (List F)) → Nat → Nat) (Pf2 : Nat → List (List (List F)) → Nat → P2) (hc2 : ComHides NS2 Com2)
    (hp2 : ∀ c4, ComPfHides NS2 Com2 (Pf2 c4) (opF ((wGroups tP (S10 c4) (S9 c4) (SP c4) EF.zero qv).map (·.base.S)) [1, 3, 5, 7]))
    (hr2 : ∀ d σ, Com2 d σ < n2) (d2 : List (List (List F)))
    (Com3 : List (List (List (List F))) × List (List (List F)) → Nat → Nat)
    (Pf3 : Nat → List (List (List (List F))) × List (List (List F)) → Nat → P3) (hc3 : ComHides NS3 Com3)
    (hp3 : ∀ c4, ComPfHides NS3 Com3 (Pf3 c4) (fun d => (opQ (wSsT (S10 c4) (S9 c4) (SP c4)) d.1, opCw (wSsC tP (S10 c4) (S9 c4) (SP c4)) d.2)))
    (hr3 : ∀ d σ, Com3 d σ < n3) (d3 : List (List (List (List F))) × List (List (List F))) :
    let blank := wMachine (List.replicate W .S) (Vt ⬝ x)
    let C := cpuTableW A row k (2 ^ 10)
    let Pg := progTableW blank.heap W
    let Wt := witTableG 0 A 0 W
    let Mm := memTableC A (cpuAirW blank.hd blank.stk blank.heap.length) (progAirW blank.heap W) (witAirW W) C Pg Wt
    let NR0 := wNR off blank.hd blank.stk blank.heap.length blank.heap W C Mm Wt tP (S10 0) (S9 0) (SP 0) EF.zero qv (wm 0) (wc 0) (ww 0) (wp 0) ncw
    let pcsZ := fun (c4 c2 : Nat) (ζ : EF) t α β r => wPcs off blank.hd blank.stk blank.heap.length blank.heap W C Mm Wt tP (S10 c4) (S9 c4) (SP c4) ζ qv (wm c2) (wc c2) (ww c2) (wp c2) ncw (αd c4)
      (friX (fri c4) (Rb c4) (Ro c4) (r / NR0)) t α β (r % NR0)
    let psimZ := fun (c4 c2 : Nat) (ζ : EF) α β v r => wPsim off blank.hd blank.stk blank.heap.length blank.heap W C Mm Wt tP (S10 c4) (S9 c4) (SP c4) ζ qv (wm c2) (wc c2) (ww c2) (wp c2) ncw (αd c4)
      (friX (fri c4) (Rb c4) (Ro c4) (r / NR0)) α β v (r % NR0)
    let NR := NR0 * NR2
    let tabs := fun t : Nat → Tup => witTables blank.hd blank.stk blank.heap.length blank.heap W
      ((C.setBlind BLA (t 1)).setBlind BLB (t 0)) (Mm.setBlind 5 (t 0)) (progTableW blank.heap W)
      (Wt.setBlind WT_BLIND (t 1))
    let tv := fun pre β t => witViewN pre β blank.hd blank.stk blank.heap.length W C Mm Wt t
    let ptm := fun pre β => terminal pre β (progAirW blank.heap W) (progTableW blank.heap W)
    let M := (allEntries (witTables blank.hd blank.stk blank.heap.length blank.heap W C Mm (progTableW blank.heap W)
      Wt)).length
    let q0 := wGroups tP (S10 0) (S9 0) (SP 0) EF.zero qv
    let qZ := fun (c4 : Nat) (ζ : EF) => wGroups tP (S10 c4) (S9 c4) (SP c4) ζ qv
    let Ss := fun c4 => (qZ c4 EF.zero).map (·.base.S)
    let ks := wKs blank.hd blank.stk blank.heap.length blank.heap W
    let cols := wCols off blank.hd blank.stk blank.heap.length blank.heap W C Mm Wt
    let tqZ := fun (c4 c2 : Nat) (ζ : EF) => (wTs off blank.hd blank.stk blank.heap.length blank.heap W C Mm Wt tP (S10 c4) (S9 c4) (SP c4) ζ qv (wm c2) (wc c2) (ww c2) (wp c2)).map Prod.fst
    let qdZ := fun (c4 c2 : Nat) (ζ : EF) (t : Nat → Tup) (α β : EF) (ms : List F) =>
      (wTs off blank.hd blank.stk blank.heap.length blank.heap W C Mm Wt tP (S10 c4) (S9 c4) (SP c4) ζ qv (wm c2) (wc c2) (ww c2) (wp c2)).map (fun p => p.2 t α β ms)
    let SsT := fun c4 => (tqZ c4 0 EF.zero).map (·.S)
    let SsC := fun c4 => (tabsInfo ncw (tqZ c4 0 EF.zero)).map (·.S)
    let mk1 := [0, 2, 4, 6]
    let mk2 := [1, 3, 5, 7]
    let main1 := fun (t : Nat → Tup) (r : Nat) => mainF2 q0 ks cols (tqZ 0 0 EF.zero) ncw mk1 t (r % NR0)
    let main2 := fun (c1 : Nat) (t : Nat → Tup) (r : Nat) =>
      mainP2 q0 ks cols (tqZ 0 0 EF.zero) ncw mk2 t (efOf (c1 / Q4)) (efOf (c1 % Q4)) (r % NR0)
    let main3 := fun (c1 c2 : Nat) (t : Nat → Tup) (r : Nat) =>
      (tabsPolys (tqZ 0 c2 EF.zero) (qdZ 0 c2 EF.zero t (efOf (c1 / Q4)) (efOf (c1 % Q4))
          (msF q0 ks (tqZ 0 c2 EF.zero) ncw (r % NR0))) (crF q0 ks (tqZ 0 c2 EF.zero) ncw (r % NR0)),
       tabsCws ncw (tqZ 0 c2 EF.zero) (ccF q0 ks (tqZ 0 c2 EF.zero) ncw (r % NR0)))
    let vS := fun (α β : EF) (t : Nat → Tup) => viewT β (fun k => prefixOf α (off β) (chainBus k)) (fun _ => false)
      chainPar 3 (xrefN (ptm (prefixOf α (off β)) β)) t
    let sop1 := fun (c4 c2 c3 r : Nat) (_ : Nat → Tup) =>
      opF (Ss c4) mk1 (mainZ2 (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw mk1 (r % NR0))
    let sop2 := fun (c4 c2 c3 _ r : Nat) (_ : Nat → Tup) =>
      opF (Ss c4) mk2 (mainZ2 (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw mk2 (r % NR0))
    let sop3 := fun (c4 c2 c3 c1 r : Nat) (t : Nat → Tup) =>
      (opQ (SsT c4) (tabsPolys (tqZ c4 c2 (efOf c3)) (canonT (tqZ c4 c2 (efOf c3)) (efOf (c1 / Q4)) (efOf (c1 % Q4))
         (vS (efOf (c1 / Q4)) (efOf (c1 % Q4)) t)
         (openMulti ((qZ c4 (efOf c3)).map QGroup.ext) ((((qZ c4 (efOf c3)).map QGroup.ext).zip ks).map
           (fun p => List.replicate p.2 (List.replicate p.1.n (0 : F))))
           (msF (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw (r % NR0))))
         (crF (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw (r % NR0))),
       opCw (SsC c4) (tabsCws ncw (tqZ c4 c2 (efOf c3)) (ccF (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw (r % NR0))))
    let ov1 : Nat → TViewN (PcsPV (V × Wv)) EF → Option (List (List (List F))) := fun c4 v => match v with
      | some (pv, _) => some (ovF2 (Ss c4) mk1 pv)
      | none => none
    let ov2 : Nat → TViewN (PcsPV (V × Wv)) EF → Option (List (List (List F))) := fun c4 v => match v with
      | some (pv, _) => some (ovF2 (Ss c4) mk2 pv)
      | none => none
    let ov3 : Nat → TViewN (PcsPV (V × Wv)) EF → Option (List (List (List (List F))) × List (List (List F))) :=
      fun _ v => match v with
      | some (pv, _) => some (ovQ pv, cwQ 8 pv)
      | none => none
    let rvF := fun (c4 c2 c3 : Nat) (α β : EF) (r : Nat) (t : Nat → Tup) =>
      realVN off tabs tv ptm (pcsZ c4 c2 (efOf c3)) α β r t
    let svF := fun (c4 c2 c3 : Nat) (α β : EF) (r : Nat) (t : Nat → Tup) =>
      simVN off ptm chainBus (fun _ => false) chainPar 3 ptm (psimZ c4 c2 (efOf c3)) α β r t
    let ozF : TViewN (PcsPV (V × Wv)) EF → Option (List (List (List EF)) × List (List (List (List EF))) × List (List (List EF))) := fun v => match v with
      | some (pv, _) => some (pv.1.1.map (fun g => g.1.map Prod.snd), pv.1.2.map (List.map (List.map Prod.snd)),
        pv.2.1.map (List.map Prod.snd))
      | none => none
    let op3 := fun (c4 : Nat) (d : List (List (List (List F))) × List (List (List F))) =>
      (opQ (SsT c4) d.1, opCw (SsC c4) d.2)
    let sd3 := fun (c4 : Nat) (o : List (List (List (List F))) × List (List (List F))) =>
      (sdQ (SsT c4) o.1, sdCw (SsC c4) o.2)
    let sm := fun (g : Nat × Nat × Nat × (Nat → Tup) → Nat) =>
      sumTo NS1 (fun σ1 => sumTo (NS2 * NS3) (fun σ => sumTo NR (fun r => sumN 2 (fun t => g (σ1, σ, r, t)))))
    let m1 := fun (x : Nat × Nat × Nat × (Nat → Tup)) => Com1 (main1 x.2.2.2 x.2.2.1) x.1
    let m2 := fun (c1 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      m1 x + n1 * Com2 (main2 c1 x.2.2.2 x.2.2.1) (x.2.1 % NS2)
    let m3 := fun (c1 c2 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      m1 x + n1 * comPair NS2 n2 Com2 Com3 (main2 c1 x.2.2.2 x.2.2.1, main3 c1 c2 x.2.2.2 x.2.2.1) x.2.1
    let rvo := fun (c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      ((ov1 c4 (rvF c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)).map (fun _ => Pf1 c4 (main1 x.2.2.2 x.2.2.1) x.1),
       (ovPair (ov2 c4) (ov3 c4) (rvF c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)).map
         (fun _ => pfPair NS2 (Pf2 c4) (Pf3 c4) (main2 c1 x.2.2.2 x.2.2.1, main3 c1 c2 x.2.2.2 x.2.2.1) x.2.1),
       rvF c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)
    let s1 := fun (c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) => Com1 (sdF (Ss c4) mk1 (sop1 c4 c2 c3 x.2.2.1 x.2.2.2)) x.1
    let s2 := fun (c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      s1 c4 c1 c2 c3 x + n1 * Com2 (sdF (Ss c4) mk2 (sop2 c4 c2 c3 c1 x.2.2.1 x.2.2.2)) (x.2.1 % NS2)
    let s3 := fun (c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      s1 c4 c1 c2 c3 x + n1 * comPair NS2 n2 Com2 Com3
        (sdF (Ss c4) mk2 (sop2 c4 c2 c3 c1 x.2.2.1 x.2.2.2), sd3 c4 (sop3 c4 c2 c3 c1 x.2.2.1 x.2.2.2)) x.2.1
    let svo := fun (c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      (some (Pf1 c4 (sdF (Ss c4) mk1 (sop1 c4 c2 c3 x.2.2.1 x.2.2.2)) x.1),
       some (pfPair NS2 (Pf2 c4) (Pf3 c4) (sdF (Ss c4) mk2 (sop2 c4 c2 c3 c1 x.2.2.1 x.2.2.2), sd3 c4 (sop3 c4 c2 c3 c1 x.2.2.1 x.2.2.2)) x.2.1),
       svF c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)
    let sm4 := fun (g : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup)) → Nat) =>
      sumTo ((Q4 * Q4) ^ n1) (fun H1 => sumTo (K2 ^ (n1 * n2)) (fun H2 =>
        sumTo (Q4 ^ (n1 * (n2 * n3))) (fun H3 => sm (fun x => g (H1, H2, H3, x)))))
    let r1 := fun (y : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup))) => rget (Q4 * Q4) (m1 y.2.2.2) y.1
    let r2 := fun (y : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup))) => rget K2 (m2 (r1 y) y.2.2.2) y.2.1
    let r3 := fun (y : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup))) => rget Q4 (m3 (r1 y) (r2 y) y.2.2.2) y.2.2.1
    let Mq := fun (y : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup))) => φ (m3 (r1 y) (r2 y) y.2.2.2)
      (ozF (rvF 0 (r2 y) (r3 y) (efOf (r1 y / Q4)) (efOf (r1 y % Q4)) y.2.2.2.2.2.1 y.2.2.2.2.2.2))
    let ST := fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo (K4 ^ N4) (fun H4 => sumTo ((Q4 * Q4) ^ n1) (fun H1 =>
      sumTo (K2 ^ (n1 * n2)) (fun H2 => sumTo (Q4 ^ (n1 * (n2 * n3))) (fun H3 => f (H1, H2, H3, H4)))))
    let SC := fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo K4 (fun c4 => sumTo (Q4 * Q4) (fun c1 =>
      sumTo K2 (fun c2 => sumTo Q4 (fun c3 => f (c1, c2, c3, c4)))))
    let rvT := fun (H : Nat × Nat × Nat × Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      (m1 x, m2 (r1 (H.1, H.2.1, H.2.2.1, x)) x, m3 (r1 (H.1, H.2.1, H.2.2.1, x)) (r2 (H.1, H.2.1, H.2.2.1, x)) x,
       rvo (rget K4 (Mq (H.1, H.2.1, H.2.2.1, x)) H.2.2.2) (r1 (H.1, H.2.1, H.2.2.1, x)) (r2 (H.1, H.2.1, H.2.2.1, x))
         (r3 (H.1, H.2.1, H.2.2.1, x)) x)
    let pgT := fun (H : Nat × Nat × Nat × Nat) (c : Nat × Nat × Nat × Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      (rset (Q4 * Q4) (s1 c.2.2.2 c.1 c.2.1 c.2.2.1 x) H.1 c.1, rset K2 (s2 c.2.2.2 c.1 c.2.1 c.2.2.1 x) H.2.1 c.2.1,
       rset Q4 (s3 c.2.2.2 c.1 c.2.1 c.2.2.1 x) H.2.2.1 c.2.2.1,
       rset K4 (φ (s3 c.2.2.2 c.1 c.2.1 c.2.2.1 x) (ozF (svF c.2.2.2 c.2.1 c.2.2.1 (efOf (c.1 / Q4)) (efOf (c.1 % Q4))
         x.2.2.1 x.2.2.2))) H.2.2.2 c.2.2.2)
    let svT := fun (c : Nat × Nat × Nat × Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      (s1 c.2.2.2 c.1 c.2.1 c.2.2.1 x, s2 c.2.2.2 c.1 c.2.1 c.2.2.1 x, s3 c.2.2.2 c.1 c.2.1 c.2.2.1 x,
       svo c.2.2.2 c.1 c.2.1 c.2.2.1 x)
    ∀ E : Nat × Nat × Nat × Nat → Nat × Nat × Nat × (Option P1 × Option (P2 × P3) × TViewN (PcsPV (V × Wv)) EF) → Bool,
    K4 * (Q4 * Q4 * (K2 * Q4)) * ST (fun H => sm (fun x => indB (E H (rvT H x)))) ≤
      ST (fun H => SC (fun c => sm (fun x => indB (E (pgT H c x) (svT c x))))) +
      (K4 ^ N4 * (K4 * ((Q4 * Q4) ^ n1 * (K2 ^ (n1 * n2) * (Q4 ^ (n1 * (n2 * n3)) *
          (K2 * (Q4 * (NS1 * (NS2 * NS3 * (Q4 * (NR * (Q4 ^ 2 * M)) + Q4 * (Q4 * (Q4 ^ 2 * 0)))) +
            Q4 * Q4 * (NS2 * NS3 * (NR * (Q4 ^ 2 * η))))) +
            (Q4 * (P * P) * (K2 * Q4) + Q4 * Q4 * (K2 * (P * P))) * (NS1 * (NS2 * NS3 * (NR * (Q4 ^ 2 * 1)))))))) +
            B4 * (Q4 * Q4 * (K2 * Q4) * sm4 (fun _ => 1)))) := by
  intro blank C Pg Wt Mm NR0 pcsZ psimZ NR tabs tv ptm M q0 qZ Ss ks cols tqZ qdZ SsT SsC mk1 mk2 main1 main2 main3 vS sop1 sop2 sop3 ov1 ov2 ov3 rvF svF ozF op3 sd3
  obtain ⟨hbal, hun⟩ := wit_honest_zk hwf hwl hW8 hA hlen hk
  obtain ⟨sc, sms, sw, hWh⟩ := wit_run_sats hwf hwl hW8 hA hK hlen hk
  obtain ⟨_, hP23, hPg⟩ := wit_prog_height hwl hA hlen
  rw [← htp] at hP23 hPg
  have hSw := fun (c4 c2 c3 : Nat) => wit_same_w off blank.hd blank.stk blank.heap.length blank.heap W C Mm Wt tP (S10 c4) (S9 c4) (SP c4) (efOf c3) EF.zero qv (wm c2) (wc c2) (ww c2) (wp c2) (wm 0) (wc 0) (ww 0) (wp 0) ncw (by rw [hlwm, hlwm]) (by rw [hlwc, hlwc]) (by rw [hlww, hlww]) (by rw [hlwp, hlwp])
  have hSz := fun (c4 c2 c3 : Nat) => wit_same_w off blank.hd blank.stk blank.heap.length blank.heap W C Mm Wt tP (S10 c4) (S9 c4) (SP c4) (efOf c3) EF.zero qv (wm c2) (wc c2) (ww c2) (wp c2) (wm c2) (wc c2) (ww c2) (wp c2) ncw rfl rfl rfl rfl
  have hS0 := fun (c4 c2 : Nat) => wit_same_w off blank.hd blank.stk blank.heap.length blank.heap W C Mm Wt tP (S10 c4) (S9 c4) (SP c4) EF.zero EF.zero qv (wm c2) (wc c2) (ww c2) (wp c2) (wm 0) (wc 0) (ww 0) (wp 0) ncw (by rw [hlwm, hlwm]) (by rw [hlwc, hlwc]) (by rw [hlww, hlww]) (by rw [hlwp, hlwp])
  have hSd := fun (c4 c2 c3 : Nat) => wit_same_d off blank.hd blank.stk blank.heap.length blank.heap W C Mm Wt tP (S10 c4) (S9 c4) (SP c4) (S10 0) (S9 0) (SP 0) (efOf c3) EF.zero qv (wm c2) (wc c2) (ww c2) (wp c2) (wm 0) (wc 0) (ww 0) (wp 0) (by rw [hlwm, hlwm]) (by rw [hlwc, hlwc]) (by rw [hlww, hlww]) (by rw [hlwp, hlwp])
  have hSdz := fun (c4 c2 c3 : Nat) => wit_same_d off blank.hd blank.stk blank.heap.length blank.heap W C Mm Wt tP (S10 c4) (S9 c4) (SP c4) (S10 0) (S9 0) (SP 0) (efOf c3) EF.zero qv (wm c2) (wc c2) (ww c2) (wp c2) (wm c2) (wc c2) (ww c2) (wp c2) rfl rfl rfl rfl
  have hb : ∀ c4 c2 c3, genB (αd c4) = true → genB (efOf c3) = true →
      (∀ E' : TViewN (PcsPV (V × Wv)) EF → Bool,
        tsumN NR 2 (fun α β r t => indB (genB β && E' (rvF c4 c2 c3 α β r t))) ≤
          tsumN NR 2 (fun α β r t => indB (genB β && E' (svF c4 c2 c3 α β r t))) + Q4 * (NR * (Q4 ^ 2 * M)) +
            Q4 * (Q4 * (Q4 ^ 2 * 0))) ∧
      (∀ E' : TViewN (PcsPV (V × Wv)) EF → Bool,
        tsumN NR 2 (fun α β r t => indB (genB β && E' (svF c4 c2 c3 α β r t))) ≤
          tsumN NR 2 (fun α β r t => indB (genB β && E' (rvF c4 c2 c3 α β r t))) + Q4 * (NR * (Q4 ^ 2 * M)) +
            Q4 * (Q4 * (Q4 ^ 2 * 0))) := fun c4 c2 c3 hg4 hg => by
    have hgz := (genB_iff _).1 hg
    have hgα := (genB_iff _).1 hg4
    have hpcs := wit_pcsX (heap := blank.heap) (ζ := efOf c3) off sc sms sw (rfl : C.h = 2 ^ 10) hlen hWh (by omega) hPg qv
      (wm c2) (wc c2) (ww c2) (wp c2) (hS10 c4) (hS9 c4) (hSP c4) (hsz10 c4) (hsz9 c4) (hszP c4) (generic_ofF_ne hgz) (mz_generic hgz) (fri c4) (mz_generic hgα) (generic_apow_ne hgα) hncw NR2 (Rb c4) (Ro c4)
    have hNR : wNR off blank.hd blank.stk blank.heap.length blank.heap W C Mm Wt tP (S10 c4) (S9 c4) (SP c4) (efOf c3) qv (wm c2) (wc c2) (ww c2) (wp c2) ncw = wNR off blank.hd blank.stk blank.heap.length blank.heap W C Mm Wt tP (S10 0) (S9 0) (SP 0) EF.zero qv (wm 0) (wc 0) (ww 0) (wp 0) ncw := by
      unfold wNR; rw [(hSd c4 c2 c3).n1, (hSd c4 c2 c3).n2]
    rw [hNR] at hpcs
    exact ⟨fun E' => (wit_transcriptG off NR 0 (pcsZ c4 c2 (efOf c3)) (psimZ c4 c2 (efOf c3)) hbal hun hpcs E').1,
      fun E' => (wit_transcriptG off NR 0 (pcsZ c4 c2 (efOf c3)) (psimZ c4 c2 (efOf c3)) hbal hun hpcs E').2⟩
  have hlen8 : ∀ (c4 : Nat) (ζ : EF) t α β, (cols t α β).map List.length = (cols t EF.zero EF.zero).map List.length :=
    fun c4 ζ t α β => by
      rw [(wCols_shaped off blank.hd blank.stk blank.heap.length (rfl : C.h = 2 ^ 10) hlen hWh hPg
          (S10 c4) (S9 c4) (SP c4) ζ qv t α β).2,
        (wCols_shaped off blank.hd blank.stk blank.heap.length (rfl : C.h = 2 ^ 10) hlen hWh hPg
          (S10 c4) (S9 c4) (SP c4) ζ qv t EF.zero EF.zero).2]
  have hmk1 : ∀ k ∈ mk1, k < 8 ∧ ∀ t α β, k < (cols t α β).length ∧
      (cols t α β).getD k [] = (cols t EF.zero EF.zero).getD k [] := by
    intro k hk
    have hk' := hk
    simp only [mk1, List.mem_cons, List.not_mem_nil, or_false] at hk'
    have hkn : k < 8 := by rcases hk' with rfl | rfl | rfl | rfl <;> decide
    exact ⟨hkn, fun t α β => ⟨hkn, witCols_main off blank.hd blank.stk blank.heap.length blank.heap W C Mm Wt t α β
      EF.zero EF.zero k hk⟩⟩
  have hmk2 : ∀ k ∈ mk2, k < 8 ∧ ∀ t α β, k < (cols t α β).length := by
    intro k hk
    simp only [mk2, List.mem_cons, List.not_mem_nil, or_false] at hk
    have hkn : k < 8 := by rcases hk with rfl | rfl | rfl | rfl <;> decide
    exact ⟨hkn, fun _ _ _ => hkn⟩
  have hvo1 : ∀ c4 c2 c3 c r t, rvF c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t = none ∨
      ov1 c4 (rvF c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (opF (Ss c4) mk1 (main1 t r)) := by
    intro c4 c2 c3 c r t
    show realVN off tabs tv ptm (pcsZ c4 c2 (efOf c3)) _ _ r t = none ∨
      ov1 c4 (realVN off tabs tv ptm (pcsZ c4 c2 (efOf c3)) _ _ r t) = _
    unfold realVN
    split
    · exact .inl rfl
    · have e := pcsFri_ov2 off (fun pre β t => witViewN pre β blank.hd blank.stk blank.heap.length W C Mm Wt t) (wGroups tP (S10 c4) (S9 c4) (SP c4) (efOf c3) qv) ks cols ((wTs off blank.hd blank.stk blank.heap.length blank.heap W C Mm Wt tP (S10 c4) (S9 c4) (SP c4) (efOf c3) qv (wm c2) (wc c2) (ww c2) (wp c2)).map Prod.fst) (fun t α β ms => (wTs off blank.hd blank.stk blank.heap.length blank.heap W C Mm Wt tP (S10 c4) (S9 c4) (SP c4) (efOf c3) qv (wm c2) (wc c2) (ww c2) (wp c2)).map fun p => p.2 t α β ms) ncw (αd c4)
        (friX (fri c4) (Rb c4) (Ro c4) (r / NR0)) mk1 hmk1 (hlen8 c4 (efOf c3)) rfl t (efOf (c / Q4)) (efOf (c % Q4)) (r % NR0)
      rw [(hSd c4 c2 c3).dataF2 cols mk1 t (r % NR0), (hSw c4 c2 c3).S] at e
      exact .inr (congrArg some e)
  have hvo2 : ∀ c4 c2 c3 c r t, rvF c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t = none ∨
      ov2 c4 (rvF c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (opF (Ss c4) mk2 (main2 c t r)) := by
    intro c4 c2 c3 c r t
    show realVN off tabs tv ptm (pcsZ c4 c2 (efOf c3)) _ _ r t = none ∨
      ov2 c4 (realVN off tabs tv ptm (pcsZ c4 c2 (efOf c3)) _ _ r t) = _
    unfold realVN
    split
    · exact .inl rfl
    · have e := pcsFri_ovP off (fun pre β t => witViewN pre β blank.hd blank.stk blank.heap.length W C Mm Wt t) (wGroups tP (S10 c4) (S9 c4) (SP c4) (efOf c3) qv) ks cols ((wTs off blank.hd blank.stk blank.heap.length blank.heap W C Mm Wt tP (S10 c4) (S9 c4) (SP c4) (efOf c3) qv (wm c2) (wc c2) (ww c2) (wp c2)).map Prod.fst) (fun t α β ms => (wTs off blank.hd blank.stk blank.heap.length blank.heap W C Mm Wt tP (S10 c4) (S9 c4) (SP c4) (efOf c3) qv (wm c2) (wc c2) (ww c2) (wp c2)).map fun p => p.2 t α β ms) ncw (αd c4)
        (friX (fri c4) (Rb c4) (Ro c4) (r / NR0)) mk2 hmk2 rfl t (efOf (c / Q4)) (efOf (c % Q4)) (r % NR0)
      rw [(hSd c4 c2 c3).dataP2 cols mk2 t _ _ (r % NR0), (hSw c4 c2 c3).S] at e
      exact .inr (congrArg some e)
  have hvo3 : ∀ c4 c2 c3 c r t, rvF c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t = none ∨
      ov3 c4 (rvF c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (op3 c4 (main3 c c2 t r)) := by
    intro c4 c2 c3 c r t
    show realVN off tabs tv ptm (pcsZ c4 c2 (efOf c3)) _ _ r t = none ∨
      ov3 c4 (realVN off tabs tv ptm (pcsZ c4 c2 (efOf c3)) _ _ r t) = _
    unfold realVN
    split
    · exact .inl rfl
    · rename_i hab
      have hab' : Aborts (prefixOf (efOf (c / Q4)) (off (efOf (c % Q4)))) (efOf (c % Q4)) (tabs t) = false := by
        cases h : Aborts (prefixOf (efOf (c / Q4)) (off (efOf (c % Q4)))) (efOf (c % Q4)) (tabs t)
        · rfl
        · exact absurd h hab
      have e0 := pcsFri_ovR2 off (fun pre β t => witViewN pre β blank.hd blank.stk blank.heap.length W C Mm Wt t) (wGroups tP (S10 c4) (S9 c4) (SP c4) (efOf c3) qv) ks cols ((wTs off blank.hd blank.stk blank.heap.length blank.heap W C Mm Wt tP (S10 c4) (S9 c4) (SP c4) (efOf c3) qv (wm c2) (wc c2) (ww c2) (wp c2)).map Prod.fst) (fun t α β ms => (wTs off blank.hd blank.stk blank.heap.length blank.heap W C Mm Wt tP (S10 c4) (S9 c4) (SP c4) (efOf c3) qv (wm c2) (wc c2) (ww c2) (wp c2)).map fun p => p.2 t α β ms) ncw (αd c4)
        (friX (fri c4) (Rb c4) (Ro c4) (r / NR0)) mk2 hmk2 rfl t (efOf (c / Q4)) (efOf (c % Q4)) (r % NR0)
      have e := congrArg Prod.snd e0
      rw [(hSz c4 c2 c3).tS, (hSz c4 c2 c3).iS, tabsPolys_congr _ _ _ _ (hSdz c4 c2 c3).shape,
        tabsCws_congr ncw _ _ _ (hSdz c4 c2 c3).shape, (hSdz c4 c2 c3).cr (r % NR0), (hSdz c4 c2 c3).cc (r % NR0),
        (hSdz c4 c2 c3).ms (r % NR0), (hS0 c4 c2).tS, (hS0 c4 c2).iS,
        wit_data_q off blank.hd blank.stk blank.heap.length blank.heap W C Mm Wt tP (S10 c4) (S9 c4) (SP c4) (S10 0) (S9 0) (SP 0) (efOf c3) EF.zero
          qv (wm c2) (wc c2) (ww c2) (wp c2) t _ _ _ hab'] at e
      exact .inr (congrArg some e)
  have hsvo1 : ∀ c4 c2 c3 c r t, ov1 c4 (svF c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (sop1 c4 c2 c3 r t) :=
    fun c4 c2 c3 c r t => congrArg some (psimFri_ov2 (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw (αd c4) _ mk1
      (fun k hk => (hmk1 k hk).1) rfl _ _ _ (r % NR0))
  have hsvo2 : ∀ c4 c2 c3 c r t, ov2 c4 (svF c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) =
      some (sop2 c4 c2 c3 c r t) :=
    fun c4 c2 c3 c r t => congrArg some (psimFri_ov2 (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw (αd c4) _ mk2
      (fun k hk => (hmk2 k hk).1) rfl _ _ _ (r % NR0))
  have hsvo3 : ∀ c4 c2 c3 c r t, ov3 c4 (svF c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) =
      some (sop3 c4 c2 c3 c r t) := by
    intro c4 c2 c3 c r t
    have e0 := psimFri_ovR2 (wGroups tP (S10 c4) (S9 c4) (SP c4) (efOf c3) qv) ks ((wTs off blank.hd blank.stk blank.heap.length blank.heap W C Mm Wt tP (S10 c4) (S9 c4) (SP c4) (efOf c3) qv (wm c2) (wc c2) (ww c2) (wp c2)).map Prod.fst) ncw (αd c4) (friX (fri c4) (Rb c4) (Ro c4) (r / NR0)) mk2
      (fun k hk => (hmk2 k hk).1) rfl (efOf (c / Q4)) (efOf (c % Q4)) (vS (efOf (c / Q4)) (efOf (c % Q4)) t) (r % NR0)
    have e := congrArg Prod.snd e0
    rw [(hSw c4 c2 c3).tS, (hSw c4 c2 c3).iS] at e
    exact congrArg some e
  have hsd1 : ∀ c4 t r, opF (Ss c4) mk1 (sdF (Ss c4) mk1 (opF (Ss c4) mk1 (main1 t r))) = opF (Ss c4) mk1 (main1 t r) :=
    fun c4 t r => opF_sdF _ _ _
  have hsd2 : ∀ c4 c t r, opF (Ss c4) mk2 (sdF (Ss c4) mk2 (opF (Ss c4) mk2 (main2 c t r))) =
      opF (Ss c4) mk2 (main2 c t r) :=
    fun c4 c t r => opF_sdF _ _ _
  have hsd3 : ∀ c4 c c' t r, op3 c4 (sd3 c4 (op3 c4 (main3 c c' t r))) = op3 c4 (main3 c c' t r) := fun c4 c c' t r =>
    congrArg Prod.snd (op2_sd2 (Ss c4) [] (SsT c4) (SsC c4) (fun _ => []) (main3 c c' t r).1 (main3 c c' t r).2)
  have hp3' : ∀ c4, ComPfHides NS3 Com3 (Pf3 c4) (op3 c4) := by
    intro c4
    have e1 : SsT c4 = wSsT (S10 c4) (S9 c4) (SP c4) := wit_SsT off blank.hd blank.stk blank.heap.length blank.heap W C Mm Wt tP (S10 c4) (S9 c4) (SP c4) EF.zero qv (wm 0) (wc 0) (ww 0) (wp 0)
    have e2 : SsC c4 = wSsC tP (S10 c4) (S9 c4) (SP c4) := wit_SsC off blank.hd blank.stk blank.heap.length blank.heap W C Mm Wt tP (S10 c4) (S9 c4) (SP c4) EF.zero qv (wm 0) (wc 0) (ww 0) (wp 0) ncw
    show ComPfHides NS3 Com3 (Pf3 c4) (fun d => (opQ (SsT c4) d.1, opCw (SsC c4) d.2))
    rw [e1, e2]; exact hp3 c4
  have hoz : ∀ c4 c2 c3 α β r t, ozF (rvF c4 c2 c3 α β r t) = ozF (rvF 0 c2 c3 α β r t) := by
    intro c4 c2 c3 α β r t
    simp only [rvF]
    unfold realVN
    cases hA : Aborts (prefixOf α (off β)) β (tabs t)
    · simp only [Bool.false_eq_true, ↓reduceIte, ozF, Option.some.injEq, Prod.mk.injEq]
      have hd := wit_same_d off blank.hd blank.stk blank.heap.length blank.heap W C Mm Wt tP (S10 c4) (S9 c4) (SP c4) (S10 0) (S9 0) (SP 0) (efOf c3) (efOf c3) qv (wm c2) (wc c2) (ww c2) (wp c2) (wm c2) (wc c2) (ww c2) (wp c2) rfl rfl rfl rfl
      refine ⟨pcsFri_ood off (fun pre β t => witViewN pre β blank.hd blank.stk blank.heap.length W C Mm Wt t) (wGroups tP (S10 c4) (S9 c4) (SP c4) (efOf c3) qv) (wGroups tP (S10 0) (S9 0) (SP 0) (efOf c3) qv) ks cols
        ((wTs off blank.hd blank.stk blank.heap.length blank.heap W C Mm Wt tP (S10 c4) (S9 c4) (SP c4) (efOf c3) qv (wm c2) (wc c2) (ww c2) (wp c2)).map Prod.fst) ((wTs off blank.hd blank.stk blank.heap.length blank.heap W C Mm Wt tP (S10 0) (S9 0) (SP 0) (efOf c3) qv (wm c2) (wc c2) (ww c2) (wp c2)).map Prod.fst) _ _ ncw (αd c4) (αd 0) _ _
        hd rfl rfl t α β (r % NR0), pcsFri_oodT off (fun pre β t => witViewN pre β blank.hd blank.stk blank.heap.length W C Mm Wt t) (wGroups tP (S10 c4) (S9 c4) (SP c4) (efOf c3) qv) (wGroups tP (S10 0) (S9 0) (SP 0) (efOf c3) qv) ks cols
        ((wTs off blank.hd blank.stk blank.heap.length blank.heap W C Mm Wt tP (S10 c4) (S9 c4) (SP c4) (efOf c3) qv (wm c2) (wc c2) (ww c2) (wp c2)).map Prod.fst) ((wTs off blank.hd blank.stk blank.heap.length blank.heap W C Mm Wt tP (S10 0) (S9 0) (SP 0) (efOf c3) qv (wm c2) (wc c2) (ww c2) (wp c2)).map Prod.fst) _ _ ncw (αd c4) (αd 0) _ _
        hd (by simp only [wTs, bbTab, airQTabG, List.map_cons, List.map_nil]) t α β (r % NR0)
        (wit_data_q off blank.hd blank.stk blank.heap.length blank.heap W C Mm Wt tP (S10 c4) (S9 c4) (SP c4) (S10 0) (S9 0) (SP 0) (efOf c3) (efOf c3) qv (wm c2) (wc c2) (ww c2) (wp c2) t _ _ _ hA),
        pcsFri_oodC off (fun pre β t => witViewN pre β blank.hd blank.stk blank.heap.length W C Mm Wt t) (wGroups tP (S10 c4) (S9 c4) (SP c4) (efOf c3) qv) (wGroups tP (S10 0) (S9 0) (SP 0) (efOf c3) qv) ks cols
        ((wTs off blank.hd blank.stk blank.heap.length blank.heap W C Mm Wt tP (S10 c4) (S9 c4) (SP c4) (efOf c3) qv (wm c2) (wc c2) (ww c2) (wp c2)).map Prod.fst) ((wTs off blank.hd blank.stk blank.heap.length blank.heap W C Mm Wt tP (S10 0) (S9 0) (SP 0) (efOf c3) qv (wm c2) (wc c2) (ww c2) (wp c2)).map Prod.fst) _ _ ncw (αd c4) (αd 0) _ _
        hd rfl (by simp only [wTs, bbTab, airQTabG, List.map_cons, List.map_nil]) t α β (r % NR0)⟩
    · rfl
  have hgz : sumTo K2 (fun _ => sumTo Q4 (fun c3 => indB (!genB (efOf c3)))) ≤ K2 * (P * P) := by
    rw [genB_count, sumTo_const]; exact Nat.le_refl _
  exact fs_open4_absA hK2 Q4_pos hK4 φ hφ rvF svF (fun c2 c3 => genB (efOf c3)) hgz (fun c4 => genB (αd c4)) hB4
    (fun c4 c2 c3 α β r t => realVN_cases _ _ _ _ _ α β r t) (fun c4 c2 c3 α β r t => simVN_some _ _ _ _ _ _ _ _ α β r t)
    ozF hoz (fun c4 c2 c3 hg4 hg => (hb c4 c2 c3 hg4 hg).1) (fun c4 c2 c3 hg4 hg => (hb c4 c2 c3 hg4 hg).2)
    Com1 Pf1 (fun c4 => opF (Ss c4) mk1) (fun c4 => sdF (Ss c4) mk1) d1 hc1 hp1 hr1 ov1 (fun _ => rfl) main1 hsd1
    Com2 Pf2 (fun c4 => opF (Ss c4) mk2) (fun c4 => sdF (Ss c4) mk2) d2 hc2 hp2 hr2 ov2 (fun _ => rfl) main2 hsd2
    Com3 Pf3 op3 sd3 d3 hc3 hp3' hr3 ov3 (fun _ => rfl) main3 hsd3 hvo1 hvo2 hvo3 sop1 sop2 sop3 hsvo1 hsvo2 hsvo3

set_option maxRecDepth 100000 in
/-- `witFS4` with the first commitment hiding up to `η`: its error gains
    `Q4² NS2 NS3 NR Q4² η` at each draw of the challenges and tables. -/
def witFS4A {V Wv P1 P2 P3 : Type} (η : Nat) (off : EF → String → EF) (Vt : Term) (x : Term) (W : Nat) (A : List Cell) (k : Nat) (row : Nat → Air.Row) (tP : Nat) (S10 : Nat → List F) (S9 : Nat → List F) (SP : Nat → List F) (qv : EF → EF → List EF → F → List F → List F → List EF) (wm : Nat → List (EF → EF → List F)) (wc : Nat → List (EF → EF → List F)) (ww : Nat → List (EF → EF → List F)) (wp : Nat → List (EF → EF → List F)) (K2 : Nat) (K4 : Nat) (φ : Nat → Option (List (List (List EF)) × List (List (List (List EF))) × List (List (List EF))) → Nat) (N4 : Nat) (ncw : Nat) (αd : Nat → EF) (B4 : Nat) (fri : Nat → EF → EF → List (EF → EF) → V) (NR2 : Nat) (Rb : Nat → EF → EF → Nat → List (EF → EF)) (Ro : Nat → EF → EF → Nat → Wv) (NS1 : Nat) (NS2 : Nat) (NS3 : Nat) (n1 : Nat) (n2 : Nat) (n3 : Nat) (Com1 : List (List (List F)) → Nat → Nat) (Pf1 : Nat → List (List (List F)) → Nat → P1) (Com2 : List (List (List F)) → Nat → Nat) (Pf2 : Nat → List (List (List F)) → Nat → P2) (Com3 : List (List (List (List F))) × List (List (List F)) → Nat → Nat) (Pf3 : Nat → List (List (List (List F))) × List (List (List F)) → Nat → P3) : FS4D (Option P1 × Option (P2 × P3) × TViewN (PcsPV (V × Wv)) EF) :=
    let blank := wMachine (List.replicate W .S) (Vt ⬝ x)
    let C := cpuTableW A row k (2 ^ 10)
    let Pg := progTableW blank.heap W
    let Wt := witTableG 0 A 0 W
    let Mm := memTableC A (cpuAirW blank.hd blank.stk blank.heap.length) (progAirW blank.heap W) (witAirW W) C Pg Wt
    let NR0 := wNR off blank.hd blank.stk blank.heap.length blank.heap W C Mm Wt tP (S10 0) (S9 0) (SP 0) EF.zero qv (wm 0) (wc 0) (ww 0) (wp 0) ncw
    let pcsZ := fun (c4 c2 : Nat) (ζ : EF) t α β r => wPcs off blank.hd blank.stk blank.heap.length blank.heap W C Mm Wt tP (S10 c4) (S9 c4) (SP c4) ζ qv (wm c2) (wc c2) (ww c2) (wp c2) ncw (αd c4)
      (friX (fri c4) (Rb c4) (Ro c4) (r / NR0)) t α β (r % NR0)
    let psimZ := fun (c4 c2 : Nat) (ζ : EF) α β v r => wPsim off blank.hd blank.stk blank.heap.length blank.heap W C Mm Wt tP (S10 c4) (S9 c4) (SP c4) ζ qv (wm c2) (wc c2) (ww c2) (wp c2) ncw (αd c4)
      (friX (fri c4) (Rb c4) (Ro c4) (r / NR0)) α β v (r % NR0)
    let NR := NR0 * NR2
    let tabs := fun t : Nat → Tup => witTables blank.hd blank.stk blank.heap.length blank.heap W
      ((C.setBlind BLA (t 1)).setBlind BLB (t 0)) (Mm.setBlind 5 (t 0)) (progTableW blank.heap W)
      (Wt.setBlind WT_BLIND (t 1))
    let tv := fun pre β t => witViewN pre β blank.hd blank.stk blank.heap.length W C Mm Wt t
    let ptm := fun pre β => terminal pre β (progAirW blank.heap W) (progTableW blank.heap W)
    let M := (allEntries (witTables blank.hd blank.stk blank.heap.length blank.heap W C Mm (progTableW blank.heap W)
      Wt)).length
    let q0 := wGroups tP (S10 0) (S9 0) (SP 0) EF.zero qv
    let qZ := fun (c4 : Nat) (ζ : EF) => wGroups tP (S10 c4) (S9 c4) (SP c4) ζ qv
    let Ss := fun c4 => (qZ c4 EF.zero).map (·.base.S)
    let ks := wKs blank.hd blank.stk blank.heap.length blank.heap W
    let cols := wCols off blank.hd blank.stk blank.heap.length blank.heap W C Mm Wt
    let tqZ := fun (c4 c2 : Nat) (ζ : EF) => (wTs off blank.hd blank.stk blank.heap.length blank.heap W C Mm Wt tP (S10 c4) (S9 c4) (SP c4) ζ qv (wm c2) (wc c2) (ww c2) (wp c2)).map Prod.fst
    let qdZ := fun (c4 c2 : Nat) (ζ : EF) (t : Nat → Tup) (α β : EF) (ms : List F) =>
      (wTs off blank.hd blank.stk blank.heap.length blank.heap W C Mm Wt tP (S10 c4) (S9 c4) (SP c4) ζ qv (wm c2) (wc c2) (ww c2) (wp c2)).map (fun p => p.2 t α β ms)
    let SsT := fun c4 => (tqZ c4 0 EF.zero).map (·.S)
    let SsC := fun c4 => (tabsInfo ncw (tqZ c4 0 EF.zero)).map (·.S)
    let mk1 := [0, 2, 4, 6]
    let mk2 := [1, 3, 5, 7]
    let main1 := fun (t : Nat → Tup) (r : Nat) => mainF2 q0 ks cols (tqZ 0 0 EF.zero) ncw mk1 t (r % NR0)
    let main2 := fun (c1 : Nat) (t : Nat → Tup) (r : Nat) =>
      mainP2 q0 ks cols (tqZ 0 0 EF.zero) ncw mk2 t (efOf (c1 / Q4)) (efOf (c1 % Q4)) (r % NR0)
    let main3 := fun (c1 c2 : Nat) (t : Nat → Tup) (r : Nat) =>
      (tabsPolys (tqZ 0 c2 EF.zero) (qdZ 0 c2 EF.zero t (efOf (c1 / Q4)) (efOf (c1 % Q4))
          (msF q0 ks (tqZ 0 c2 EF.zero) ncw (r % NR0))) (crF q0 ks (tqZ 0 c2 EF.zero) ncw (r % NR0)),
       tabsCws ncw (tqZ 0 c2 EF.zero) (ccF q0 ks (tqZ 0 c2 EF.zero) ncw (r % NR0)))
    let vS := fun (α β : EF) (t : Nat → Tup) => viewT β (fun k => prefixOf α (off β) (chainBus k)) (fun _ => false)
      chainPar 3 (xrefN (ptm (prefixOf α (off β)) β)) t
    let sop1 := fun (c4 c2 c3 r : Nat) (_ : Nat → Tup) =>
      opF (Ss c4) mk1 (mainZ2 (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw mk1 (r % NR0))
    let sop2 := fun (c4 c2 c3 _ r : Nat) (_ : Nat → Tup) =>
      opF (Ss c4) mk2 (mainZ2 (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw mk2 (r % NR0))
    let sop3 := fun (c4 c2 c3 c1 r : Nat) (t : Nat → Tup) =>
      (opQ (SsT c4) (tabsPolys (tqZ c4 c2 (efOf c3)) (canonT (tqZ c4 c2 (efOf c3)) (efOf (c1 / Q4)) (efOf (c1 % Q4))
         (vS (efOf (c1 / Q4)) (efOf (c1 % Q4)) t)
         (openMulti ((qZ c4 (efOf c3)).map QGroup.ext) ((((qZ c4 (efOf c3)).map QGroup.ext).zip ks).map
           (fun p => List.replicate p.2 (List.replicate p.1.n (0 : F))))
           (msF (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw (r % NR0))))
         (crF (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw (r % NR0))),
       opCw (SsC c4) (tabsCws ncw (tqZ c4 c2 (efOf c3)) (ccF (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw (r % NR0))))
    let ov1 : Nat → TViewN (PcsPV (V × Wv)) EF → Option (List (List (List F))) := fun c4 v => match v with
      | some (pv, _) => some (ovF2 (Ss c4) mk1 pv)
      | none => none
    let ov2 : Nat → TViewN (PcsPV (V × Wv)) EF → Option (List (List (List F))) := fun c4 v => match v with
      | some (pv, _) => some (ovF2 (Ss c4) mk2 pv)
      | none => none
    let ov3 : Nat → TViewN (PcsPV (V × Wv)) EF → Option (List (List (List (List F))) × List (List (List F))) :=
      fun _ v => match v with
      | some (pv, _) => some (ovQ pv, cwQ 8 pv)
      | none => none
    let rvF := fun (c4 c2 c3 : Nat) (α β : EF) (r : Nat) (t : Nat → Tup) =>
      realVN off tabs tv ptm (pcsZ c4 c2 (efOf c3)) α β r t
    let svF := fun (c4 c2 c3 : Nat) (α β : EF) (r : Nat) (t : Nat → Tup) =>
      simVN off ptm chainBus (fun _ => false) chainPar 3 ptm (psimZ c4 c2 (efOf c3)) α β r t
    let ozF : TViewN (PcsPV (V × Wv)) EF → Option (List (List (List EF)) × List (List (List (List EF))) × List (List (List EF))) := fun v => match v with
      | some (pv, _) => some (pv.1.1.map (fun g => g.1.map Prod.snd), pv.1.2.map (List.map (List.map Prod.snd)),
        pv.2.1.map (List.map Prod.snd))
      | none => none
    let op3 := fun (c4 : Nat) (d : List (List (List (List F))) × List (List (List F))) =>
      (opQ (SsT c4) d.1, opCw (SsC c4) d.2)
    let sd3 := fun (c4 : Nat) (o : List (List (List (List F))) × List (List (List F))) =>
      (sdQ (SsT c4) o.1, sdCw (SsC c4) o.2)
    let sm := fun (g : Nat × Nat × Nat × (Nat → Tup) → Nat) =>
      sumTo NS1 (fun σ1 => sumTo (NS2 * NS3) (fun σ => sumTo NR (fun r => sumN 2 (fun t => g (σ1, σ, r, t)))))
    let m1 := fun (x : Nat × Nat × Nat × (Nat → Tup)) => Com1 (main1 x.2.2.2 x.2.2.1) x.1
    let m2 := fun (c1 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      m1 x + n1 * Com2 (main2 c1 x.2.2.2 x.2.2.1) (x.2.1 % NS2)
    let m3 := fun (c1 c2 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      m1 x + n1 * comPair NS2 n2 Com2 Com3 (main2 c1 x.2.2.2 x.2.2.1, main3 c1 c2 x.2.2.2 x.2.2.1) x.2.1
    let rvo := fun (c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      ((ov1 c4 (rvF c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)).map (fun _ => Pf1 c4 (main1 x.2.2.2 x.2.2.1) x.1),
       (ovPair (ov2 c4) (ov3 c4) (rvF c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)).map
         (fun _ => pfPair NS2 (Pf2 c4) (Pf3 c4) (main2 c1 x.2.2.2 x.2.2.1, main3 c1 c2 x.2.2.2 x.2.2.1) x.2.1),
       rvF c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)
    let s1 := fun (c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) => Com1 (sdF (Ss c4) mk1 (sop1 c4 c2 c3 x.2.2.1 x.2.2.2)) x.1
    let s2 := fun (c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      s1 c4 c1 c2 c3 x + n1 * Com2 (sdF (Ss c4) mk2 (sop2 c4 c2 c3 c1 x.2.2.1 x.2.2.2)) (x.2.1 % NS2)
    let s3 := fun (c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      s1 c4 c1 c2 c3 x + n1 * comPair NS2 n2 Com2 Com3
        (sdF (Ss c4) mk2 (sop2 c4 c2 c3 c1 x.2.2.1 x.2.2.2), sd3 c4 (sop3 c4 c2 c3 c1 x.2.2.1 x.2.2.2)) x.2.1
    let svo := fun (c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      (some (Pf1 c4 (sdF (Ss c4) mk1 (sop1 c4 c2 c3 x.2.2.1 x.2.2.2)) x.1),
       some (pfPair NS2 (Pf2 c4) (Pf3 c4) (sdF (Ss c4) mk2 (sop2 c4 c2 c3 c1 x.2.2.1 x.2.2.2), sd3 c4 (sop3 c4 c2 c3 c1 x.2.2.1 x.2.2.2)) x.2.1),
       svF c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)
    let sm4 := fun (g : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup)) → Nat) =>
      sumTo ((Q4 * Q4) ^ n1) (fun H1 => sumTo (K2 ^ (n1 * n2)) (fun H2 =>
        sumTo (Q4 ^ (n1 * (n2 * n3))) (fun H3 => sm (fun x => g (H1, H2, H3, x)))))
    let r1 := fun (y : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup))) => rget (Q4 * Q4) (m1 y.2.2.2) y.1
    let r2 := fun (y : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup))) => rget K2 (m2 (r1 y) y.2.2.2) y.2.1
    let r3 := fun (y : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup))) => rget Q4 (m3 (r1 y) (r2 y) y.2.2.2) y.2.2.1
    let Mq := fun (y : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup))) => φ (m3 (r1 y) (r2 y) y.2.2.2)
      (ozF (rvF 0 (r2 y) (r3 y) (efOf (r1 y / Q4)) (efOf (r1 y % Q4)) y.2.2.2.2.2.1 y.2.2.2.2.2.2))
  ⟨NS1, NS2 * NS3, NR, m1, m2, m3,
    fun c1 c2 c3 x => φ (m3 c1 c2 x) (ozF (rvF 0 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)),
    rvo,
    fun c x => (s1 c.2.2.2 c.1 c.2.1 c.2.2.1 x, s2 c.2.2.2 c.1 c.2.1 c.2.2.1 x, s3 c.2.2.2 c.1 c.2.1 c.2.2.1 x,
      φ (s3 c.2.2.2 c.1 c.2.1 c.2.2.1 x) (ozF (svF c.2.2.2 c.2.1 c.2.2.1 (efOf (c.1 / Q4)) (efOf (c.1 % Q4)) x.2.2.1 x.2.2.2))),
    fun c x => (s1 c.2.2.2 c.1 c.2.1 c.2.2.1 x, s2 c.2.2.2 c.1 c.2.1 c.2.2.1 x, s3 c.2.2.2 c.1 c.2.1 c.2.2.1 x,
      svo c.2.2.2 c.1 c.2.1 c.2.2.1 x),
    K4 ^ N4 * (K4 * ((Q4 * Q4) ^ n1 * (K2 ^ (n1 * n2) * (Q4 ^ (n1 * (n2 * n3)) *
          (K2 * (Q4 * (NS1 * (NS2 * NS3 * (Q4 * (NR * (Q4 ^ 2 * M)) + Q4 * (Q4 * (Q4 ^ 2 * 0)))) +
            Q4 * Q4 * (NS2 * NS3 * (NR * (Q4 ^ 2 * η))))) +
            (Q4 * (P * P) * (K2 * Q4) + Q4 * Q4 * (K2 * (P * P))) * (NS1 * (NS2 * NS3 * (NR * (Q4 ^ 2 * 1)))))))) +
            B4 * (Q4 * Q4 * (K2 * Q4) * sm4 (fun _ => 1)))⟩

set_option maxRecDepth 100000 in
/-- **`wit_fs4` with the first commitment hiding up to `η`**
    (`witFS4A`, `wit_fs_open4_absA`).  One direction. -/
theorem wit_fs4A {V Wv P1 P2 P3 : Type} (off : EF → String → EF) {Vt x : Term} {W : Nat} {ws : List Cell} (hwf : WF ws)
    (hwl : ws.length = W) (hW8 : W ≤ 2 ^ 8) {A : List Cell} {k : Nat} {row : Nat → Air.Row}
    (hA : AcceptsFrom A (wMachine ws (Vt ⬝ x)) k row)
    (hK : rd A (row (k - 1)).ctr (row (k - 1)).hd = some .K ∧ rd A (row (k - 1)).ctr (row (k - 1)).stk = some .nil)
    (hlen : A.length = 2 ^ 10) (hk : k ≤ 2 ^ 10)
    {tP : Nat} (htp : tP = progTpW (wMachine (List.replicate W .S) (Vt ⬝ x)).heap W)
    (S10 S9 SP : Nat → List F) (qv : EF → EF → List EF → F → List F → List F → List EF)
    (wm wc ww wp : Nat → List (EF → EF → List F)) {Lwm Lwc Lww Lwp : Nat} (hlwm : ∀ c, (wm c).length = Lwm)
    (hlwc : ∀ c, (wc c).length = Lwc) (hlww : ∀ c, (ww c).length = Lww) (hlwp : ∀ c, (wp c).length = Lwp)
    {K2 K4 : Nat} (hK2 : 0 < K2) (hK4 : 0 < K4)
    (φ : Nat → Option (List (List (List EF)) × List (List (List (List EF))) × List (List (List EF))) → Nat) {N4 : Nat} (hφ : ∀ m w, φ m w < N4)
    (hS10 : ∀ c4, ∀ x ∈ S10 c4, x ∉ cosetL 1 (bbGen 10) (2 ^ 10)) (hS9 : ∀ c4, ∀ x ∈ S9 c4, x ∉ cosetL 1 (bbGen 9) (2 ^ 9))
    (hSP : ∀ c4, ∀ x ∈ SP c4, x ∉ cosetL 1 (bbGen (tP + 1)) (2 ^ (tP + 1)))
    (hsz10 : ∀ c4, 2 * (S10 c4).length + 8 ≤ 2 ^ 10) (hsz9 : ∀ c4, 2 * (S9 c4).length + 8 ≤ 2 ^ 9)
    (hszP : ∀ c4, 2 * (SP c4).length + 8 ≤ 2 ^ (tP + 1)) {ncw : Nat} (αd : Nat → EF) {B4 : Nat}
    (hB4 : sumTo K4 (fun c4 => indB (!genB (αd c4))) ≤ B4) (fri : Nat → EF → EF → List (EF → EF) → V) (hncw : 4 ≤ ncw)
    (NR2 : Nat) (Rb : Nat → EF → EF → Nat → List (EF → EF)) (Ro : Nat → EF → EF → Nat → Wv)
    {NS1 NS2 NS3 n1 n2 n3 : Nat}
    (Com1 : List (List (List F)) → Nat → Nat) (Pf1 : Nat → List (List (List F)) → Nat → P1) {η : Nat} (hc1 : ComHidesA NS1 η Com1)
    (hp1 : ∀ c4, ComPfHidesA NS1 η Com1 (Pf1 c4) (opF ((wGroups tP (S10 c4) (S9 c4) (SP c4) EF.zero qv).map (·.base.S)) [0, 2, 4, 6]))
    (hr1 : ∀ d σ, Com1 d σ < n1) (d1 : List (List (List F)))
    (Com2 : List (List (List F)) → Nat → Nat) (Pf2 : Nat → List (List (List F)) → Nat → P2) (hc2 : ComHides NS2 Com2)
    (hp2 : ∀ c4, ComPfHides NS2 Com2 (Pf2 c4) (opF ((wGroups tP (S10 c4) (S9 c4) (SP c4) EF.zero qv).map (·.base.S)) [1, 3, 5, 7]))
    (hr2 : ∀ d σ, Com2 d σ < n2) (d2 : List (List (List F)))
    (Com3 : List (List (List (List F))) × List (List (List F)) → Nat → Nat)
    (Pf3 : Nat → List (List (List (List F))) × List (List (List F)) → Nat → P3) (hc3 : ComHides NS3 Com3)
    (hp3 : ∀ c4, ComPfHides NS3 Com3 (Pf3 c4) (fun d => (opQ (wSsT (S10 c4) (S9 c4) (SP c4)) d.1, opCw (wSsC tP (S10 c4) (S9 c4) (SP c4)) d.2)))
    (hr3 : ∀ d σ, Com3 d σ < n3) (d3 : List (List (List (List F))) × List (List (List F))) :
    ZKB (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo (K4 ^ N4) (fun H4 => sumTo ((Q4 * Q4) ^ n1) (fun H1 =>
      sumTo (K2 ^ (n1 * n2)) (fun H2 => sumTo (Q4 ^ (n1 * (n2 * n3))) (fun H3 => f (H1, H2, H3, H4))))))
      (K4 * (Q4 * Q4 * (K2 * Q4))) ((witFS4A η off Vt x W A k row tP S10 S9 SP qv wm wc ww wp K2 K4 φ N4 ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Pf1 Com2 Pf2 Com3 Pf3).sm 2)
      (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo K4 (fun c4 => sumTo (Q4 * Q4) (fun c1 =>
        sumTo K2 (fun c2 => sumTo Q4 (fun c3 => f (c1, c2, c3, c4))))))
      (read4 (Q4 * Q4) K2 Q4 K4 (witFS4A η off Vt x W A k row tP S10 S9 SP qv wm wc ww wp K2 K4 φ N4 ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Pf1 Com2 Pf2 Com3 Pf3).m1 (witFS4A η off Vt x W A k row tP S10 S9 SP qv wm wc ww wp K2 K4 φ N4 ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Pf1 Com2 Pf2 Com3 Pf3).m2 (witFS4A η off Vt x W A k row tP S10 S9 SP qv wm wc ww wp K2 K4 φ N4 ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Pf1 Com2 Pf2 Com3 Pf3).m3 (witFS4A η off Vt x W A k row tP S10 S9 SP qv wm wc ww wp K2 K4 φ N4 ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Pf1 Com2 Pf2 Com3 Pf3).q (witFS4A η off Vt x W A k row tP S10 S9 SP qv wm wc ww wp K2 K4 φ N4 ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Pf1 Com2 Pf2 Com3 Pf3).out)
      (fun H c xx => prog4 (Q4 * Q4) K2 Q4 K4 H ((witFS4A η off Vt x W A k row tP S10 S9 SP qv wm wc ww wp K2 K4 φ N4 ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Pf1 Com2 Pf2 Com3 Pf3).pts c xx) c) (witFS4A η off Vt x W A k row tP S10 S9 SP qv wm wc ww wp K2 K4 φ N4 ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Pf1 Com2 Pf2 Com3 Pf3).sv (witFS4A η off Vt x W A k row tP S10 S9 SP qv wm wc ww wp K2 K4 φ N4 ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Pf1 Com2 Pf2 Com3 Pf3).ε :=
  wit_fs_open4_absA off hwf hwl hW8 hA hK hlen hk htp S10 S9 SP qv wm wc ww wp hlwm hlwc hlww hlwp hK2 hK4 φ hφ hS10 hS9 hSP hsz10 hsz9 hszP αd hB4 fri hncw NR2 Rb Ro Com1 Pf1 hc1 hp1 hr1 d1 Com2 Pf2 hc2 hp2 hr2 d2 Com3 Pf3 hc3 hp3 hr3 d3

set_option maxRecDepth 100000 in
/-- **`comp_fs_open4_abs` with the first commitment hiding up to `η`**
    (`fs_open4_absA`).  One direction. -/
theorem comp_fs_open4_absA {V Wv P1 P2 P3 : Type} (off : EF → String → EF) {R Lm : Nat} (hR : R ≤ 20) {shp : BT} {Ps : List Term}
    {W : Nat} {ρ : Nat → Bool} {region : List Cell} (hrl : region.length = W)
    (hr : ∀ i c, region[i]? = some c → cellOK (BT.nleaves shp + 3 + i) c = true)
    {A : List Cell} {e : Nat → Nat} {row : Nat → Air.Row}
    (hA : AcceptsC A (cMachine ρ shp region Ps) (cHeap ρ shp region Ps).2
      (cHeap ρ shp region Ps).1.length Ps.length e row)
    (hlen : A.length = 2 ^ Lm) (hLm : Lm ≤ 20) (hK : e (Ps.length - 1) < 2 ^ R)
    (hNW : BT.nleaves shp + W ≤ 2 ^ 8)
    {tbM tbC tpP tpS : Nat} (htM : tbM + 1 = Lm) (htC : tbC + 1 = R)
    (htP : tpP = progTpC (blankM shp W Ps).heap (BT.nleaves shp) W) (htS : tpS = segTp (blankRoots shp W Ps))
    (SM SC S9 SP SS : Nat → List F) (qv : EF → EF → List EF → F → List F → List F → List EF)
    (wm wc ww wp wsg : Nat → List (EF → EF → List F)) {Lwm Lwc Lww Lwp Lwsg : Nat} (hlwm : ∀ c, (wm c).length = Lwm)
    (hlwc : ∀ c, (wc c).length = Lwc) (hlww : ∀ c, (ww c).length = Lww) (hlwp : ∀ c, (wp c).length = Lwp)
    (hlwsg : ∀ c, (wsg c).length = Lwsg)
    {K2 K4 : Nat} (hK2 : 0 < K2) (hK4 : 0 < K4)
    (φ : Nat → Option (List (List (List EF)) × List (List (List (List EF))) × List (List (List EF))) → Nat) {N4 : Nat} (hφ : ∀ m w, φ m w < N4)
    (hSM : ∀ c4, ∀ x ∈ SM c4, x ∉ cosetL 1 (bbGen (tbM + 1)) (2 ^ (tbM + 1)))
    (hSC : ∀ c4, ∀ x ∈ SC c4, x ∉ cosetL 1 (bbGen (tbC + 1)) (2 ^ (tbC + 1)))
    (hS9 : ∀ c4, ∀ x ∈ S9 c4, x ∉ cosetL 1 (bbGen 9) (2 ^ 9))
    (hSP : ∀ c4, ∀ x ∈ SP c4, x ∉ cosetL 1 (bbGen (tpP + 1)) (2 ^ (tpP + 1)))
    (hSS : ∀ c4, ∀ x ∈ SS c4, x ∉ cosetL 1 (bbGen (tpS + 1)) (2 ^ (tpS + 1)))
    (hszM : ∀ c4, 2 * (SM c4).length + 8 ≤ 2 ^ (tbM + 1)) (hszC : ∀ c4, 2 * (SC c4).length + 8 ≤ 2 ^ (tbC + 1))
    (hsz9 : ∀ c4, 2 * (S9 c4).length + 8 ≤ 2 ^ 9) (hszP : ∀ c4, 2 * (SP c4).length + 8 ≤ 2 ^ (tpP + 1))
    (hszS : ∀ c4, 2 * (SS c4).length + 8 ≤ 2 ^ (tpS + 1)) {ncw : Nat} (αd : Nat → EF) {B4 : Nat}
    (hB4 : sumTo K4 (fun c4 => indB (!genB (αd c4))) ≤ B4) (fri : Nat → EF → EF → List (EF → EF) → V) (hncw : 4 ≤ ncw)
    (NR2 : Nat) (Rb : Nat → EF → EF → Nat → List (EF → EF)) (Ro : Nat → EF → EF → Nat → Wv)
    {NS1 NS2 NS3 n1 n2 n3 : Nat}
    (Com1 : List (List (List F)) → Nat → Nat) (Pf1 : Nat → List (List (List F)) → Nat → P1) {η : Nat} (hc1 : ComHidesA NS1 η Com1)
    (hp1 : ∀ c4, ComPfHidesA NS1 η Com1 (Pf1 c4) (opF ((cGroups tbM tbC tpP tpS (SM c4) (SC c4) (S9 c4) (SP c4) (SS c4) EF.zero qv).map (·.base.S)) [0, 2, 4, 6, 8]))
    (hr1 : ∀ d σ, Com1 d σ < n1) (d1 : List (List (List F)))
    (Com2 : List (List (List F)) → Nat → Nat) (Pf2 : Nat → List (List (List F)) → Nat → P2) (hc2 : ComHides NS2 Com2)
    (hp2 : ∀ c4, ComPfHides NS2 Com2 (Pf2 c4) (opF ((cGroups tbM tbC tpP tpS (SM c4) (SC c4) (S9 c4) (SP c4) (SS c4) EF.zero qv).map (·.base.S)) [1, 3, 5, 7, 9]))
    (hr2 : ∀ d σ, Com2 d σ < n2) (d2 : List (List (List F)))
    (Com3 : List (List (List (List F))) × List (List (List F)) → Nat → Nat)
    (Pf3 : Nat → List (List (List (List F))) × List (List (List F)) → Nat → P3) (hc3 : ComHides NS3 Com3)
    (hp3 : ∀ c4, ComPfHides NS3 Com3 (Pf3 c4) (fun d => (opQ (cSsT (SM c4) (SC c4) (S9 c4) (SP c4) (SS c4)) d.1, opCw (cSsC tbM tbC tpP tpS (SM c4) (SC c4) (S9 c4) (SP c4) (SS c4)) d.2)))
    (hr3 : ∀ d σ, Com3 d σ < n3) (d3 : List (List (List (List F))) × List (List (List F))) :
    let m := blankM shp W Ps
    let roots := blankRoots shp W Ps
    let N := BT.nleaves shp
    let C := cpuTableC A row e Ps.length roots (2 ^ R)
    let Pg := progTableC m.heap N W
    let Wt := witTable A N W
    let Mm := memTableC A (cpuAirC m.hd m.stk m.heap.length roots.length m.stk) (progAirC m.heap N W)
      (witAir N W) C Pg Wt
    let NR0 := cNR off m.hd m.stk m.heap.length roots.length m.stk m.heap N W roots C Mm Wt tbM tbC tpP tpS (SM 0) (SC 0) (S9 0) (SP 0) (SS 0) EF.zero qv (wm 0) (wc 0) (ww 0) (wp 0) (wsg 0) ncw
    let pcsZ := fun (c4 c2 : Nat) (ζ : EF) t α β r => cPcs off m.hd m.stk m.heap.length roots.length m.stk m.heap N W roots C Mm Wt tbM tbC tpP tpS (SM c4) (SC c4) (S9 c4) (SP c4) (SS c4) ζ qv (wm c2) (wc c2) (ww c2) (wp c2) (wsg c2) ncw (αd c4)
      (friX (fri c4) (Rb c4) (Ro c4) (r / NR0)) t α β (r % NR0)
    let psimZ := fun (c4 c2 : Nat) (ζ : EF) α β v r => cPsim off m.hd m.stk m.heap.length roots.length m.stk m.heap N W roots C Mm Wt tbM tbC tpP tpS (SM c4) (SC c4) (S9 c4) (SP c4) (SS c4) ζ qv (wm c2) (wc c2) (ww c2) (wp c2) (wsg c2) ncw (αd c4)
      (friX (fri c4) (Rb c4) (Ro c4) (r / NR0)) α β v (r % NR0)
    let NR := NR0 * NR2
    let tabs := fun t : Nat → Tup => compTables m.hd m.stk m.heap.length roots.length m.stk m.heap N W roots
      ((C.setBlind BLA (t 1)).setBlind BLB (t 0)) (Mm.setBlind 5 (t 0)) (progTableC m.heap N W)
      (Wt.setBlind WT_BLIND (t 1)) (segsPub roots)
    let tv := fun pre β t => compViewN pre β m.hd m.stk m.heap.length roots.length m.stk N W C Mm Wt t
    let pb := fun pre β => (terminal pre β (progAirC m.heap N W) (progTableC m.heap N W),
      terminal pre β (segsAir roots) (segsPub roots))
    let ptm := fun pre β => (terminal pre β (progAirC m.heap N W) (progTableC m.heap N W)).add
      (terminal pre β (segsAir roots) (segsPub roots))
    let M := (allEntries (compTables m.hd m.stk m.heap.length roots.length m.stk m.heap N W roots C Mm
      (progTableC m.heap N W) Wt (segsPub roots))).length
    let q0 := cGroups tbM tbC tpP tpS (SM 0) (SC 0) (S9 0) (SP 0) (SS 0) EF.zero qv
    let qZ := fun (c4 : Nat) (ζ : EF) => cGroups tbM tbC tpP tpS (SM c4) (SC c4) (S9 c4) (SP c4) (SS c4) ζ qv
    let Ss := fun c4 => (qZ c4 EF.zero).map (·.base.S)
    let ks := cKs m.hd m.stk m.heap.length roots.length m.stk m.heap N W roots
    let cols := cCols off m.hd m.stk m.heap.length roots.length m.stk m.heap N W roots C Mm Wt
    let tqZ := fun (c4 c2 : Nat) (ζ : EF) => (cTs off m.hd m.stk m.heap.length roots.length m.stk m.heap N W roots C Mm Wt tbM tbC tpP tpS (SM c4) (SC c4) (S9 c4) (SP c4) (SS c4) ζ qv (wm c2) (wc c2) (ww c2) (wp c2) (wsg c2)).map Prod.fst
    let qdZ := fun (c4 c2 : Nat) (ζ : EF) (t : Nat → Tup) (α β : EF) (ms : List F) =>
      (cTs off m.hd m.stk m.heap.length roots.length m.stk m.heap N W roots C Mm Wt tbM tbC tpP tpS (SM c4) (SC c4) (S9 c4) (SP c4) (SS c4) ζ qv (wm c2) (wc c2) (ww c2) (wp c2) (wsg c2)).map (fun p => p.2 t α β ms)
    let SsT := fun c4 => (tqZ c4 0 EF.zero).map (·.S)
    let SsC := fun c4 => (tabsInfo ncw (tqZ c4 0 EF.zero)).map (·.S)
    let mk1 := [0, 2, 4, 6, 8]
    let mk2 := [1, 3, 5, 7, 9]
    let main1 := fun (t : Nat → Tup) (r : Nat) => mainF2 q0 ks cols (tqZ 0 0 EF.zero) ncw mk1 t (r % NR0)
    let main2 := fun (c1 : Nat) (t : Nat → Tup) (r : Nat) =>
      mainP2 q0 ks cols (tqZ 0 0 EF.zero) ncw mk2 t (efOf (c1 / Q4)) (efOf (c1 % Q4)) (r % NR0)
    let main3 := fun (c1 c2 : Nat) (t : Nat → Tup) (r : Nat) =>
      (tabsPolys (tqZ 0 c2 EF.zero) (qdZ 0 c2 EF.zero t (efOf (c1 / Q4)) (efOf (c1 % Q4))
          (msF q0 ks (tqZ 0 c2 EF.zero) ncw (r % NR0))) (crF q0 ks (tqZ 0 c2 EF.zero) ncw (r % NR0)),
       tabsCws ncw (tqZ 0 c2 EF.zero) (ccF q0 ks (tqZ 0 c2 EF.zero) ncw (r % NR0)))
    let vS := fun (α β : EF) (t : Nat → Tup) => viewT β (fun k => prefixOf α (off β) (chainBus k)) (fun _ => false)
      chainPar 3 (xrefN (ptm (prefixOf α (off β)) β)) t
    let sop1 := fun (c4 c2 c3 r : Nat) (_ : Nat → Tup) =>
      opF (Ss c4) mk1 (mainZ2 (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw mk1 (r % NR0))
    let sop2 := fun (c4 c2 c3 _ r : Nat) (_ : Nat → Tup) =>
      opF (Ss c4) mk2 (mainZ2 (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw mk2 (r % NR0))
    let sop3 := fun (c4 c2 c3 c1 r : Nat) (t : Nat → Tup) =>
      (opQ (SsT c4) (tabsPolys (tqZ c4 c2 (efOf c3)) (canonT (tqZ c4 c2 (efOf c3)) (efOf (c1 / Q4)) (efOf (c1 % Q4))
         (vS (efOf (c1 / Q4)) (efOf (c1 % Q4)) t)
         (openMulti ((qZ c4 (efOf c3)).map QGroup.ext) ((((qZ c4 (efOf c3)).map QGroup.ext).zip ks).map
           (fun p => List.replicate p.2 (List.replicate p.1.n (0 : F))))
           (msF (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw (r % NR0))))
         (crF (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw (r % NR0))),
       opCw (SsC c4) (tabsCws ncw (tqZ c4 c2 (efOf c3)) (ccF (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw (r % NR0))))
    let ov1 : Nat → TViewN (PcsPV (V × Wv)) (EF × EF) → Option (List (List (List F))) := fun c4 v => match v with
      | some (pv, _) => some (ovF2 (Ss c4) mk1 pv)
      | none => none
    let ov2 : Nat → TViewN (PcsPV (V × Wv)) (EF × EF) → Option (List (List (List F))) := fun c4 v => match v with
      | some (pv, _) => some (ovF2 (Ss c4) mk2 pv)
      | none => none
    let ov3 : Nat → TViewN (PcsPV (V × Wv)) (EF × EF) → Option (List (List (List (List F))) × List (List (List F))) :=
      fun _ v => match v with
      | some (pv, _) => some (ovQ pv, cwQ 10 pv)
      | none => none
    let rvF := fun (c4 c2 c3 : Nat) (α β : EF) (r : Nat) (t : Nat → Tup) =>
      realVN off tabs tv pb (pcsZ c4 c2 (efOf c3)) α β r t
    let svF := fun (c4 c2 c3 : Nat) (α β : EF) (r : Nat) (t : Nat → Tup) =>
      simVN off pb chainBus (fun _ => false) chainPar 3 ptm (psimZ c4 c2 (efOf c3)) α β r t
    let ozF : TViewN (PcsPV (V × Wv)) (EF × EF) → Option (List (List (List EF)) × List (List (List (List EF))) × List (List (List EF))) := fun v => match v with
      | some (pv, _) => some (pv.1.1.map (fun g => g.1.map Prod.snd), pv.1.2.map (List.map (List.map Prod.snd)),
        pv.2.1.map (List.map Prod.snd))
      | none => none
    let op3 := fun (c4 : Nat) (d : List (List (List (List F))) × List (List (List F))) =>
      (opQ (SsT c4) d.1, opCw (SsC c4) d.2)
    let sd3 := fun (c4 : Nat) (o : List (List (List (List F))) × List (List (List F))) =>
      (sdQ (SsT c4) o.1, sdCw (SsC c4) o.2)
    let sm := fun (g : Nat × Nat × Nat × (Nat → Tup) → Nat) =>
      sumTo NS1 (fun σ1 => sumTo (NS2 * NS3) (fun σ => sumTo NR (fun r => sumN 2 (fun t => g (σ1, σ, r, t)))))
    let m1 := fun (x : Nat × Nat × Nat × (Nat → Tup)) => Com1 (main1 x.2.2.2 x.2.2.1) x.1
    let m2 := fun (c1 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      m1 x + n1 * Com2 (main2 c1 x.2.2.2 x.2.2.1) (x.2.1 % NS2)
    let m3 := fun (c1 c2 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      m1 x + n1 * comPair NS2 n2 Com2 Com3 (main2 c1 x.2.2.2 x.2.2.1, main3 c1 c2 x.2.2.2 x.2.2.1) x.2.1
    let rvo := fun (c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      ((ov1 c4 (rvF c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)).map (fun _ => Pf1 c4 (main1 x.2.2.2 x.2.2.1) x.1),
       (ovPair (ov2 c4) (ov3 c4) (rvF c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)).map
         (fun _ => pfPair NS2 (Pf2 c4) (Pf3 c4) (main2 c1 x.2.2.2 x.2.2.1, main3 c1 c2 x.2.2.2 x.2.2.1) x.2.1),
       rvF c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)
    let s1 := fun (c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) => Com1 (sdF (Ss c4) mk1 (sop1 c4 c2 c3 x.2.2.1 x.2.2.2)) x.1
    let s2 := fun (c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      s1 c4 c1 c2 c3 x + n1 * Com2 (sdF (Ss c4) mk2 (sop2 c4 c2 c3 c1 x.2.2.1 x.2.2.2)) (x.2.1 % NS2)
    let s3 := fun (c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      s1 c4 c1 c2 c3 x + n1 * comPair NS2 n2 Com2 Com3
        (sdF (Ss c4) mk2 (sop2 c4 c2 c3 c1 x.2.2.1 x.2.2.2), sd3 c4 (sop3 c4 c2 c3 c1 x.2.2.1 x.2.2.2)) x.2.1
    let svo := fun (c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      (some (Pf1 c4 (sdF (Ss c4) mk1 (sop1 c4 c2 c3 x.2.2.1 x.2.2.2)) x.1),
       some (pfPair NS2 (Pf2 c4) (Pf3 c4) (sdF (Ss c4) mk2 (sop2 c4 c2 c3 c1 x.2.2.1 x.2.2.2), sd3 c4 (sop3 c4 c2 c3 c1 x.2.2.1 x.2.2.2)) x.2.1),
       svF c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)
    let sm4 := fun (g : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup)) → Nat) =>
      sumTo ((Q4 * Q4) ^ n1) (fun H1 => sumTo (K2 ^ (n1 * n2)) (fun H2 =>
        sumTo (Q4 ^ (n1 * (n2 * n3))) (fun H3 => sm (fun x => g (H1, H2, H3, x)))))
    let r1 := fun (y : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup))) => rget (Q4 * Q4) (m1 y.2.2.2) y.1
    let r2 := fun (y : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup))) => rget K2 (m2 (r1 y) y.2.2.2) y.2.1
    let r3 := fun (y : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup))) => rget Q4 (m3 (r1 y) (r2 y) y.2.2.2) y.2.2.1
    let Mq := fun (y : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup))) => φ (m3 (r1 y) (r2 y) y.2.2.2)
      (ozF (rvF 0 (r2 y) (r3 y) (efOf (r1 y / Q4)) (efOf (r1 y % Q4)) y.2.2.2.2.2.1 y.2.2.2.2.2.2))
    let ST := fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo (K4 ^ N4) (fun H4 => sumTo ((Q4 * Q4) ^ n1) (fun H1 =>
      sumTo (K2 ^ (n1 * n2)) (fun H2 => sumTo (Q4 ^ (n1 * (n2 * n3))) (fun H3 => f (H1, H2, H3, H4)))))
    let SC := fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo K4 (fun c4 => sumTo (Q4 * Q4) (fun c1 =>
      sumTo K2 (fun c2 => sumTo Q4 (fun c3 => f (c1, c2, c3, c4)))))
    let rvT := fun (H : Nat × Nat × Nat × Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      (m1 x, m2 (r1 (H.1, H.2.1, H.2.2.1, x)) x, m3 (r1 (H.1, H.2.1, H.2.2.1, x)) (r2 (H.1, H.2.1, H.2.2.1, x)) x,
       rvo (rget K4 (Mq (H.1, H.2.1, H.2.2.1, x)) H.2.2.2) (r1 (H.1, H.2.1, H.2.2.1, x)) (r2 (H.1, H.2.1, H.2.2.1, x))
         (r3 (H.1, H.2.1, H.2.2.1, x)) x)
    let pgT := fun (H : Nat × Nat × Nat × Nat) (c : Nat × Nat × Nat × Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      (rset (Q4 * Q4) (s1 c.2.2.2 c.1 c.2.1 c.2.2.1 x) H.1 c.1, rset K2 (s2 c.2.2.2 c.1 c.2.1 c.2.2.1 x) H.2.1 c.2.1,
       rset Q4 (s3 c.2.2.2 c.1 c.2.1 c.2.2.1 x) H.2.2.1 c.2.2.1,
       rset K4 (φ (s3 c.2.2.2 c.1 c.2.1 c.2.2.1 x) (ozF (svF c.2.2.2 c.2.1 c.2.2.1 (efOf (c.1 / Q4)) (efOf (c.1 % Q4))
         x.2.2.1 x.2.2.2))) H.2.2.2 c.2.2.2)
    let svT := fun (c : Nat × Nat × Nat × Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      (s1 c.2.2.2 c.1 c.2.1 c.2.2.1 x, s2 c.2.2.2 c.1 c.2.1 c.2.2.1 x, s3 c.2.2.2 c.1 c.2.1 c.2.2.1 x,
       svo c.2.2.2 c.1 c.2.1 c.2.2.1 x)
    ∀ E : Nat × Nat × Nat × Nat → Nat × Nat × Nat × (Option P1 × Option (P2 × P3) × TViewN (PcsPV (V × Wv)) (EF × EF)) → Bool,
    K4 * (Q4 * Q4 * (K2 * Q4)) * ST (fun H => sm (fun x => indB (E H (rvT H x)))) ≤
      ST (fun H => SC (fun c => sm (fun x => indB (E (pgT H c x) (svT c x))))) +
      (K4 ^ N4 * (K4 * ((Q4 * Q4) ^ n1 * (K2 ^ (n1 * n2) * (Q4 ^ (n1 * (n2 * n3)) *
          (K2 * (Q4 * (NS1 * (NS2 * NS3 * (Q4 * (NR * (Q4 ^ 2 * M)) + Q4 * (Q4 * (Q4 ^ 2 * 0)))) +
            Q4 * Q4 * (NS2 * NS3 * (NR * (Q4 ^ 2 * η))))) +
            (Q4 * (P * P) * (K2 * Q4) + Q4 * Q4 * (K2 * (P * P))) * (NS1 * (NS2 * NS3 * (NR * (Q4 ^ 2 * 1)))))))) +
            B4 * (Q4 * Q4 * (K2 * Q4) * sm4 (fun _ => 1)))) := by
  intro m roots N C Pg Wt Mm NR0 pcsZ psimZ NR tabs tv pb ptm M q0 qZ Ss ks cols tqZ qdZ SsT SsC mk1 mk2 main1 main2 main3 vS sop1 sop2 sop3 ov1 ov2 ov3 rvF svF ozF op3 sd3
  obtain ⟨hbal, hun⟩ := comp_honest_zk hR hrl hr hA hlen hLm hK hNW
  obtain ⟨sc, sms, sw, hWh, _⟩ := comp_run_sats hR hrl hr hA hlen hLm hK hNW
  obtain ⟨p1, p2, s1, s2⟩ := comp_pub_heights hR hrl hA hlen hLm hK
  rw [← htP] at p1 p2
  rw [← htS] at s1 s2
  have hM : Mm.h = 2 ^ (tbM + 1) := by rw [htM]; exact hlen
  have hC : C.h = 2 ^ (tbC + 1) := by rw [htC]; rfl
  have hSw := fun (c4 c2 c3 : Nat) => comp_same_w off m.hd m.stk m.heap.length roots.length m.stk m.heap N W roots C Mm Wt tbM tbC tpP tpS (SM c4) (SC c4) (S9 c4) (SP c4) (SS c4) (efOf c3) EF.zero qv (wm c2) (wc c2) (ww c2) (wp c2) (wsg c2) (wm 0) (wc 0) (ww 0) (wp 0) (wsg 0) ncw (by rw [hlwm, hlwm]) (by rw [hlwc, hlwc]) (by rw [hlww, hlww]) (by rw [hlwp, hlwp]) (by rw [hlwsg, hlwsg])
  have hSz := fun (c4 c2 c3 : Nat) => comp_same_w off m.hd m.stk m.heap.length roots.length m.stk m.heap N W roots C Mm Wt tbM tbC tpP tpS (SM c4) (SC c4) (S9 c4) (SP c4) (SS c4) (efOf c3) EF.zero qv (wm c2) (wc c2) (ww c2) (wp c2) (wsg c2) (wm c2) (wc c2) (ww c2) (wp c2) (wsg c2) ncw rfl rfl rfl rfl rfl
  have hS0 := fun (c4 c2 : Nat) => comp_same_w off m.hd m.stk m.heap.length roots.length m.stk m.heap N W roots C Mm Wt tbM tbC tpP tpS (SM c4) (SC c4) (S9 c4) (SP c4) (SS c4) EF.zero EF.zero qv (wm c2) (wc c2) (ww c2) (wp c2) (wsg c2) (wm 0) (wc 0) (ww 0) (wp 0) (wsg 0) ncw (by rw [hlwm, hlwm]) (by rw [hlwc, hlwc]) (by rw [hlww, hlww]) (by rw [hlwp, hlwp]) (by rw [hlwsg, hlwsg])
  have hSd := fun (c4 c2 c3 : Nat) => comp_same_d off m.hd m.stk m.heap.length roots.length m.stk m.heap N W roots C Mm Wt tbM tbC tpP tpS (SM c4) (SC c4) (S9 c4) (SP c4) (SS c4) (SM 0) (SC 0) (S9 0) (SP 0) (SS 0) (efOf c3) EF.zero qv (wm c2) (wc c2) (ww c2) (wp c2) (wsg c2) (wm 0) (wc 0) (ww 0) (wp 0) (wsg 0) (by rw [hlwm, hlwm]) (by rw [hlwc, hlwc]) (by rw [hlww, hlww]) (by rw [hlwp, hlwp]) (by rw [hlwsg, hlwsg])
  have hSdz := fun (c4 c2 c3 : Nat) => comp_same_d off m.hd m.stk m.heap.length roots.length m.stk m.heap N W roots C Mm Wt tbM tbC tpP tpS (SM c4) (SC c4) (S9 c4) (SP c4) (SS c4) (SM 0) (SC 0) (S9 0) (SP 0) (SS 0) (efOf c3) EF.zero qv (wm c2) (wc c2) (ww c2) (wp c2) (wsg c2) (wm c2) (wc c2) (ww c2) (wp c2) (wsg c2) rfl rfl rfl rfl rfl
  have hb : ∀ c4 c2 c3, genB (αd c4) = true → genB (efOf c3) = true →
      (∀ E' : TViewN (PcsPV (V × Wv)) (EF × EF) → Bool,
        tsumN NR 2 (fun α β r t => indB (genB β && E' (rvF c4 c2 c3 α β r t))) ≤
          tsumN NR 2 (fun α β r t => indB (genB β && E' (svF c4 c2 c3 α β r t))) + Q4 * (NR * (Q4 ^ 2 * M)) +
            Q4 * (Q4 * (Q4 ^ 2 * 0))) ∧
      (∀ E' : TViewN (PcsPV (V × Wv)) (EF × EF) → Bool,
        tsumN NR 2 (fun α β r t => indB (genB β && E' (svF c4 c2 c3 α β r t))) ≤
          tsumN NR 2 (fun α β r t => indB (genB β && E' (rvF c4 c2 c3 α β r t))) + Q4 * (NR * (Q4 ^ 2 * M)) +
            Q4 * (Q4 * (Q4 ^ 2 * 0))) := fun c4 c2 c3 hg4 hg => by
    have hgz := (genB_iff _).1 hg
    have hgα := (genB_iff _).1 hg4
    have hpcs := comp_pcsX (heap := m.heap) (ζ := efOf c3) (roots := roots) off sc sms sw (by omega) (by omega) (by omega) (by omega)
      hM hC hWh p2 s2 qv (wm c2) (wc c2) (ww c2) (wp c2) (wsg c2) (hSM c4) (hSC c4) (hS9 c4) (hSP c4) (hSS c4) (hszM c4) (hszC c4) (hsz9 c4) (hszP c4) (hszS c4) (generic_ofF_ne hgz) (mz_generic hgz) (fri c4) (mz_generic hgα) (generic_apow_ne hgα) hncw NR2 (Rb c4) (Ro c4)
    have hNR : cNR off m.hd m.stk m.heap.length roots.length m.stk m.heap N W roots C Mm Wt tbM tbC tpP tpS (SM c4) (SC c4) (S9 c4) (SP c4) (SS c4) (efOf c3) qv (wm c2) (wc c2) (ww c2) (wp c2) (wsg c2) ncw = cNR off m.hd m.stk m.heap.length roots.length m.stk m.heap N W roots C Mm Wt tbM tbC tpP tpS (SM 0) (SC 0) (S9 0) (SP 0) (SS 0) EF.zero qv (wm 0) (wc 0) (ww 0) (wp 0) (wsg 0) ncw := by
      unfold cNR; rw [(hSd c4 c2 c3).n1, (hSd c4 c2 c3).n2]
    rw [hNR] at hpcs
    exact ⟨fun E' => (comp_transcriptG off NR 0 (pcsZ c4 c2 (efOf c3)) (psimZ c4 c2 (efOf c3)) hbal hun hpcs E').1,
      fun E' => (comp_transcriptG off NR 0 (pcsZ c4 c2 (efOf c3)) (psimZ c4 c2 (efOf c3)) hbal hun hpcs E').2⟩
  have hlen8 : ∀ (c4 : Nat) (ζ : EF) t α β, (cols t α β).map List.length = (cols t EF.zero EF.zero).map List.length :=
    fun c4 ζ t α β => by
      rw [(cCols_shaped off m.hd m.stk m.heap.length roots.length m.stk hM hC hWh p2 s2
          (SM c4) (SC c4) (S9 c4) (SP c4) (SS c4) ζ qv t α β).2,
        (cCols_shaped off m.hd m.stk m.heap.length roots.length m.stk hM hC hWh p2 s2
          (SM c4) (SC c4) (S9 c4) (SP c4) (SS c4) ζ qv t EF.zero EF.zero).2]
  have hmk1 : ∀ k ∈ mk1, k < 10 ∧ ∀ t α β, k < (cols t α β).length ∧
      (cols t α β).getD k [] = (cols t EF.zero EF.zero).getD k [] := by
    intro k hk
    have hk' := hk
    simp only [mk1, List.mem_cons, List.not_mem_nil, or_false] at hk'
    have hkn : k < 10 := by rcases hk' with rfl | rfl | rfl | rfl | rfl <;> decide
    exact ⟨hkn, fun t α β => ⟨hkn, compCols_main off m.hd m.stk m.heap.length roots.length m.stk m.heap N W roots C Mm Wt t α β
      EF.zero EF.zero k hk⟩⟩
  have hmk2 : ∀ k ∈ mk2, k < 10 ∧ ∀ t α β, k < (cols t α β).length := by
    intro k hk
    simp only [mk2, List.mem_cons, List.not_mem_nil, or_false] at hk
    have hkn : k < 10 := by rcases hk with rfl | rfl | rfl | rfl | rfl <;> decide
    exact ⟨hkn, fun _ _ _ => hkn⟩
  have hvo1 : ∀ c4 c2 c3 c r t, rvF c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t = none ∨
      ov1 c4 (rvF c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (opF (Ss c4) mk1 (main1 t r)) := by
    intro c4 c2 c3 c r t
    show realVN off tabs tv pb (pcsZ c4 c2 (efOf c3)) _ _ r t = none ∨
      ov1 c4 (realVN off tabs tv pb (pcsZ c4 c2 (efOf c3)) _ _ r t) = _
    unfold realVN
    split
    · exact .inl rfl
    · have e := pcsFri_ov2 off (fun pre β t => compViewN pre β m.hd m.stk m.heap.length roots.length m.stk N W C Mm Wt t) (cGroups tbM tbC tpP tpS (SM c4) (SC c4) (S9 c4) (SP c4) (SS c4) (efOf c3) qv) ks cols ((cTs off m.hd m.stk m.heap.length roots.length m.stk m.heap N W roots C Mm Wt tbM tbC tpP tpS (SM c4) (SC c4) (S9 c4) (SP c4) (SS c4) (efOf c3) qv (wm c2) (wc c2) (ww c2) (wp c2) (wsg c2)).map Prod.fst) (fun t α β ms => (cTs off m.hd m.stk m.heap.length roots.length m.stk m.heap N W roots C Mm Wt tbM tbC tpP tpS (SM c4) (SC c4) (S9 c4) (SP c4) (SS c4) (efOf c3) qv (wm c2) (wc c2) (ww c2) (wp c2) (wsg c2)).map fun p => p.2 t α β ms) ncw (αd c4)
        (friX (fri c4) (Rb c4) (Ro c4) (r / NR0)) mk1 hmk1 (hlen8 c4 (efOf c3)) rfl t (efOf (c / Q4)) (efOf (c % Q4)) (r % NR0)
      rw [(hSd c4 c2 c3).dataF2 cols mk1 t (r % NR0), (hSw c4 c2 c3).S] at e
      exact .inr (congrArg some e)
  have hvo2 : ∀ c4 c2 c3 c r t, rvF c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t = none ∨
      ov2 c4 (rvF c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (opF (Ss c4) mk2 (main2 c t r)) := by
    intro c4 c2 c3 c r t
    show realVN off tabs tv pb (pcsZ c4 c2 (efOf c3)) _ _ r t = none ∨
      ov2 c4 (realVN off tabs tv pb (pcsZ c4 c2 (efOf c3)) _ _ r t) = _
    unfold realVN
    split
    · exact .inl rfl
    · have e := pcsFri_ovP off (fun pre β t => compViewN pre β m.hd m.stk m.heap.length roots.length m.stk N W C Mm Wt t) (cGroups tbM tbC tpP tpS (SM c4) (SC c4) (S9 c4) (SP c4) (SS c4) (efOf c3) qv) ks cols ((cTs off m.hd m.stk m.heap.length roots.length m.stk m.heap N W roots C Mm Wt tbM tbC tpP tpS (SM c4) (SC c4) (S9 c4) (SP c4) (SS c4) (efOf c3) qv (wm c2) (wc c2) (ww c2) (wp c2) (wsg c2)).map Prod.fst) (fun t α β ms => (cTs off m.hd m.stk m.heap.length roots.length m.stk m.heap N W roots C Mm Wt tbM tbC tpP tpS (SM c4) (SC c4) (S9 c4) (SP c4) (SS c4) (efOf c3) qv (wm c2) (wc c2) (ww c2) (wp c2) (wsg c2)).map fun p => p.2 t α β ms) ncw (αd c4)
        (friX (fri c4) (Rb c4) (Ro c4) (r / NR0)) mk2 hmk2 rfl t (efOf (c / Q4)) (efOf (c % Q4)) (r % NR0)
      rw [(hSd c4 c2 c3).dataP2 cols mk2 t _ _ (r % NR0), (hSw c4 c2 c3).S] at e
      exact .inr (congrArg some e)
  have hvo3 : ∀ c4 c2 c3 c r t, rvF c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t = none ∨
      ov3 c4 (rvF c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (op3 c4 (main3 c c2 t r)) := by
    intro c4 c2 c3 c r t
    show realVN off tabs tv pb (pcsZ c4 c2 (efOf c3)) _ _ r t = none ∨
      ov3 c4 (realVN off tabs tv pb (pcsZ c4 c2 (efOf c3)) _ _ r t) = _
    unfold realVN
    split
    · exact .inl rfl
    · rename_i hab
      have hab' : Aborts (prefixOf (efOf (c / Q4)) (off (efOf (c % Q4)))) (efOf (c % Q4)) (tabs t) = false := by
        cases h : Aborts (prefixOf (efOf (c / Q4)) (off (efOf (c % Q4)))) (efOf (c % Q4)) (tabs t)
        · rfl
        · exact absurd h hab
      have e0 := pcsFri_ovR2 off (fun pre β t => compViewN pre β m.hd m.stk m.heap.length roots.length m.stk N W C Mm Wt t) (cGroups tbM tbC tpP tpS (SM c4) (SC c4) (S9 c4) (SP c4) (SS c4) (efOf c3) qv) ks cols ((cTs off m.hd m.stk m.heap.length roots.length m.stk m.heap N W roots C Mm Wt tbM tbC tpP tpS (SM c4) (SC c4) (S9 c4) (SP c4) (SS c4) (efOf c3) qv (wm c2) (wc c2) (ww c2) (wp c2) (wsg c2)).map Prod.fst) (fun t α β ms => (cTs off m.hd m.stk m.heap.length roots.length m.stk m.heap N W roots C Mm Wt tbM tbC tpP tpS (SM c4) (SC c4) (S9 c4) (SP c4) (SS c4) (efOf c3) qv (wm c2) (wc c2) (ww c2) (wp c2) (wsg c2)).map fun p => p.2 t α β ms) ncw (αd c4)
        (friX (fri c4) (Rb c4) (Ro c4) (r / NR0)) mk2 hmk2 rfl t (efOf (c / Q4)) (efOf (c % Q4)) (r % NR0)
      have e := congrArg Prod.snd e0
      rw [(hSz c4 c2 c3).tS, (hSz c4 c2 c3).iS, tabsPolys_congr _ _ _ _ (hSdz c4 c2 c3).shape,
        tabsCws_congr ncw _ _ _ (hSdz c4 c2 c3).shape, (hSdz c4 c2 c3).cr (r % NR0), (hSdz c4 c2 c3).cc (r % NR0),
        (hSdz c4 c2 c3).ms (r % NR0), (hS0 c4 c2).tS, (hS0 c4 c2).iS,
        comp_data_q off m.hd m.stk m.heap.length roots.length m.stk m.heap N W roots C Mm Wt tbM tbC tpP tpS (SM c4) (SC c4) (S9 c4) (SP c4) (SS c4) (SM 0) (SC 0) (S9 0) (SP 0) (SS 0) (efOf c3) EF.zero
          qv (wm c2) (wc c2) (ww c2) (wp c2) (wsg c2) t _ _ _ hab'] at e
      exact .inr (congrArg some e)
  have hsvo1 : ∀ c4 c2 c3 c r t, ov1 c4 (svF c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (sop1 c4 c2 c3 r t) :=
    fun c4 c2 c3 c r t => congrArg some (psimFri_ov2 (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw (αd c4) _ mk1
      (fun k hk => (hmk1 k hk).1) rfl _ _ _ (r % NR0))
  have hsvo2 : ∀ c4 c2 c3 c r t, ov2 c4 (svF c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) =
      some (sop2 c4 c2 c3 c r t) :=
    fun c4 c2 c3 c r t => congrArg some (psimFri_ov2 (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw (αd c4) _ mk2
      (fun k hk => (hmk2 k hk).1) rfl _ _ _ (r % NR0))
  have hsvo3 : ∀ c4 c2 c3 c r t, ov3 c4 (svF c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) =
      some (sop3 c4 c2 c3 c r t) := by
    intro c4 c2 c3 c r t
    have e0 := psimFri_ovR2 (cGroups tbM tbC tpP tpS (SM c4) (SC c4) (S9 c4) (SP c4) (SS c4) (efOf c3) qv) ks ((cTs off m.hd m.stk m.heap.length roots.length m.stk m.heap N W roots C Mm Wt tbM tbC tpP tpS (SM c4) (SC c4) (S9 c4) (SP c4) (SS c4) (efOf c3) qv (wm c2) (wc c2) (ww c2) (wp c2) (wsg c2)).map Prod.fst) ncw (αd c4) (friX (fri c4) (Rb c4) (Ro c4) (r / NR0)) mk2
      (fun k hk => (hmk2 k hk).1) rfl (efOf (c / Q4)) (efOf (c % Q4)) (vS (efOf (c / Q4)) (efOf (c % Q4)) t) (r % NR0)
    have e := congrArg Prod.snd e0
    rw [(hSw c4 c2 c3).tS, (hSw c4 c2 c3).iS] at e
    exact congrArg some e
  have hsd1 : ∀ c4 t r, opF (Ss c4) mk1 (sdF (Ss c4) mk1 (opF (Ss c4) mk1 (main1 t r))) = opF (Ss c4) mk1 (main1 t r) :=
    fun c4 t r => opF_sdF _ _ _
  have hsd2 : ∀ c4 c t r, opF (Ss c4) mk2 (sdF (Ss c4) mk2 (opF (Ss c4) mk2 (main2 c t r))) =
      opF (Ss c4) mk2 (main2 c t r) :=
    fun c4 c t r => opF_sdF _ _ _
  have hsd3 : ∀ c4 c c' t r, op3 c4 (sd3 c4 (op3 c4 (main3 c c' t r))) = op3 c4 (main3 c c' t r) := fun c4 c c' t r =>
    congrArg Prod.snd (op2_sd2 (Ss c4) [] (SsT c4) (SsC c4) (fun _ => []) (main3 c c' t r).1 (main3 c c' t r).2)
  have hp3' : ∀ c4, ComPfHides NS3 Com3 (Pf3 c4) (op3 c4) := by
    intro c4
    have e1 : SsT c4 = cSsT (SM c4) (SC c4) (S9 c4) (SP c4) (SS c4) := comp_SsT off m.hd m.stk m.heap.length roots.length m.stk m.heap N W roots C Mm Wt tbM tbC tpP tpS (SM c4) (SC c4) (S9 c4) (SP c4) (SS c4) EF.zero qv (wm 0) (wc 0) (ww 0) (wp 0) (wsg 0)
    have e2 : SsC c4 = cSsC tbM tbC tpP tpS (SM c4) (SC c4) (S9 c4) (SP c4) (SS c4) := comp_SsC off m.hd m.stk m.heap.length roots.length m.stk m.heap N W roots C Mm Wt tbM tbC tpP tpS (SM c4) (SC c4) (S9 c4) (SP c4) (SS c4) EF.zero qv (wm 0) (wc 0) (ww 0) (wp 0) (wsg 0) ncw
    show ComPfHides NS3 Com3 (Pf3 c4) (fun d => (opQ (SsT c4) d.1, opCw (SsC c4) d.2))
    rw [e1, e2]; exact hp3 c4
  have hoz : ∀ c4 c2 c3 α β r t, ozF (rvF c4 c2 c3 α β r t) = ozF (rvF 0 c2 c3 α β r t) := by
    intro c4 c2 c3 α β r t
    simp only [rvF]
    unfold realVN
    cases hA : Aborts (prefixOf α (off β)) β (tabs t)
    · simp only [Bool.false_eq_true, ↓reduceIte, ozF, Option.some.injEq, Prod.mk.injEq]
      have hd := comp_same_d off m.hd m.stk m.heap.length roots.length m.stk m.heap N W roots C Mm Wt tbM tbC tpP tpS (SM c4) (SC c4) (S9 c4) (SP c4) (SS c4) (SM 0) (SC 0) (S9 0) (SP 0) (SS 0) (efOf c3) (efOf c3) qv (wm c2) (wc c2) (ww c2) (wp c2) (wsg c2) (wm c2) (wc c2) (ww c2) (wp c2) (wsg c2) rfl rfl rfl rfl rfl
      refine ⟨pcsFri_ood off (fun pre β t => compViewN pre β m.hd m.stk m.heap.length roots.length m.stk N W C Mm Wt t) (cGroups tbM tbC tpP tpS (SM c4) (SC c4) (S9 c4) (SP c4) (SS c4) (efOf c3) qv) (cGroups tbM tbC tpP tpS (SM 0) (SC 0) (S9 0) (SP 0) (SS 0) (efOf c3) qv) ks cols
        ((cTs off m.hd m.stk m.heap.length roots.length m.stk m.heap N W roots C Mm Wt tbM tbC tpP tpS (SM c4) (SC c4) (S9 c4) (SP c4) (SS c4) (efOf c3) qv (wm c2) (wc c2) (ww c2) (wp c2) (wsg c2)).map Prod.fst) ((cTs off m.hd m.stk m.heap.length roots.length m.stk m.heap N W roots C Mm Wt tbM tbC tpP tpS (SM 0) (SC 0) (S9 0) (SP 0) (SS 0) (efOf c3) qv (wm c2) (wc c2) (ww c2) (wp c2) (wsg c2)).map Prod.fst) _ _ ncw (αd c4) (αd 0) _ _
        hd rfl rfl t α β (r % NR0), pcsFri_oodT off (fun pre β t => compViewN pre β m.hd m.stk m.heap.length roots.length m.stk N W C Mm Wt t) (cGroups tbM tbC tpP tpS (SM c4) (SC c4) (S9 c4) (SP c4) (SS c4) (efOf c3) qv) (cGroups tbM tbC tpP tpS (SM 0) (SC 0) (S9 0) (SP 0) (SS 0) (efOf c3) qv) ks cols
        ((cTs off m.hd m.stk m.heap.length roots.length m.stk m.heap N W roots C Mm Wt tbM tbC tpP tpS (SM c4) (SC c4) (S9 c4) (SP c4) (SS c4) (efOf c3) qv (wm c2) (wc c2) (ww c2) (wp c2) (wsg c2)).map Prod.fst) ((cTs off m.hd m.stk m.heap.length roots.length m.stk m.heap N W roots C Mm Wt tbM tbC tpP tpS (SM 0) (SC 0) (S9 0) (SP 0) (SS 0) (efOf c3) qv (wm c2) (wc c2) (ww c2) (wp c2) (wsg c2)).map Prod.fst) _ _ ncw (αd c4) (αd 0) _ _
        hd (by simp only [cTs, bbTab, airQTabG, List.map_cons, List.map_nil]) t α β (r % NR0)
        (comp_data_q off m.hd m.stk m.heap.length roots.length m.stk m.heap N W roots C Mm Wt tbM tbC tpP tpS (SM c4) (SC c4) (S9 c4) (SP c4) (SS c4) (SM 0) (SC 0) (S9 0) (SP 0) (SS 0) (efOf c3) (efOf c3) qv (wm c2) (wc c2) (ww c2) (wp c2) (wsg c2) t _ _ _ hA),
        pcsFri_oodC off (fun pre β t => compViewN pre β m.hd m.stk m.heap.length roots.length m.stk N W C Mm Wt t) (cGroups tbM tbC tpP tpS (SM c4) (SC c4) (S9 c4) (SP c4) (SS c4) (efOf c3) qv) (cGroups tbM tbC tpP tpS (SM 0) (SC 0) (S9 0) (SP 0) (SS 0) (efOf c3) qv) ks cols
        ((cTs off m.hd m.stk m.heap.length roots.length m.stk m.heap N W roots C Mm Wt tbM tbC tpP tpS (SM c4) (SC c4) (S9 c4) (SP c4) (SS c4) (efOf c3) qv (wm c2) (wc c2) (ww c2) (wp c2) (wsg c2)).map Prod.fst) ((cTs off m.hd m.stk m.heap.length roots.length m.stk m.heap N W roots C Mm Wt tbM tbC tpP tpS (SM 0) (SC 0) (S9 0) (SP 0) (SS 0) (efOf c3) qv (wm c2) (wc c2) (ww c2) (wp c2) (wsg c2)).map Prod.fst) _ _ ncw (αd c4) (αd 0) _ _
        hd rfl (by simp only [cTs, bbTab, airQTabG, List.map_cons, List.map_nil]) t α β (r % NR0)⟩
    · rfl
  have hgz : sumTo K2 (fun _ => sumTo Q4 (fun c3 => indB (!genB (efOf c3)))) ≤ K2 * (P * P) := by
    rw [genB_count, sumTo_const]; exact Nat.le_refl _
  exact fs_open4_absA hK2 Q4_pos hK4 φ hφ rvF svF (fun c2 c3 => genB (efOf c3)) hgz (fun c4 => genB (αd c4)) hB4
    (fun c4 c2 c3 α β r t => realVN_cases _ _ _ _ _ α β r t) (fun c4 c2 c3 α β r t => simVN_some _ _ _ _ _ _ _ _ α β r t)
    ozF hoz (fun c4 c2 c3 hg4 hg => (hb c4 c2 c3 hg4 hg).1) (fun c4 c2 c3 hg4 hg => (hb c4 c2 c3 hg4 hg).2)
    Com1 Pf1 (fun c4 => opF (Ss c4) mk1) (fun c4 => sdF (Ss c4) mk1) d1 hc1 hp1 hr1 ov1 (fun _ => rfl) main1 hsd1
    Com2 Pf2 (fun c4 => opF (Ss c4) mk2) (fun c4 => sdF (Ss c4) mk2) d2 hc2 hp2 hr2 ov2 (fun _ => rfl) main2 hsd2
    Com3 Pf3 op3 sd3 d3 hc3 hp3' hr3 ov3 (fun _ => rfl) main3 hsd3 hvo1 hvo2 hvo3 sop1 sop2 sop3 hsvo1 hsvo2 hsvo3

set_option maxRecDepth 100000 in
/-- `compFS4` with the first commitment hiding up to `η`: its error gains
    `Q4² NS2 NS3 NR Q4² η` at each draw of the challenges and tables. -/
def compFS4A {V Wv P1 P2 P3 : Type} (η : Nat) (off : EF → String → EF) (R : Nat) (shp : BT) (Ps : List Term) (W : Nat) (A : List Cell) (e : Nat → Nat) (row : Nat → Air.Row) (tbM : Nat) (tbC : Nat) (tpP : Nat) (tpS : Nat) (SM : Nat → List F) (SC : Nat → List F) (S9 : Nat → List F) (SP : Nat → List F) (SS : Nat → List F) (qv : EF → EF → List EF → F → List F → List F → List EF) (wm : Nat → List (EF → EF → List F)) (wc : Nat → List (EF → EF → List F)) (ww : Nat → List (EF → EF → List F)) (wp : Nat → List (EF → EF → List F)) (wsg : Nat → List (EF → EF → List F)) (K2 : Nat) (K4 : Nat) (φ : Nat → Option (List (List (List EF)) × List (List (List (List EF))) × List (List (List EF))) → Nat) (N4 : Nat) (ncw : Nat) (αd : Nat → EF) (B4 : Nat) (fri : Nat → EF → EF → List (EF → EF) → V) (NR2 : Nat) (Rb : Nat → EF → EF → Nat → List (EF → EF)) (Ro : Nat → EF → EF → Nat → Wv) (NS1 : Nat) (NS2 : Nat) (NS3 : Nat) (n1 : Nat) (n2 : Nat) (n3 : Nat) (Com1 : List (List (List F)) → Nat → Nat) (Pf1 : Nat → List (List (List F)) → Nat → P1) (Com2 : List (List (List F)) → Nat → Nat) (Pf2 : Nat → List (List (List F)) → Nat → P2) (Com3 : List (List (List (List F))) × List (List (List F)) → Nat → Nat) (Pf3 : Nat → List (List (List (List F))) × List (List (List F)) → Nat → P3) : FS4D (Option P1 × Option (P2 × P3) × TViewN (PcsPV (V × Wv)) (EF × EF)) :=
    let m := blankM shp W Ps
    let roots := blankRoots shp W Ps
    let N := BT.nleaves shp
    let C := cpuTableC A row e Ps.length roots (2 ^ R)
    let Pg := progTableC m.heap N W
    let Wt := witTable A N W
    let Mm := memTableC A (cpuAirC m.hd m.stk m.heap.length roots.length m.stk) (progAirC m.heap N W)
      (witAir N W) C Pg Wt
    let NR0 := cNR off m.hd m.stk m.heap.length roots.length m.stk m.heap N W roots C Mm Wt tbM tbC tpP tpS (SM 0) (SC 0) (S9 0) (SP 0) (SS 0) EF.zero qv (wm 0) (wc 0) (ww 0) (wp 0) (wsg 0) ncw
    let pcsZ := fun (c4 c2 : Nat) (ζ : EF) t α β r => cPcs off m.hd m.stk m.heap.length roots.length m.stk m.heap N W roots C Mm Wt tbM tbC tpP tpS (SM c4) (SC c4) (S9 c4) (SP c4) (SS c4) ζ qv (wm c2) (wc c2) (ww c2) (wp c2) (wsg c2) ncw (αd c4)
      (friX (fri c4) (Rb c4) (Ro c4) (r / NR0)) t α β (r % NR0)
    let psimZ := fun (c4 c2 : Nat) (ζ : EF) α β v r => cPsim off m.hd m.stk m.heap.length roots.length m.stk m.heap N W roots C Mm Wt tbM tbC tpP tpS (SM c4) (SC c4) (S9 c4) (SP c4) (SS c4) ζ qv (wm c2) (wc c2) (ww c2) (wp c2) (wsg c2) ncw (αd c4)
      (friX (fri c4) (Rb c4) (Ro c4) (r / NR0)) α β v (r % NR0)
    let NR := NR0 * NR2
    let tabs := fun t : Nat → Tup => compTables m.hd m.stk m.heap.length roots.length m.stk m.heap N W roots
      ((C.setBlind BLA (t 1)).setBlind BLB (t 0)) (Mm.setBlind 5 (t 0)) (progTableC m.heap N W)
      (Wt.setBlind WT_BLIND (t 1)) (segsPub roots)
    let tv := fun pre β t => compViewN pre β m.hd m.stk m.heap.length roots.length m.stk N W C Mm Wt t
    let pb := fun pre β => (terminal pre β (progAirC m.heap N W) (progTableC m.heap N W),
      terminal pre β (segsAir roots) (segsPub roots))
    let ptm := fun pre β => (terminal pre β (progAirC m.heap N W) (progTableC m.heap N W)).add
      (terminal pre β (segsAir roots) (segsPub roots))
    let M := (allEntries (compTables m.hd m.stk m.heap.length roots.length m.stk m.heap N W roots C Mm
      (progTableC m.heap N W) Wt (segsPub roots))).length
    let q0 := cGroups tbM tbC tpP tpS (SM 0) (SC 0) (S9 0) (SP 0) (SS 0) EF.zero qv
    let qZ := fun (c4 : Nat) (ζ : EF) => cGroups tbM tbC tpP tpS (SM c4) (SC c4) (S9 c4) (SP c4) (SS c4) ζ qv
    let Ss := fun c4 => (qZ c4 EF.zero).map (·.base.S)
    let ks := cKs m.hd m.stk m.heap.length roots.length m.stk m.heap N W roots
    let cols := cCols off m.hd m.stk m.heap.length roots.length m.stk m.heap N W roots C Mm Wt
    let tqZ := fun (c4 c2 : Nat) (ζ : EF) => (cTs off m.hd m.stk m.heap.length roots.length m.stk m.heap N W roots C Mm Wt tbM tbC tpP tpS (SM c4) (SC c4) (S9 c4) (SP c4) (SS c4) ζ qv (wm c2) (wc c2) (ww c2) (wp c2) (wsg c2)).map Prod.fst
    let qdZ := fun (c4 c2 : Nat) (ζ : EF) (t : Nat → Tup) (α β : EF) (ms : List F) =>
      (cTs off m.hd m.stk m.heap.length roots.length m.stk m.heap N W roots C Mm Wt tbM tbC tpP tpS (SM c4) (SC c4) (S9 c4) (SP c4) (SS c4) ζ qv (wm c2) (wc c2) (ww c2) (wp c2) (wsg c2)).map (fun p => p.2 t α β ms)
    let SsT := fun c4 => (tqZ c4 0 EF.zero).map (·.S)
    let SsC := fun c4 => (tabsInfo ncw (tqZ c4 0 EF.zero)).map (·.S)
    let mk1 := [0, 2, 4, 6, 8]
    let mk2 := [1, 3, 5, 7, 9]
    let main1 := fun (t : Nat → Tup) (r : Nat) => mainF2 q0 ks cols (tqZ 0 0 EF.zero) ncw mk1 t (r % NR0)
    let main2 := fun (c1 : Nat) (t : Nat → Tup) (r : Nat) =>
      mainP2 q0 ks cols (tqZ 0 0 EF.zero) ncw mk2 t (efOf (c1 / Q4)) (efOf (c1 % Q4)) (r % NR0)
    let main3 := fun (c1 c2 : Nat) (t : Nat → Tup) (r : Nat) =>
      (tabsPolys (tqZ 0 c2 EF.zero) (qdZ 0 c2 EF.zero t (efOf (c1 / Q4)) (efOf (c1 % Q4))
          (msF q0 ks (tqZ 0 c2 EF.zero) ncw (r % NR0))) (crF q0 ks (tqZ 0 c2 EF.zero) ncw (r % NR0)),
       tabsCws ncw (tqZ 0 c2 EF.zero) (ccF q0 ks (tqZ 0 c2 EF.zero) ncw (r % NR0)))
    let vS := fun (α β : EF) (t : Nat → Tup) => viewT β (fun k => prefixOf α (off β) (chainBus k)) (fun _ => false)
      chainPar 3 (xrefN (ptm (prefixOf α (off β)) β)) t
    let sop1 := fun (c4 c2 c3 r : Nat) (_ : Nat → Tup) =>
      opF (Ss c4) mk1 (mainZ2 (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw mk1 (r % NR0))
    let sop2 := fun (c4 c2 c3 _ r : Nat) (_ : Nat → Tup) =>
      opF (Ss c4) mk2 (mainZ2 (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw mk2 (r % NR0))
    let sop3 := fun (c4 c2 c3 c1 r : Nat) (t : Nat → Tup) =>
      (opQ (SsT c4) (tabsPolys (tqZ c4 c2 (efOf c3)) (canonT (tqZ c4 c2 (efOf c3)) (efOf (c1 / Q4)) (efOf (c1 % Q4))
         (vS (efOf (c1 / Q4)) (efOf (c1 % Q4)) t)
         (openMulti ((qZ c4 (efOf c3)).map QGroup.ext) ((((qZ c4 (efOf c3)).map QGroup.ext).zip ks).map
           (fun p => List.replicate p.2 (List.replicate p.1.n (0 : F))))
           (msF (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw (r % NR0))))
         (crF (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw (r % NR0))),
       opCw (SsC c4) (tabsCws ncw (tqZ c4 c2 (efOf c3)) (ccF (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw (r % NR0))))
    let ov1 : Nat → TViewN (PcsPV (V × Wv)) (EF × EF) → Option (List (List (List F))) := fun c4 v => match v with
      | some (pv, _) => some (ovF2 (Ss c4) mk1 pv)
      | none => none
    let ov2 : Nat → TViewN (PcsPV (V × Wv)) (EF × EF) → Option (List (List (List F))) := fun c4 v => match v with
      | some (pv, _) => some (ovF2 (Ss c4) mk2 pv)
      | none => none
    let ov3 : Nat → TViewN (PcsPV (V × Wv)) (EF × EF) → Option (List (List (List (List F))) × List (List (List F))) :=
      fun _ v => match v with
      | some (pv, _) => some (ovQ pv, cwQ 10 pv)
      | none => none
    let rvF := fun (c4 c2 c3 : Nat) (α β : EF) (r : Nat) (t : Nat → Tup) =>
      realVN off tabs tv pb (pcsZ c4 c2 (efOf c3)) α β r t
    let svF := fun (c4 c2 c3 : Nat) (α β : EF) (r : Nat) (t : Nat → Tup) =>
      simVN off pb chainBus (fun _ => false) chainPar 3 ptm (psimZ c4 c2 (efOf c3)) α β r t
    let ozF : TViewN (PcsPV (V × Wv)) (EF × EF) → Option (List (List (List EF)) × List (List (List (List EF))) × List (List (List EF))) := fun v => match v with
      | some (pv, _) => some (pv.1.1.map (fun g => g.1.map Prod.snd), pv.1.2.map (List.map (List.map Prod.snd)),
        pv.2.1.map (List.map Prod.snd))
      | none => none
    let op3 := fun (c4 : Nat) (d : List (List (List (List F))) × List (List (List F))) =>
      (opQ (SsT c4) d.1, opCw (SsC c4) d.2)
    let sd3 := fun (c4 : Nat) (o : List (List (List (List F))) × List (List (List F))) =>
      (sdQ (SsT c4) o.1, sdCw (SsC c4) o.2)
    let sm := fun (g : Nat × Nat × Nat × (Nat → Tup) → Nat) =>
      sumTo NS1 (fun σ1 => sumTo (NS2 * NS3) (fun σ => sumTo NR (fun r => sumN 2 (fun t => g (σ1, σ, r, t)))))
    let m1 := fun (x : Nat × Nat × Nat × (Nat → Tup)) => Com1 (main1 x.2.2.2 x.2.2.1) x.1
    let m2 := fun (c1 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      m1 x + n1 * Com2 (main2 c1 x.2.2.2 x.2.2.1) (x.2.1 % NS2)
    let m3 := fun (c1 c2 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      m1 x + n1 * comPair NS2 n2 Com2 Com3 (main2 c1 x.2.2.2 x.2.2.1, main3 c1 c2 x.2.2.2 x.2.2.1) x.2.1
    let rvo := fun (c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      ((ov1 c4 (rvF c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)).map (fun _ => Pf1 c4 (main1 x.2.2.2 x.2.2.1) x.1),
       (ovPair (ov2 c4) (ov3 c4) (rvF c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)).map
         (fun _ => pfPair NS2 (Pf2 c4) (Pf3 c4) (main2 c1 x.2.2.2 x.2.2.1, main3 c1 c2 x.2.2.2 x.2.2.1) x.2.1),
       rvF c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)
    let s1 := fun (c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) => Com1 (sdF (Ss c4) mk1 (sop1 c4 c2 c3 x.2.2.1 x.2.2.2)) x.1
    let s2 := fun (c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      s1 c4 c1 c2 c3 x + n1 * Com2 (sdF (Ss c4) mk2 (sop2 c4 c2 c3 c1 x.2.2.1 x.2.2.2)) (x.2.1 % NS2)
    let s3 := fun (c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      s1 c4 c1 c2 c3 x + n1 * comPair NS2 n2 Com2 Com3
        (sdF (Ss c4) mk2 (sop2 c4 c2 c3 c1 x.2.2.1 x.2.2.2), sd3 c4 (sop3 c4 c2 c3 c1 x.2.2.1 x.2.2.2)) x.2.1
    let svo := fun (c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      (some (Pf1 c4 (sdF (Ss c4) mk1 (sop1 c4 c2 c3 x.2.2.1 x.2.2.2)) x.1),
       some (pfPair NS2 (Pf2 c4) (Pf3 c4) (sdF (Ss c4) mk2 (sop2 c4 c2 c3 c1 x.2.2.1 x.2.2.2), sd3 c4 (sop3 c4 c2 c3 c1 x.2.2.1 x.2.2.2)) x.2.1),
       svF c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)
    let sm4 := fun (g : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup)) → Nat) =>
      sumTo ((Q4 * Q4) ^ n1) (fun H1 => sumTo (K2 ^ (n1 * n2)) (fun H2 =>
        sumTo (Q4 ^ (n1 * (n2 * n3))) (fun H3 => sm (fun x => g (H1, H2, H3, x)))))
    let r1 := fun (y : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup))) => rget (Q4 * Q4) (m1 y.2.2.2) y.1
    let r2 := fun (y : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup))) => rget K2 (m2 (r1 y) y.2.2.2) y.2.1
    let r3 := fun (y : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup))) => rget Q4 (m3 (r1 y) (r2 y) y.2.2.2) y.2.2.1
    let Mq := fun (y : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup))) => φ (m3 (r1 y) (r2 y) y.2.2.2)
      (ozF (rvF 0 (r2 y) (r3 y) (efOf (r1 y / Q4)) (efOf (r1 y % Q4)) y.2.2.2.2.2.1 y.2.2.2.2.2.2))
  ⟨NS1, NS2 * NS3, NR, m1, m2, m3,
    fun c1 c2 c3 x => φ (m3 c1 c2 x) (ozF (rvF 0 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)),
    rvo,
    fun c x => (s1 c.2.2.2 c.1 c.2.1 c.2.2.1 x, s2 c.2.2.2 c.1 c.2.1 c.2.2.1 x, s3 c.2.2.2 c.1 c.2.1 c.2.2.1 x,
      φ (s3 c.2.2.2 c.1 c.2.1 c.2.2.1 x) (ozF (svF c.2.2.2 c.2.1 c.2.2.1 (efOf (c.1 / Q4)) (efOf (c.1 % Q4)) x.2.2.1 x.2.2.2))),
    fun c x => (s1 c.2.2.2 c.1 c.2.1 c.2.2.1 x, s2 c.2.2.2 c.1 c.2.1 c.2.2.1 x, s3 c.2.2.2 c.1 c.2.1 c.2.2.1 x,
      svo c.2.2.2 c.1 c.2.1 c.2.2.1 x),
    K4 ^ N4 * (K4 * ((Q4 * Q4) ^ n1 * (K2 ^ (n1 * n2) * (Q4 ^ (n1 * (n2 * n3)) *
          (K2 * (Q4 * (NS1 * (NS2 * NS3 * (Q4 * (NR * (Q4 ^ 2 * M)) + Q4 * (Q4 * (Q4 ^ 2 * 0)))) +
            Q4 * Q4 * (NS2 * NS3 * (NR * (Q4 ^ 2 * η))))) +
            (Q4 * (P * P) * (K2 * Q4) + Q4 * Q4 * (K2 * (P * P))) * (NS1 * (NS2 * NS3 * (NR * (Q4 ^ 2 * 1)))))))) +
            B4 * (Q4 * Q4 * (K2 * Q4) * sm4 (fun _ => 1)))⟩

set_option maxRecDepth 100000 in
/-- **`comp_fs4` with the first commitment hiding up to `η`**
    (`compFS4A`, `comp_fs_open4_absA`).  One direction. -/
theorem comp_fs4A {V Wv P1 P2 P3 : Type} (off : EF → String → EF) {R Lm : Nat} (hR : R ≤ 20) {shp : BT} {Ps : List Term}
    {W : Nat} {ρ : Nat → Bool} {region : List Cell} (hrl : region.length = W)
    (hr : ∀ i c, region[i]? = some c → cellOK (BT.nleaves shp + 3 + i) c = true)
    {A : List Cell} {e : Nat → Nat} {row : Nat → Air.Row}
    (hA : AcceptsC A (cMachine ρ shp region Ps) (cHeap ρ shp region Ps).2
      (cHeap ρ shp region Ps).1.length Ps.length e row)
    (hlen : A.length = 2 ^ Lm) (hLm : Lm ≤ 20) (hK : e (Ps.length - 1) < 2 ^ R)
    (hNW : BT.nleaves shp + W ≤ 2 ^ 8)
    {tbM tbC tpP tpS : Nat} (htM : tbM + 1 = Lm) (htC : tbC + 1 = R)
    (htP : tpP = progTpC (blankM shp W Ps).heap (BT.nleaves shp) W) (htS : tpS = segTp (blankRoots shp W Ps))
    (SM SC S9 SP SS : Nat → List F) (qv : EF → EF → List EF → F → List F → List F → List EF)
    (wm wc ww wp wsg : Nat → List (EF → EF → List F)) {Lwm Lwc Lww Lwp Lwsg : Nat} (hlwm : ∀ c, (wm c).length = Lwm)
    (hlwc : ∀ c, (wc c).length = Lwc) (hlww : ∀ c, (ww c).length = Lww) (hlwp : ∀ c, (wp c).length = Lwp)
    (hlwsg : ∀ c, (wsg c).length = Lwsg)
    {K2 K4 : Nat} (hK2 : 0 < K2) (hK4 : 0 < K4)
    (φ : Nat → Option (List (List (List EF)) × List (List (List (List EF))) × List (List (List EF))) → Nat) {N4 : Nat} (hφ : ∀ m w, φ m w < N4)
    (hSM : ∀ c4, ∀ x ∈ SM c4, x ∉ cosetL 1 (bbGen (tbM + 1)) (2 ^ (tbM + 1)))
    (hSC : ∀ c4, ∀ x ∈ SC c4, x ∉ cosetL 1 (bbGen (tbC + 1)) (2 ^ (tbC + 1)))
    (hS9 : ∀ c4, ∀ x ∈ S9 c4, x ∉ cosetL 1 (bbGen 9) (2 ^ 9))
    (hSP : ∀ c4, ∀ x ∈ SP c4, x ∉ cosetL 1 (bbGen (tpP + 1)) (2 ^ (tpP + 1)))
    (hSS : ∀ c4, ∀ x ∈ SS c4, x ∉ cosetL 1 (bbGen (tpS + 1)) (2 ^ (tpS + 1)))
    (hszM : ∀ c4, 2 * (SM c4).length + 8 ≤ 2 ^ (tbM + 1)) (hszC : ∀ c4, 2 * (SC c4).length + 8 ≤ 2 ^ (tbC + 1))
    (hsz9 : ∀ c4, 2 * (S9 c4).length + 8 ≤ 2 ^ 9) (hszP : ∀ c4, 2 * (SP c4).length + 8 ≤ 2 ^ (tpP + 1))
    (hszS : ∀ c4, 2 * (SS c4).length + 8 ≤ 2 ^ (tpS + 1)) {ncw : Nat} (αd : Nat → EF) {B4 : Nat}
    (hB4 : sumTo K4 (fun c4 => indB (!genB (αd c4))) ≤ B4) (fri : Nat → EF → EF → List (EF → EF) → V) (hncw : 4 ≤ ncw)
    (NR2 : Nat) (Rb : Nat → EF → EF → Nat → List (EF → EF)) (Ro : Nat → EF → EF → Nat → Wv)
    {NS1 NS2 NS3 n1 n2 n3 : Nat}
    (Com1 : List (List (List F)) → Nat → Nat) (Pf1 : Nat → List (List (List F)) → Nat → P1) {η : Nat} (hc1 : ComHidesA NS1 η Com1)
    (hp1 : ∀ c4, ComPfHidesA NS1 η Com1 (Pf1 c4) (opF ((cGroups tbM tbC tpP tpS (SM c4) (SC c4) (S9 c4) (SP c4) (SS c4) EF.zero qv).map (·.base.S)) [0, 2, 4, 6, 8]))
    (hr1 : ∀ d σ, Com1 d σ < n1) (d1 : List (List (List F)))
    (Com2 : List (List (List F)) → Nat → Nat) (Pf2 : Nat → List (List (List F)) → Nat → P2) (hc2 : ComHides NS2 Com2)
    (hp2 : ∀ c4, ComPfHides NS2 Com2 (Pf2 c4) (opF ((cGroups tbM tbC tpP tpS (SM c4) (SC c4) (S9 c4) (SP c4) (SS c4) EF.zero qv).map (·.base.S)) [1, 3, 5, 7, 9]))
    (hr2 : ∀ d σ, Com2 d σ < n2) (d2 : List (List (List F)))
    (Com3 : List (List (List (List F))) × List (List (List F)) → Nat → Nat)
    (Pf3 : Nat → List (List (List (List F))) × List (List (List F)) → Nat → P3) (hc3 : ComHides NS3 Com3)
    (hp3 : ∀ c4, ComPfHides NS3 Com3 (Pf3 c4) (fun d => (opQ (cSsT (SM c4) (SC c4) (S9 c4) (SP c4) (SS c4)) d.1, opCw (cSsC tbM tbC tpP tpS (SM c4) (SC c4) (S9 c4) (SP c4) (SS c4)) d.2)))
    (hr3 : ∀ d σ, Com3 d σ < n3) (d3 : List (List (List (List F))) × List (List (List F))) :
    ZKB (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo (K4 ^ N4) (fun H4 => sumTo ((Q4 * Q4) ^ n1) (fun H1 =>
      sumTo (K2 ^ (n1 * n2)) (fun H2 => sumTo (Q4 ^ (n1 * (n2 * n3))) (fun H3 => f (H1, H2, H3, H4))))))
      (K4 * (Q4 * Q4 * (K2 * Q4))) ((compFS4A η off R shp Ps W A e row tbM tbC tpP tpS SM SC S9 SP SS qv wm wc ww wp wsg K2 K4 φ N4 ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Pf1 Com2 Pf2 Com3 Pf3).sm 2)
      (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo K4 (fun c4 => sumTo (Q4 * Q4) (fun c1 =>
        sumTo K2 (fun c2 => sumTo Q4 (fun c3 => f (c1, c2, c3, c4))))))
      (read4 (Q4 * Q4) K2 Q4 K4 (compFS4A η off R shp Ps W A e row tbM tbC tpP tpS SM SC S9 SP SS qv wm wc ww wp wsg K2 K4 φ N4 ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Pf1 Com2 Pf2 Com3 Pf3).m1 (compFS4A η off R shp Ps W A e row tbM tbC tpP tpS SM SC S9 SP SS qv wm wc ww wp wsg K2 K4 φ N4 ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Pf1 Com2 Pf2 Com3 Pf3).m2 (compFS4A η off R shp Ps W A e row tbM tbC tpP tpS SM SC S9 SP SS qv wm wc ww wp wsg K2 K4 φ N4 ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Pf1 Com2 Pf2 Com3 Pf3).m3 (compFS4A η off R shp Ps W A e row tbM tbC tpP tpS SM SC S9 SP SS qv wm wc ww wp wsg K2 K4 φ N4 ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Pf1 Com2 Pf2 Com3 Pf3).q (compFS4A η off R shp Ps W A e row tbM tbC tpP tpS SM SC S9 SP SS qv wm wc ww wp wsg K2 K4 φ N4 ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Pf1 Com2 Pf2 Com3 Pf3).out)
      (fun H c x => prog4 (Q4 * Q4) K2 Q4 K4 H ((compFS4A η off R shp Ps W A e row tbM tbC tpP tpS SM SC S9 SP SS qv wm wc ww wp wsg K2 K4 φ N4 ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Pf1 Com2 Pf2 Com3 Pf3).pts c x) c) (compFS4A η off R shp Ps W A e row tbM tbC tpP tpS SM SC S9 SP SS qv wm wc ww wp wsg K2 K4 φ N4 ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Pf1 Com2 Pf2 Com3 Pf3).sv (compFS4A η off R shp Ps W A e row tbM tbC tpP tpS SM SC S9 SP SS qv wm wc ww wp wsg K2 K4 φ N4 ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Pf1 Com2 Pf2 Com3 Pf3).ε :=
  comp_fs_open4_absA off hR hrl hr hA hlen hLm hK hNW htM htC htP htS SM SC S9 SP SS qv wm wc ww wp wsg hlwm hlwc hlww hlwp hlwsg hK2 hK4 φ hφ hSM hSC hS9 hSP hSS hszM hszC hsz9 hszP hszS αd hB4 fri hncw NR2 Rb Ro Com1 Pf1 hc1 hp1 hr1 d1 Com2 Pf2 hc2 hp2 hr2 d2 Com3 Pf3 hc3 hp3 hr3 d3

set_option maxRecDepth 100000 in
/-- **`sud_fs_open4_powD` with each first commitment hiding up to `η ix`**:
    `fs4_powD` at `sudFS4A`, each statement's error gaining its `η` term
    (`sud_fs4A`).  One direction. -/
theorem sud_fs_open4_powDA {V Wv P1 P2 P3 : Type}  (off : EF → String → EF) {puzzle : ∀ ix : Nat, List Nat} (hc : ∀ ix : Nat, CluesOK (cluesOf (puzzle ix))) {ρ : ∀ ix : Nat, Nat → Bool} {A : ∀ ix : Nat, List Cell} {k : ∀ ix : Nat, Nat} {row : ∀ ix : Nat, Nat → Air.Row} (hA : ∀ ix : Nat, AcceptsFrom (A ix) (stmtMachine (ρ ix) 729 (sudokuExpr (cluesOf (puzzle ix))) ACC REJ) (k ix) (row ix)) (hacc : ∀ ix : Nat, rd (A ix) ((row ix) ((k ix) - 1)).ctr ((row ix) ((k ix) - 1)).hd = some (.atom ACC)) (hlen : ∀ ix : Nat, (A ix).length = 2 ^ 16) (hk : ∀ ix : Nat, (k ix) ≤ 2 ^ 16) {tP : ∀ ix : Nat, Nat} (htp : ∀ ix : Nat, (tP ix) = progTp (stmtMachine (fun _ => false) 729 (sudokuExpr (cluesOf (puzzle ix))) ACC REJ).heap) (S16 S10 SP : ∀ ix : Nat, Nat → List F) (qv : ∀ ix : Nat, EF → EF → List EF → F → List F → List F → List EF) (wm wc ww wp : ∀ ix : Nat, Nat → List (EF → EF → List F)) {Lwm Lwc Lww Lwp : ∀ ix : Nat, Nat} (hlwm : ∀ ix : Nat, ∀ c, ((wm ix) c).length = (Lwm ix)) (hlwc : ∀ ix : Nat, ∀ c, ((wc ix) c).length = (Lwc ix)) (hlww : ∀ ix : Nat, ∀ c, ((ww ix) c).length = (Lww ix)) (hlwp : ∀ ix : Nat, ∀ c, ((wp ix) c).length = (Lwp ix)) {K2 K4 : Nat} (hK2 : 0 < K2) (hK4 : 0 < K4) (φ : ∀ ix : Nat, Nat → Option (List (List (List EF)) × List (List (List (List EF))) × List (List (List EF))) → Nat) {N4 : Nat} (hφ : ∀ ix : Nat, ∀ m w, (φ ix) m w < N4) (hS16 : ∀ ix : Nat, ∀ c4, ∀ x ∈ (S16 ix) c4, x ∉ cosetL 1 (bbGen 16) (2 ^ 16)) (hS10 : ∀ ix : Nat, ∀ c4, ∀ x ∈ (S10 ix) c4, x ∉ cosetL 1 (bbGen 10) (2 ^ 10)) (hSP : ∀ ix : Nat, ∀ c4, ∀ x ∈ (SP ix) c4, x ∉ cosetL 1 (bbGen ((tP ix) + 1)) (2 ^ ((tP ix) + 1))) (hsz16 : ∀ ix : Nat, ∀ c4, 2 * ((S16 ix) c4).length + 8 ≤ 2 ^ 16) (hsz : ∀ ix : Nat, ∀ c4, 2 * ((S10 ix) c4).length + 8 ≤ 2 ^ 10) (hszP : ∀ ix : Nat, ∀ c4, 2 * ((SP ix) c4).length + 8 ≤ 2 ^ ((tP ix) + 1)) {ncw : ∀ ix : Nat, Nat} (αd : ∀ ix : Nat, Nat → EF) {B4 : ∀ ix : Nat, Nat} (hB4 : ∀ ix : Nat, sumTo K4 (fun c4 => indB (!genB ((αd ix) c4))) ≤ (B4 ix)) (fri : ∀ ix : Nat, Nat → EF → EF → List (EF → EF) → V) (hncw : ∀ ix : Nat, 4 ≤ (ncw ix)) (NR2 : ∀ ix : Nat, Nat) (Rb : ∀ ix : Nat, Nat → EF → EF → Nat → List (EF → EF)) (Ro : ∀ ix : Nat, Nat → EF → EF → Nat → Wv) {n1 n2 n3 : Nat} {NS1 NS2 NS3 : ∀ ix : Nat, Nat} (Com1 : ∀ ix : Nat, List (List (List F)) → Nat → Nat) (Pf1 : ∀ ix : Nat, Nat → List (List (List F)) → Nat → P1) (η : Nat → Nat) (hc1 : ∀ ix : Nat, ComHidesA (NS1 ix) (η ix) (Com1 ix)) (hp1 : ∀ ix : Nat, ∀ c4, ComPfHidesA (NS1 ix) (η ix) (Com1 ix) ((Pf1 ix) c4) (opF ((sudGroups (tP ix) ((S16 ix) c4) ((S10 ix) c4) ((SP ix) c4) EF.zero (qv ix)).map (·.base.S)) [0, 2, 4, 6])) (hr1 : ∀ ix : Nat, ∀ d σ, (Com1 ix) d σ < n1) (d1 : ∀ ix : Nat, List (List (List F))) (Com2 : ∀ ix : Nat, List (List (List F)) → Nat → Nat) (Pf2 : ∀ ix : Nat, Nat → List (List (List F)) → Nat → P2) (hc2 : ∀ ix : Nat, ComHides (NS2 ix) (Com2 ix)) (hp2 : ∀ ix : Nat, ∀ c4, ComPfHides (NS2 ix) (Com2 ix) ((Pf2 ix) c4) (opF ((sudGroups (tP ix) ((S16 ix) c4) ((S10 ix) c4) ((SP ix) c4) EF.zero (qv ix)).map (·.base.S)) [1, 3, 5, 7])) (hr2 : ∀ ix : Nat, ∀ d σ, (Com2 ix) d σ < n2) (d2 : ∀ ix : Nat, List (List (List F))) (Com3 : ∀ ix : Nat, List (List (List (List F))) × List (List (List F)) → Nat → Nat) (Pf3 : ∀ ix : Nat, Nat → List (List (List (List F))) × List (List (List F)) → Nat → P3) (hc3 : ∀ ix : Nat, ComHides (NS3 ix) (Com3 ix)) (hp3 : ∀ ix : Nat, ∀ c4, ComPfHides (NS3 ix) (Com3 ix) ((Pf3 ix) c4) (fun d => (opQ (sudSsT ((S16 ix) c4) ((S10 ix) c4) ((SP ix) c4)) d.1, opCw (sudSsC (tP ix) ((S16 ix) c4) ((S10 ix) c4) ((SP ix) c4)) d.2))) (hr3 : ∀ ix : Nat, ∀ d σ, (Com3 ix) d σ < n3) (d3 : ∀ ix : Nat, List (List (List (List F))) × List (List (List F)))
    (hφs : ∀ i j m w m' w', φ i m w = φ j m' w' → m % n1 = m' % n1) (δs : Nat → Nat)
    (hsp : ∀ ix d v, sumTo (NS1 ix) (fun σ => indB (decide (Com1 ix d σ = v))) ≤ δs ix) :
    ∀ n, ZKB (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo (K4 ^ N4) (fun H4 => sumTo ((Q4 * Q4) ^ n1) (fun H1 =>
        sumTo (K2 ^ (n1 * n2)) (fun H2 => sumTo (Q4 ^ (n1 * (n2 * n3))) (fun H3 => f (H1, H2, H3, H4))))))
      (KPowD (fun _ => K4 * (Q4 * Q4 * (K2 * Q4))) n)
      (smPowD (X := fun _ => Nat × Nat × Nat × (Nat → Tup)) (fun ix => (sudFS4A (η ix) off (puzzle ix) (A ix) (k ix) (row ix) (tP ix) (S16 ix) (S10 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NS1 ix) (NS2 ix) (NS3 ix) n1 n2 n3 (Com1 ix) (Pf1 ix) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix)).sm 2) n)
      (scPowD (C := fun _ => Nat × Nat × Nat × Nat) (fun _ => fun (f : Nat × Nat × Nat × Nat → Nat) =>
        sumTo K4 (fun c4 => sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo Q4 (fun c3 => f (c1, c2, c3, c4)))))) n)
      (rvPowD (fun ix => read4 (Q4 * Q4) K2 Q4 K4 (sudFS4A (η ix) off (puzzle ix) (A ix) (k ix) (row ix) (tP ix) (S16 ix) (S10 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NS1 ix) (NS2 ix) (NS3 ix) n1 n2 n3 (Com1 ix) (Pf1 ix) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix)).m1 (sudFS4A (η ix) off (puzzle ix) (A ix) (k ix) (row ix) (tP ix) (S16 ix) (S10 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NS1 ix) (NS2 ix) (NS3 ix) n1 n2 n3 (Com1 ix) (Pf1 ix) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix)).m2 (sudFS4A (η ix) off (puzzle ix) (A ix) (k ix) (row ix) (tP ix) (S16 ix) (S10 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NS1 ix) (NS2 ix) (NS3 ix) n1 n2 n3 (Com1 ix) (Pf1 ix) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix)).m3 (sudFS4A (η ix) off (puzzle ix) (A ix) (k ix) (row ix) (tP ix) (S16 ix) (S10 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NS1 ix) (NS2 ix) (NS3 ix) n1 n2 n3 (Com1 ix) (Pf1 ix) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix)).q (sudFS4A (η ix) off (puzzle ix) (A ix) (k ix) (row ix) (tP ix) (S16 ix) (S10 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NS1 ix) (NS2 ix) (NS3 ix) n1 n2 n3 (Com1 ix) (Pf1 ix) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix)).out) n)
      (pgPowD (fun ix H c xx => prog4 (Q4 * Q4) K2 Q4 K4 H ((sudFS4A (η ix) off (puzzle ix) (A ix) (k ix) (row ix) (tP ix) (S16 ix) (S10 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NS1 ix) (NS2 ix) (NS3 ix) n1 n2 n3 (Com1 ix) (Pf1 ix) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix)).pts c xx) c) n) (svPowD (fun ix => (sudFS4A (η ix) off (puzzle ix) (A ix) (k ix) (row ix) (tP ix) (S16 ix) (S10 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NS1 ix) (NS2 ix) (NS3 ix) n1 n2 n3 (Com1 ix) (Pf1 ix) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix)).sv) n)
      (errPowD (fun _ => K4 * (Q4 * Q4 * (K2 * Q4))) (fun ix => (sudFS4A (η ix) off (puzzle ix) (A ix) (k ix) (row ix) (tP ix) (S16 ix) (S10 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NS1 ix) (NS2 ix) (NS3 ix) n1 n2 n3 (Com1 ix) (Pf1 ix) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix)).sm 2)
        (fun _ => fun (f : Nat × Nat × Nat × Nat → Nat) =>
          sumTo K4 (fun c4 => sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo Q4 (fun c3 => f (c1, c2, c3, c4))))))
        (fun ix => (sudFS4A (η ix) off (puzzle ix) (A ix) (k ix) (row ix) (tP ix) (S16 ix) (S10 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NS1 ix) (NS2 ix) (NS3 ix) n1 n2 n3 (Com1 ix) (Pf1 ix) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix)).ε)
        (fun j => sumTo K4 (fun c4 => sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo Q4 (fun c3 =>
          (sudFS4A (η j) off (puzzle j) (A j) (k j) (row j) (tP j) (S16 j) (S10 j) (SP j) (qv j) (wm j) (wc j) (ww j) (wp j) K2 K4 (φ j) N4 (ncw j) (αd j) (B4 j) (fri j) (NR2 j) (Rb j) (Ro j) (NS1 j) (NS2 j) (NS3 j) n1 n2 n3 (Com1 j) (Pf1 j) (Com2 j) (Pf2 j) (Com3 j) (Pf3 j)).sm 2 (fun _ => sumTo (K4 ^ N4) (fun H4 => sumTo ((Q4 * Q4) ^ n1) (fun H1 =>
            sumTo (K2 ^ (n1 * n2)) (fun H2 => sumTo (Q4 ^ (n1 * (n2 * n3))) (fun H3 =>
              hitBD (fun ix => (sudFS4A (η ix) off (puzzle ix) (A ix) (k ix) (row ix) (tP ix) (S16 ix) (S10 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NS1 ix) (NS2 ix) (NS3 ix) n1 n2 n3 (Com1 ix) (Pf1 ix) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix)).sm 2) (fun ix => (sudFS4A (η ix) off (puzzle ix) (A ix) (k ix) (row ix) (tP ix) (S16 ix) (S10 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NS1 ix) (NS2 ix) (NS3 ix) n1 n2 n3 (Com1 ix) (Pf1 ix) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix)).NS * ((sudFS4A (η ix) off (puzzle ix) (A ix) (k ix) (row ix) (tP ix) (S16 ix) (S10 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NS1 ix) (NS2 ix) (NS3 ix) n1 n2 n3 (Com1 ix) (Pf1 ix) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix)).NR * (Q4 ^ 2 * δs ix))) j)))))))))) n) := by
  intro n
  exact fs4_powD (n1 := n1) hK2 hK4 (fun ix => (sudFS4A (η ix) off (puzzle ix) (A ix) (k ix) (row ix) (tP ix) (S16 ix) (S10 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NS1 ix) (NS2 ix) (NS3 ix) n1 n2 n3 (Com1 ix) (Pf1 ix) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix)))
    (fun ix c1 x => (Nat.add_mul_mod_self_left _ _ _).trans (Nat.mod_eq_of_lt (hr1 ix _ _)))
    (fun ix c1 c2 x => (Nat.add_mul_mod_self_left _ _ _).trans (Nat.mod_eq_of_lt (hr1 ix _ _)))
    (fun ix c x => (Nat.add_mul_mod_self_left _ _ _).trans (Nat.mod_eq_of_lt (hr1 ix _ _)))
    (fun ix c x => (Nat.add_mul_mod_self_left _ _ _).trans (Nat.mod_eq_of_lt (hr1 ix _ _)))
    (fun i j c1 c2 c3 x c xa h => hφs i j _ _ _ _ h)
    (fun ix => (sudFS4A (η ix) off (puzzle ix) (A ix) (k ix) (row ix) (tP ix) (S16 ix) (S10 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NS1 ix) (NS2 ix) (NS3 ix) n1 n2 n3 (Com1 ix) (Pf1 ix) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix)).NS * ((sudFS4A (η ix) off (puzzle ix) (A ix) (k ix) (row ix) (tP ix) (S16 ix) (S10 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NS1 ix) (NS2 ix) (NS3 ix) n1 n2 n3 (Com1 ix) (Pf1 ix) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix)).NR * (Q4 ^ 2 * δs ix)))
    (fun ix v => spread_sum (Com1 ix) (sudMain1 V Wv off (puzzle ix) (A ix) (k ix) (row ix) (tP ix) (S16 ix) (S10 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (ncw ix) (αd ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix)) (hsp ix) v)
    (fun ix => sud_fs4A off (hc ix) (hA ix) (hacc ix) (hlen ix) (hk ix) (htp ix) (S16 ix) (S10 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (hlwm ix) (hlwc ix) (hlww ix) (hlwp ix) hK2 hK4 (φ ix) (hφ ix) (hS16 ix) (hS10 ix) (hSP ix) (hsz16 ix) (hsz ix) (hszP ix) (αd ix) (hB4 ix) (fri ix) (hncw ix) (NR2 ix) (Rb ix) (Ro ix) (Com1 ix) (Pf1 ix) (hc1 ix) (hp1 ix) (hr1 ix) (d1 ix) (Com2 ix) (Pf2 ix) (hc2 ix) (hp2 ix) (hr2 ix) (d2 ix) (Com3 ix) (Pf3 ix) (hc3 ix) (hp3 ix) (hr3 ix) (d3 ix)) n

set_option maxRecDepth 100000 in
/-- **`wit_fs_open4_powD` with each first commitment hiding up to `η ix`**:
    `fs4_powD` at `witFS4A`, each statement's error gaining its `η` term
    (`wit_fs4A`).  One direction. -/
theorem wit_fs_open4_powDA {V Wv P1 P2 P3 : Type}  (off : EF → String → EF) {Vt x : ∀ ix : Nat, Term} {W : ∀ ix : Nat, Nat} {ws : ∀ ix : Nat, List Cell} (hwf : ∀ ix : Nat, WF (ws ix)) (hwl : ∀ ix : Nat, (ws ix).length = (W ix)) (hW8 : ∀ ix : Nat, (W ix) ≤ 2 ^ 8) {A : ∀ ix : Nat, List Cell} {k : ∀ ix : Nat, Nat} {row : ∀ ix : Nat, Nat → Air.Row} (hA : ∀ ix : Nat, AcceptsFrom (A ix) (wMachine (ws ix) ((Vt ix) ⬝ (x ix))) (k ix) (row ix)) (hK : ∀ ix : Nat, rd (A ix) ((row ix) ((k ix) - 1)).ctr ((row ix) ((k ix) - 1)).hd = some .K ∧ rd (A ix) ((row ix) ((k ix) - 1)).ctr ((row ix) ((k ix) - 1)).stk = some .nil) (hlen : ∀ ix : Nat, (A ix).length = 2 ^ 10) (hk : ∀ ix : Nat, (k ix) ≤ 2 ^ 10) {tP : ∀ ix : Nat, Nat} (htp : ∀ ix : Nat, (tP ix) = progTpW (wMachine (List.replicate (W ix) .S) ((Vt ix) ⬝ (x ix))).heap (W ix)) (S10 S9 SP : ∀ ix : Nat, Nat → List F) (qv : ∀ ix : Nat, EF → EF → List EF → F → List F → List F → List EF) (wm wc ww wp : ∀ ix : Nat, Nat → List (EF → EF → List F)) {Lwm Lwc Lww Lwp : ∀ ix : Nat, Nat} (hlwm : ∀ ix : Nat, ∀ c, ((wm ix) c).length = (Lwm ix)) (hlwc : ∀ ix : Nat, ∀ c, ((wc ix) c).length = (Lwc ix)) (hlww : ∀ ix : Nat, ∀ c, ((ww ix) c).length = (Lww ix)) (hlwp : ∀ ix : Nat, ∀ c, ((wp ix) c).length = (Lwp ix)) {K2 K4 : Nat} (hK2 : 0 < K2) (hK4 : 0 < K4) (φ : ∀ ix : Nat, Nat → Option (List (List (List EF)) × List (List (List (List EF))) × List (List (List EF))) → Nat) {N4 : Nat} (hφ : ∀ ix : Nat, ∀ m w, (φ ix) m w < N4) (hS10 : ∀ ix : Nat, ∀ c4, ∀ x ∈ (S10 ix) c4, x ∉ cosetL 1 (bbGen 10) (2 ^ 10)) (hS9 : ∀ ix : Nat, ∀ c4, ∀ x ∈ (S9 ix) c4, x ∉ cosetL 1 (bbGen 9) (2 ^ 9)) (hSP : ∀ ix : Nat, ∀ c4, ∀ x ∈ (SP ix) c4, x ∉ cosetL 1 (bbGen ((tP ix) + 1)) (2 ^ ((tP ix) + 1))) (hsz10 : ∀ ix : Nat, ∀ c4, 2 * ((S10 ix) c4).length + 8 ≤ 2 ^ 10) (hsz9 : ∀ ix : Nat, ∀ c4, 2 * ((S9 ix) c4).length + 8 ≤ 2 ^ 9) (hszP : ∀ ix : Nat, ∀ c4, 2 * ((SP ix) c4).length + 8 ≤ 2 ^ ((tP ix) + 1)) {ncw : ∀ ix : Nat, Nat} (αd : ∀ ix : Nat, Nat → EF) {B4 : ∀ ix : Nat, Nat} (hB4 : ∀ ix : Nat, sumTo K4 (fun c4 => indB (!genB ((αd ix) c4))) ≤ (B4 ix)) (fri : ∀ ix : Nat, Nat → EF → EF → List (EF → EF) → V) (hncw : ∀ ix : Nat, 4 ≤ (ncw ix)) (NR2 : ∀ ix : Nat, Nat) (Rb : ∀ ix : Nat, Nat → EF → EF → Nat → List (EF → EF)) (Ro : ∀ ix : Nat, Nat → EF → EF → Nat → Wv) {n1 n2 n3 : Nat} {NS1 NS2 NS3 : ∀ ix : Nat, Nat} (Com1 : ∀ ix : Nat, List (List (List F)) → Nat → Nat) (Pf1 : ∀ ix : Nat, Nat → List (List (List F)) → Nat → P1) (η : Nat → Nat) (hc1 : ∀ ix : Nat, ComHidesA (NS1 ix) (η ix) (Com1 ix)) (hp1 : ∀ ix : Nat, ∀ c4, ComPfHidesA (NS1 ix) (η ix) (Com1 ix) ((Pf1 ix) c4) (opF ((wGroups (tP ix) ((S10 ix) c4) ((S9 ix) c4) ((SP ix) c4) EF.zero (qv ix)).map (·.base.S)) [0, 2, 4, 6])) (hr1 : ∀ ix : Nat, ∀ d σ, (Com1 ix) d σ < n1) (d1 : ∀ ix : Nat, List (List (List F))) (Com2 : ∀ ix : Nat, List (List (List F)) → Nat → Nat) (Pf2 : ∀ ix : Nat, Nat → List (List (List F)) → Nat → P2) (hc2 : ∀ ix : Nat, ComHides (NS2 ix) (Com2 ix)) (hp2 : ∀ ix : Nat, ∀ c4, ComPfHides (NS2 ix) (Com2 ix) ((Pf2 ix) c4) (opF ((wGroups (tP ix) ((S10 ix) c4) ((S9 ix) c4) ((SP ix) c4) EF.zero (qv ix)).map (·.base.S)) [1, 3, 5, 7])) (hr2 : ∀ ix : Nat, ∀ d σ, (Com2 ix) d σ < n2) (d2 : ∀ ix : Nat, List (List (List F))) (Com3 : ∀ ix : Nat, List (List (List (List F))) × List (List (List F)) → Nat → Nat) (Pf3 : ∀ ix : Nat, Nat → List (List (List (List F))) × List (List (List F)) → Nat → P3) (hc3 : ∀ ix : Nat, ComHides (NS3 ix) (Com3 ix)) (hp3 : ∀ ix : Nat, ∀ c4, ComPfHides (NS3 ix) (Com3 ix) ((Pf3 ix) c4) (fun d => (opQ (wSsT ((S10 ix) c4) ((S9 ix) c4) ((SP ix) c4)) d.1, opCw (wSsC (tP ix) ((S10 ix) c4) ((S9 ix) c4) ((SP ix) c4)) d.2))) (hr3 : ∀ ix : Nat, ∀ d σ, (Com3 ix) d σ < n3) (d3 : ∀ ix : Nat, List (List (List (List F))) × List (List (List F)))
    (hφs : ∀ i j m w m' w', φ i m w = φ j m' w' → m % n1 = m' % n1) (δs : Nat → Nat)
    (hsp : ∀ ix d v, sumTo (NS1 ix) (fun σ => indB (decide (Com1 ix d σ = v))) ≤ δs ix) :
    ∀ n, ZKB (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo (K4 ^ N4) (fun H4 => sumTo ((Q4 * Q4) ^ n1) (fun H1 =>
        sumTo (K2 ^ (n1 * n2)) (fun H2 => sumTo (Q4 ^ (n1 * (n2 * n3))) (fun H3 => f (H1, H2, H3, H4))))))
      (KPowD (fun _ => K4 * (Q4 * Q4 * (K2 * Q4))) n)
      (smPowD (X := fun _ => Nat × Nat × Nat × (Nat → Tup)) (fun ix => (witFS4A (η ix) off (Vt ix) (x ix) (W ix) (A ix) (k ix) (row ix) (tP ix) (S10 ix) (S9 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NS1 ix) (NS2 ix) (NS3 ix) n1 n2 n3 (Com1 ix) (Pf1 ix) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix)).sm 2) n)
      (scPowD (C := fun _ => Nat × Nat × Nat × Nat) (fun _ => fun (f : Nat × Nat × Nat × Nat → Nat) =>
        sumTo K4 (fun c4 => sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo Q4 (fun c3 => f (c1, c2, c3, c4)))))) n)
      (rvPowD (fun ix => read4 (Q4 * Q4) K2 Q4 K4 (witFS4A (η ix) off (Vt ix) (x ix) (W ix) (A ix) (k ix) (row ix) (tP ix) (S10 ix) (S9 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NS1 ix) (NS2 ix) (NS3 ix) n1 n2 n3 (Com1 ix) (Pf1 ix) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix)).m1 (witFS4A (η ix) off (Vt ix) (x ix) (W ix) (A ix) (k ix) (row ix) (tP ix) (S10 ix) (S9 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NS1 ix) (NS2 ix) (NS3 ix) n1 n2 n3 (Com1 ix) (Pf1 ix) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix)).m2 (witFS4A (η ix) off (Vt ix) (x ix) (W ix) (A ix) (k ix) (row ix) (tP ix) (S10 ix) (S9 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NS1 ix) (NS2 ix) (NS3 ix) n1 n2 n3 (Com1 ix) (Pf1 ix) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix)).m3 (witFS4A (η ix) off (Vt ix) (x ix) (W ix) (A ix) (k ix) (row ix) (tP ix) (S10 ix) (S9 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NS1 ix) (NS2 ix) (NS3 ix) n1 n2 n3 (Com1 ix) (Pf1 ix) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix)).q (witFS4A (η ix) off (Vt ix) (x ix) (W ix) (A ix) (k ix) (row ix) (tP ix) (S10 ix) (S9 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NS1 ix) (NS2 ix) (NS3 ix) n1 n2 n3 (Com1 ix) (Pf1 ix) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix)).out) n)
      (pgPowD (fun ix H c xx => prog4 (Q4 * Q4) K2 Q4 K4 H ((witFS4A (η ix) off (Vt ix) (x ix) (W ix) (A ix) (k ix) (row ix) (tP ix) (S10 ix) (S9 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NS1 ix) (NS2 ix) (NS3 ix) n1 n2 n3 (Com1 ix) (Pf1 ix) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix)).pts c xx) c) n) (svPowD (fun ix => (witFS4A (η ix) off (Vt ix) (x ix) (W ix) (A ix) (k ix) (row ix) (tP ix) (S10 ix) (S9 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NS1 ix) (NS2 ix) (NS3 ix) n1 n2 n3 (Com1 ix) (Pf1 ix) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix)).sv) n)
      (errPowD (fun _ => K4 * (Q4 * Q4 * (K2 * Q4))) (fun ix => (witFS4A (η ix) off (Vt ix) (x ix) (W ix) (A ix) (k ix) (row ix) (tP ix) (S10 ix) (S9 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NS1 ix) (NS2 ix) (NS3 ix) n1 n2 n3 (Com1 ix) (Pf1 ix) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix)).sm 2)
        (fun _ => fun (f : Nat × Nat × Nat × Nat → Nat) =>
          sumTo K4 (fun c4 => sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo Q4 (fun c3 => f (c1, c2, c3, c4))))))
        (fun ix => (witFS4A (η ix) off (Vt ix) (x ix) (W ix) (A ix) (k ix) (row ix) (tP ix) (S10 ix) (S9 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NS1 ix) (NS2 ix) (NS3 ix) n1 n2 n3 (Com1 ix) (Pf1 ix) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix)).ε)
        (fun j => sumTo K4 (fun c4 => sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo Q4 (fun c3 =>
          (witFS4A (η j) off (Vt j) (x j) (W j) (A j) (k j) (row j) (tP j) (S10 j) (S9 j) (SP j) (qv j) (wm j) (wc j) (ww j) (wp j) K2 K4 (φ j) N4 (ncw j) (αd j) (B4 j) (fri j) (NR2 j) (Rb j) (Ro j) (NS1 j) (NS2 j) (NS3 j) n1 n2 n3 (Com1 j) (Pf1 j) (Com2 j) (Pf2 j) (Com3 j) (Pf3 j)).sm 2 (fun _ => sumTo (K4 ^ N4) (fun H4 => sumTo ((Q4 * Q4) ^ n1) (fun H1 =>
            sumTo (K2 ^ (n1 * n2)) (fun H2 => sumTo (Q4 ^ (n1 * (n2 * n3))) (fun H3 =>
              hitBD (fun ix => (witFS4A (η ix) off (Vt ix) (x ix) (W ix) (A ix) (k ix) (row ix) (tP ix) (S10 ix) (S9 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NS1 ix) (NS2 ix) (NS3 ix) n1 n2 n3 (Com1 ix) (Pf1 ix) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix)).sm 2) (fun ix => (witFS4A (η ix) off (Vt ix) (x ix) (W ix) (A ix) (k ix) (row ix) (tP ix) (S10 ix) (S9 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NS1 ix) (NS2 ix) (NS3 ix) n1 n2 n3 (Com1 ix) (Pf1 ix) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix)).NS * ((witFS4A (η ix) off (Vt ix) (x ix) (W ix) (A ix) (k ix) (row ix) (tP ix) (S10 ix) (S9 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NS1 ix) (NS2 ix) (NS3 ix) n1 n2 n3 (Com1 ix) (Pf1 ix) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix)).NR * (Q4 ^ 2 * δs ix))) j)))))))))) n) := by
  intro n
  exact fs4_powD (n1 := n1) hK2 hK4 (fun ix => (witFS4A (η ix) off (Vt ix) (x ix) (W ix) (A ix) (k ix) (row ix) (tP ix) (S10 ix) (S9 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NS1 ix) (NS2 ix) (NS3 ix) n1 n2 n3 (Com1 ix) (Pf1 ix) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix)))
    (fun ix c1 x => (Nat.add_mul_mod_self_left _ _ _).trans (Nat.mod_eq_of_lt (hr1 ix _ _)))
    (fun ix c1 c2 x => (Nat.add_mul_mod_self_left _ _ _).trans (Nat.mod_eq_of_lt (hr1 ix _ _)))
    (fun ix c x => (Nat.add_mul_mod_self_left _ _ _).trans (Nat.mod_eq_of_lt (hr1 ix _ _)))
    (fun ix c x => (Nat.add_mul_mod_self_left _ _ _).trans (Nat.mod_eq_of_lt (hr1 ix _ _)))
    (fun i j c1 c2 c3 x c xa h => hφs i j _ _ _ _ h)
    (fun ix => (witFS4A (η ix) off (Vt ix) (x ix) (W ix) (A ix) (k ix) (row ix) (tP ix) (S10 ix) (S9 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NS1 ix) (NS2 ix) (NS3 ix) n1 n2 n3 (Com1 ix) (Pf1 ix) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix)).NS * ((witFS4A (η ix) off (Vt ix) (x ix) (W ix) (A ix) (k ix) (row ix) (tP ix) (S10 ix) (S9 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NS1 ix) (NS2 ix) (NS3 ix) n1 n2 n3 (Com1 ix) (Pf1 ix) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix)).NR * (Q4 ^ 2 * δs ix)))
    (fun ix v => spread_sum (Com1 ix) (witMain1 V Wv off (Vt ix) (x ix) (W ix) (A ix) (k ix) (row ix) (tP ix) (S10 ix) (S9 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (ncw ix) (αd ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix)) (hsp ix) v)
    (fun ix => wit_fs4A off (hwf ix) (hwl ix) (hW8 ix) (hA ix) (hK ix) (hlen ix) (hk ix) (htp ix) (S10 ix) (S9 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (hlwm ix) (hlwc ix) (hlww ix) (hlwp ix) hK2 hK4 (φ ix) (hφ ix) (hS10 ix) (hS9 ix) (hSP ix) (hsz10 ix) (hsz9 ix) (hszP ix) (αd ix) (hB4 ix) (fri ix) (hncw ix) (NR2 ix) (Rb ix) (Ro ix) (Com1 ix) (Pf1 ix) (hc1 ix) (hp1 ix) (hr1 ix) (d1 ix) (Com2 ix) (Pf2 ix) (hc2 ix) (hp2 ix) (hr2 ix) (d2 ix) (Com3 ix) (Pf3 ix) (hc3 ix) (hp3 ix) (hr3 ix) (d3 ix)) n

set_option maxRecDepth 100000 in
/-- **`comp_fs_open4_powD` with each first commitment hiding up to `η ix`**:
    `fs4_powD` at `compFS4A`, each statement's error gaining its `η` term
    (`comp_fs4A`).  One direction. -/
theorem comp_fs_open4_powDA {V Wv P1 P2 P3 : Type}  (off : EF → String → EF) {R Lm : ∀ ix : Nat, Nat} (hR : ∀ ix : Nat, (R ix) ≤ 20) {shp : ∀ ix : Nat, BT} {Ps : ∀ ix : Nat, List Term} {W : ∀ ix : Nat, Nat} {ρ : ∀ ix : Nat, Nat → Bool} {region : ∀ ix : Nat, List Cell} (hrl : ∀ ix : Nat, (region ix).length = (W ix)) (hr : ∀ ix : Nat, ∀ i c, (region ix)[i]? = some c → cellOK (BT.nleaves (shp ix) + 3 + i) c = true) {A : ∀ ix : Nat, List Cell} {e : ∀ ix : Nat, Nat → Nat} {row : ∀ ix : Nat, Nat → Air.Row} (hA : ∀ ix : Nat, AcceptsC (A ix) (cMachine (ρ ix) (shp ix) (region ix) (Ps ix)) (cHeap (ρ ix) (shp ix) (region ix) (Ps ix)).2
      (cHeap (ρ ix) (shp ix) (region ix) (Ps ix)).1.length (Ps ix).length (e ix) (row ix)) (hlen : ∀ ix : Nat, (A ix).length = 2 ^ (Lm ix)) (hLm : ∀ ix : Nat, (Lm ix) ≤ 20) (hK : ∀ ix : Nat, (e ix) ((Ps ix).length - 1) < 2 ^ (R ix)) (hNW : ∀ ix : Nat, BT.nleaves (shp ix) + (W ix) ≤ 2 ^ 8) {tbM tbC tpP tpS : ∀ ix : Nat, Nat} (htM : ∀ ix : Nat, (tbM ix) + 1 = (Lm ix)) (htC : ∀ ix : Nat, (tbC ix) + 1 = (R ix)) (htP : ∀ ix : Nat, (tpP ix) = progTpC (blankM (shp ix) (W ix) (Ps ix)).heap (BT.nleaves (shp ix)) (W ix)) (htS : ∀ ix : Nat, (tpS ix) = segTp (blankRoots (shp ix) (W ix) (Ps ix))) (SM SC S9 SP SS : ∀ ix : Nat, Nat → List F) (qv : ∀ ix : Nat, EF → EF → List EF → F → List F → List F → List EF) (wm wc ww wp wsg : ∀ ix : Nat, Nat → List (EF → EF → List F)) {Lwm Lwc Lww Lwp Lwsg : ∀ ix : Nat, Nat} (hlwm : ∀ ix : Nat, ∀ c, ((wm ix) c).length = (Lwm ix)) (hlwc : ∀ ix : Nat, ∀ c, ((wc ix) c).length = (Lwc ix)) (hlww : ∀ ix : Nat, ∀ c, ((ww ix) c).length = (Lww ix)) (hlwp : ∀ ix : Nat, ∀ c, ((wp ix) c).length = (Lwp ix)) (hlwsg : ∀ ix : Nat, ∀ c, ((wsg ix) c).length = (Lwsg ix)) {K2 K4 : Nat} (hK2 : 0 < K2) (hK4 : 0 < K4) (φ : ∀ ix : Nat, Nat → Option (List (List (List EF)) × List (List (List (List EF))) × List (List (List EF))) → Nat) {N4 : Nat} (hφ : ∀ ix : Nat, ∀ m w, (φ ix) m w < N4) (hSM : ∀ ix : Nat, ∀ c4, ∀ x ∈ (SM ix) c4, x ∉ cosetL 1 (bbGen ((tbM ix) + 1)) (2 ^ ((tbM ix) + 1))) (hSC : ∀ ix : Nat, ∀ c4, ∀ x ∈ (SC ix) c4, x ∉ cosetL 1 (bbGen ((tbC ix) + 1)) (2 ^ ((tbC ix) + 1))) (hS9 : ∀ ix : Nat, ∀ c4, ∀ x ∈ (S9 ix) c4, x ∉ cosetL 1 (bbGen 9) (2 ^ 9)) (hSP : ∀ ix : Nat, ∀ c4, ∀ x ∈ (SP ix) c4, x ∉ cosetL 1 (bbGen ((tpP ix) + 1)) (2 ^ ((tpP ix) + 1))) (hSS : ∀ ix : Nat, ∀ c4, ∀ x ∈ (SS ix) c4, x ∉ cosetL 1 (bbGen ((tpS ix) + 1)) (2 ^ ((tpS ix) + 1))) (hszM : ∀ ix : Nat, ∀ c4, 2 * ((SM ix) c4).length + 8 ≤ 2 ^ ((tbM ix) + 1)) (hszC : ∀ ix : Nat, ∀ c4, 2 * ((SC ix) c4).length + 8 ≤ 2 ^ ((tbC ix) + 1)) (hsz9 : ∀ ix : Nat, ∀ c4, 2 * ((S9 ix) c4).length + 8 ≤ 2 ^ 9) (hszP : ∀ ix : Nat, ∀ c4, 2 * ((SP ix) c4).length + 8 ≤ 2 ^ ((tpP ix) + 1)) (hszS : ∀ ix : Nat, ∀ c4, 2 * ((SS ix) c4).length + 8 ≤ 2 ^ ((tpS ix) + 1)) {ncw : ∀ ix : Nat, Nat} (αd : ∀ ix : Nat, Nat → EF) {B4 : ∀ ix : Nat, Nat} (hB4 : ∀ ix : Nat, sumTo K4 (fun c4 => indB (!genB ((αd ix) c4))) ≤ (B4 ix)) (fri : ∀ ix : Nat, Nat → EF → EF → List (EF → EF) → V) (hncw : ∀ ix : Nat, 4 ≤ (ncw ix)) (NR2 : ∀ ix : Nat, Nat) (Rb : ∀ ix : Nat, Nat → EF → EF → Nat → List (EF → EF)) (Ro : ∀ ix : Nat, Nat → EF → EF → Nat → Wv) {n1 n2 n3 : Nat} {NS1 NS2 NS3 : ∀ ix : Nat, Nat} (Com1 : ∀ ix : Nat, List (List (List F)) → Nat → Nat) (Pf1 : ∀ ix : Nat, Nat → List (List (List F)) → Nat → P1) (η : Nat → Nat) (hc1 : ∀ ix : Nat, ComHidesA (NS1 ix) (η ix) (Com1 ix)) (hp1 : ∀ ix : Nat, ∀ c4, ComPfHidesA (NS1 ix) (η ix) (Com1 ix) ((Pf1 ix) c4) (opF ((cGroups (tbM ix) (tbC ix) (tpP ix) (tpS ix) ((SM ix) c4) ((SC ix) c4) ((S9 ix) c4) ((SP ix) c4) ((SS ix) c4) EF.zero (qv ix)).map (·.base.S)) [0, 2, 4, 6, 8])) (hr1 : ∀ ix : Nat, ∀ d σ, (Com1 ix) d σ < n1) (d1 : ∀ ix : Nat, List (List (List F))) (Com2 : ∀ ix : Nat, List (List (List F)) → Nat → Nat) (Pf2 : ∀ ix : Nat, Nat → List (List (List F)) → Nat → P2) (hc2 : ∀ ix : Nat, ComHides (NS2 ix) (Com2 ix)) (hp2 : ∀ ix : Nat, ∀ c4, ComPfHides (NS2 ix) (Com2 ix) ((Pf2 ix) c4) (opF ((cGroups (tbM ix) (tbC ix) (tpP ix) (tpS ix) ((SM ix) c4) ((SC ix) c4) ((S9 ix) c4) ((SP ix) c4) ((SS ix) c4) EF.zero (qv ix)).map (·.base.S)) [1, 3, 5, 7, 9])) (hr2 : ∀ ix : Nat, ∀ d σ, (Com2 ix) d σ < n2) (d2 : ∀ ix : Nat, List (List (List F))) (Com3 : ∀ ix : Nat, List (List (List (List F))) × List (List (List F)) → Nat → Nat) (Pf3 : ∀ ix : Nat, Nat → List (List (List (List F))) × List (List (List F)) → Nat → P3) (hc3 : ∀ ix : Nat, ComHides (NS3 ix) (Com3 ix)) (hp3 : ∀ ix : Nat, ∀ c4, ComPfHides (NS3 ix) (Com3 ix) ((Pf3 ix) c4) (fun d => (opQ (cSsT ((SM ix) c4) ((SC ix) c4) ((S9 ix) c4) ((SP ix) c4) ((SS ix) c4)) d.1, opCw (cSsC (tbM ix) (tbC ix) (tpP ix) (tpS ix) ((SM ix) c4) ((SC ix) c4) ((S9 ix) c4) ((SP ix) c4) ((SS ix) c4)) d.2))) (hr3 : ∀ ix : Nat, ∀ d σ, (Com3 ix) d σ < n3) (d3 : ∀ ix : Nat, List (List (List (List F))) × List (List (List F)))
    (hφs : ∀ i j m w m' w', φ i m w = φ j m' w' → m % n1 = m' % n1) (δs : Nat → Nat)
    (hsp : ∀ ix d v, sumTo (NS1 ix) (fun σ => indB (decide (Com1 ix d σ = v))) ≤ δs ix) :
    ∀ n, ZKB (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo (K4 ^ N4) (fun H4 => sumTo ((Q4 * Q4) ^ n1) (fun H1 =>
        sumTo (K2 ^ (n1 * n2)) (fun H2 => sumTo (Q4 ^ (n1 * (n2 * n3))) (fun H3 => f (H1, H2, H3, H4))))))
      (KPowD (fun _ => K4 * (Q4 * Q4 * (K2 * Q4))) n)
      (smPowD (X := fun _ => Nat × Nat × Nat × (Nat → Tup)) (fun ix => (compFS4A (η ix) off (R ix) (shp ix) (Ps ix) (W ix) (A ix) (e ix) (row ix) (tbM ix) (tbC ix) (tpP ix) (tpS ix) (SM ix) (SC ix) (S9 ix) (SP ix) (SS ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (wsg ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NS1 ix) (NS2 ix) (NS3 ix) n1 n2 n3 (Com1 ix) (Pf1 ix) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix)).sm 2) n)
      (scPowD (C := fun _ => Nat × Nat × Nat × Nat) (fun _ => fun (f : Nat × Nat × Nat × Nat → Nat) =>
        sumTo K4 (fun c4 => sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo Q4 (fun c3 => f (c1, c2, c3, c4)))))) n)
      (rvPowD (fun ix => read4 (Q4 * Q4) K2 Q4 K4 (compFS4A (η ix) off (R ix) (shp ix) (Ps ix) (W ix) (A ix) (e ix) (row ix) (tbM ix) (tbC ix) (tpP ix) (tpS ix) (SM ix) (SC ix) (S9 ix) (SP ix) (SS ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (wsg ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NS1 ix) (NS2 ix) (NS3 ix) n1 n2 n3 (Com1 ix) (Pf1 ix) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix)).m1 (compFS4A (η ix) off (R ix) (shp ix) (Ps ix) (W ix) (A ix) (e ix) (row ix) (tbM ix) (tbC ix) (tpP ix) (tpS ix) (SM ix) (SC ix) (S9 ix) (SP ix) (SS ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (wsg ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NS1 ix) (NS2 ix) (NS3 ix) n1 n2 n3 (Com1 ix) (Pf1 ix) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix)).m2 (compFS4A (η ix) off (R ix) (shp ix) (Ps ix) (W ix) (A ix) (e ix) (row ix) (tbM ix) (tbC ix) (tpP ix) (tpS ix) (SM ix) (SC ix) (S9 ix) (SP ix) (SS ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (wsg ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NS1 ix) (NS2 ix) (NS3 ix) n1 n2 n3 (Com1 ix) (Pf1 ix) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix)).m3 (compFS4A (η ix) off (R ix) (shp ix) (Ps ix) (W ix) (A ix) (e ix) (row ix) (tbM ix) (tbC ix) (tpP ix) (tpS ix) (SM ix) (SC ix) (S9 ix) (SP ix) (SS ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (wsg ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NS1 ix) (NS2 ix) (NS3 ix) n1 n2 n3 (Com1 ix) (Pf1 ix) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix)).q (compFS4A (η ix) off (R ix) (shp ix) (Ps ix) (W ix) (A ix) (e ix) (row ix) (tbM ix) (tbC ix) (tpP ix) (tpS ix) (SM ix) (SC ix) (S9 ix) (SP ix) (SS ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (wsg ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NS1 ix) (NS2 ix) (NS3 ix) n1 n2 n3 (Com1 ix) (Pf1 ix) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix)).out) n)
      (pgPowD (fun ix H c x => prog4 (Q4 * Q4) K2 Q4 K4 H ((compFS4A (η ix) off (R ix) (shp ix) (Ps ix) (W ix) (A ix) (e ix) (row ix) (tbM ix) (tbC ix) (tpP ix) (tpS ix) (SM ix) (SC ix) (S9 ix) (SP ix) (SS ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (wsg ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NS1 ix) (NS2 ix) (NS3 ix) n1 n2 n3 (Com1 ix) (Pf1 ix) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix)).pts c x) c) n) (svPowD (fun ix => (compFS4A (η ix) off (R ix) (shp ix) (Ps ix) (W ix) (A ix) (e ix) (row ix) (tbM ix) (tbC ix) (tpP ix) (tpS ix) (SM ix) (SC ix) (S9 ix) (SP ix) (SS ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (wsg ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NS1 ix) (NS2 ix) (NS3 ix) n1 n2 n3 (Com1 ix) (Pf1 ix) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix)).sv) n)
      (errPowD (fun _ => K4 * (Q4 * Q4 * (K2 * Q4))) (fun ix => (compFS4A (η ix) off (R ix) (shp ix) (Ps ix) (W ix) (A ix) (e ix) (row ix) (tbM ix) (tbC ix) (tpP ix) (tpS ix) (SM ix) (SC ix) (S9 ix) (SP ix) (SS ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (wsg ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NS1 ix) (NS2 ix) (NS3 ix) n1 n2 n3 (Com1 ix) (Pf1 ix) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix)).sm 2)
        (fun _ => fun (f : Nat × Nat × Nat × Nat → Nat) =>
          sumTo K4 (fun c4 => sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo Q4 (fun c3 => f (c1, c2, c3, c4))))))
        (fun ix => (compFS4A (η ix) off (R ix) (shp ix) (Ps ix) (W ix) (A ix) (e ix) (row ix) (tbM ix) (tbC ix) (tpP ix) (tpS ix) (SM ix) (SC ix) (S9 ix) (SP ix) (SS ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (wsg ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NS1 ix) (NS2 ix) (NS3 ix) n1 n2 n3 (Com1 ix) (Pf1 ix) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix)).ε)
        (fun j => sumTo K4 (fun c4 => sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo Q4 (fun c3 =>
          (compFS4A (η j) off (R j) (shp j) (Ps j) (W j) (A j) (e j) (row j) (tbM j) (tbC j) (tpP j) (tpS j) (SM j) (SC j) (S9 j) (SP j) (SS j) (qv j) (wm j) (wc j) (ww j) (wp j) (wsg j) K2 K4 (φ j) N4 (ncw j) (αd j) (B4 j) (fri j) (NR2 j) (Rb j) (Ro j) (NS1 j) (NS2 j) (NS3 j) n1 n2 n3 (Com1 j) (Pf1 j) (Com2 j) (Pf2 j) (Com3 j) (Pf3 j)).sm 2 (fun _ => sumTo (K4 ^ N4) (fun H4 => sumTo ((Q4 * Q4) ^ n1) (fun H1 =>
            sumTo (K2 ^ (n1 * n2)) (fun H2 => sumTo (Q4 ^ (n1 * (n2 * n3))) (fun H3 =>
              hitBD (fun ix => (compFS4A (η ix) off (R ix) (shp ix) (Ps ix) (W ix) (A ix) (e ix) (row ix) (tbM ix) (tbC ix) (tpP ix) (tpS ix) (SM ix) (SC ix) (S9 ix) (SP ix) (SS ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (wsg ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NS1 ix) (NS2 ix) (NS3 ix) n1 n2 n3 (Com1 ix) (Pf1 ix) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix)).sm 2) (fun ix => (compFS4A (η ix) off (R ix) (shp ix) (Ps ix) (W ix) (A ix) (e ix) (row ix) (tbM ix) (tbC ix) (tpP ix) (tpS ix) (SM ix) (SC ix) (S9 ix) (SP ix) (SS ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (wsg ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NS1 ix) (NS2 ix) (NS3 ix) n1 n2 n3 (Com1 ix) (Pf1 ix) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix)).NS * ((compFS4A (η ix) off (R ix) (shp ix) (Ps ix) (W ix) (A ix) (e ix) (row ix) (tbM ix) (tbC ix) (tpP ix) (tpS ix) (SM ix) (SC ix) (S9 ix) (SP ix) (SS ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (wsg ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NS1 ix) (NS2 ix) (NS3 ix) n1 n2 n3 (Com1 ix) (Pf1 ix) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix)).NR * (Q4 ^ 2 * δs ix))) j)))))))))) n) := by
  intro n
  exact fs4_powD (n1 := n1) hK2 hK4 (fun ix => (compFS4A (η ix) off (R ix) (shp ix) (Ps ix) (W ix) (A ix) (e ix) (row ix) (tbM ix) (tbC ix) (tpP ix) (tpS ix) (SM ix) (SC ix) (S9 ix) (SP ix) (SS ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (wsg ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NS1 ix) (NS2 ix) (NS3 ix) n1 n2 n3 (Com1 ix) (Pf1 ix) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix)))
    (fun ix c1 x => (Nat.add_mul_mod_self_left _ _ _).trans (Nat.mod_eq_of_lt (hr1 ix _ _)))
    (fun ix c1 c2 x => (Nat.add_mul_mod_self_left _ _ _).trans (Nat.mod_eq_of_lt (hr1 ix _ _)))
    (fun ix c x => (Nat.add_mul_mod_self_left _ _ _).trans (Nat.mod_eq_of_lt (hr1 ix _ _)))
    (fun ix c x => (Nat.add_mul_mod_self_left _ _ _).trans (Nat.mod_eq_of_lt (hr1 ix _ _)))
    (fun i j c1 c2 c3 x c xa h => hφs i j _ _ _ _ h)
    (fun ix => (compFS4A (η ix) off (R ix) (shp ix) (Ps ix) (W ix) (A ix) (e ix) (row ix) (tbM ix) (tbC ix) (tpP ix) (tpS ix) (SM ix) (SC ix) (S9 ix) (SP ix) (SS ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (wsg ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NS1 ix) (NS2 ix) (NS3 ix) n1 n2 n3 (Com1 ix) (Pf1 ix) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix)).NS * ((compFS4A (η ix) off (R ix) (shp ix) (Ps ix) (W ix) (A ix) (e ix) (row ix) (tbM ix) (tbC ix) (tpP ix) (tpS ix) (SM ix) (SC ix) (S9 ix) (SP ix) (SS ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (wsg ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NS1 ix) (NS2 ix) (NS3 ix) n1 n2 n3 (Com1 ix) (Pf1 ix) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix)).NR * (Q4 ^ 2 * δs ix)))
    (fun ix v => spread_sum (Com1 ix) (compMain1 V Wv off (R ix) (shp ix) (Ps ix) (W ix) (A ix) (e ix) (row ix) (tbM ix) (tbC ix) (tpP ix) (tpS ix) (SM ix) (SC ix) (S9 ix) (SP ix) (SS ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (wsg ix) (ncw ix) (αd ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix)) (hsp ix) v)
    (fun ix => comp_fs4A off (hR ix) (hrl ix) (hr ix) (hA ix) (hlen ix) (hLm ix) (hK ix) (hNW ix) (htM ix) (htC ix) (htP ix) (htS ix) (SM ix) (SC ix) (S9 ix) (SP ix) (SS ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (wsg ix) (hlwm ix) (hlwc ix) (hlww ix) (hlwp ix) (hlwsg ix) hK2 hK4 (φ ix) (hφ ix) (hSM ix) (hSC ix) (hS9 ix) (hSP ix) (hSS ix) (hszM ix) (hszC ix) (hsz9 ix) (hszP ix) (hszS ix) (αd ix) (hB4 ix) (fri ix) (hncw ix) (NR2 ix) (Rb ix) (Ro ix) (Com1 ix) (Pf1 ix) (hc1 ix) (hp1 ix) (hr1 ix) (d1 ix) (Com2 ix) (Pf2 ix) (hc2 ix) (hp2 ix) (hr2 ix) (d2 ix) (Com3 ix) (Pf3 ix) (hc3 ix) (hp3 ix) (hr3 ix) (d3 ix)) n

end

end Circuit
