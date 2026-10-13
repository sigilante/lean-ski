import Ski.ZK.ROMInst
import Ski.ZK.FSQueryT

/-!
# The circuits' four-round proofs over the oracle's commitment, the queries reading the tables

`ROMInst` with the distinguisher's queries `nxtT` and the later openings
`Pf2T`, `Pf3T` reading the four Fiat–Shamir tables, each side's own (the
real tables, the simulator's programmed ones): the transfer
runs at each choice of tables (`rom4_transferT`), and `FSQueryT`'s
instances hold at the ideal opening (`sud_fs_open4ROMT`,
`wit_fs_open4ROMT`, `comp_fs_open4ROMT`).  One direction.  The queries read
the tables, the first commitment's value and its opened data, not the
later commitments, their openings or the transcript; `ROMInst`'s other
limits hold.
-/
set_option autoImplicit false

namespace Circuit
open ZKF

/-- The four-round real count of `fs_open4T`'s left side at `n1 = K`, its
    first commitment `Com1` and opening `Pf1` at salt range `NS1`, the
    openings reading the four tables. -/
def real4T {PV PB D O1 P1 D2 O2 P2 D3 O3 P3 W : Type} (K NR m NS2 NS3 K2 K3 K4 N4 n2 n3 : Nat)
    (φ : Nat → W → Nat) (rv : Nat → Nat → Nat → EF → EF → Nat → (Nat → Tup) → TViewN PV PB)
    (oz : TViewN PV PB → W) (ov1 : Nat → TViewN PV PB → Option O1) (main1 : (Nat → Tup) → Nat → D)
    (Com2 : D2 → Nat → Nat) (Pf2 : Nat → Nat → Nat → Nat → Nat → Nat → D2 → Nat → P2) (ov2 : Nat → TViewN PV PB → Option O2)
    (main2 : Nat → (Nat → Tup) → Nat → D2)
    (Com3 : D3 → Nat → Nat) (Pf3 : Nat → Nat → Nat → Nat → Nat → Nat → D3 → Nat → P3) (ov3 : Nat → TViewN PV PB → Option O3)
    (main3 : Nat → Nat → (Nat → Tup) → Nat → D3)
    (E : Nat → Nat → Nat → Nat → Nat → Nat → Nat → Option P1 × Option (P2 × P3) × TViewN PV PB → Bool)
    (Com1 : D → Nat → Nat) (Pf1 : Nat → Nat → Nat → Nat → Nat → Nat → D → Nat → P1) (NS1 : Nat) : Nat :=
  let sm := fun (g : Nat × Nat × Nat × (Nat → Tup) → Nat) =>
    sumTo NS1 (fun σ1 => sumTo (NS2 * NS3) (fun σ => sumTo NR (fun r => sumN m (fun t => g (σ1, σ, r, t)))))
  let m1 := fun (x : Nat × Nat × Nat × (Nat → Tup)) => Com1 (main1 x.2.2.2 x.2.2.1) x.1
  let m2 := fun (c1 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
    m1 x + K * Com2 (main2 c1 x.2.2.2 x.2.2.1) (x.2.1 % NS2)
  let m3 := fun (c1 c2 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
    m1 x + K * comPair NS2 n2 Com2 Com3 (main2 c1 x.2.2.2 x.2.2.1, main3 c1 c2 x.2.2.2 x.2.2.1) x.2.1
  let rvo := fun (T1 T2 T3 T4 c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
    ((ov1 c4 (rv c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)).map (fun _ => Pf1 c4 T1 T2 T3 T4 (m3 c1 c2 x) (main1 x.2.2.2 x.2.2.1) x.1),
     (ovPair (ov2 c4) (ov3 c4) (rv c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)).map
       (fun _ => pfPair NS2 (Pf2 c4 T1 T2 T3 T4 (m3 c1 c2 x)) (Pf3 c4 T1 T2 T3 T4 (m3 c1 c2 x)) (main2 c1 x.2.2.2 x.2.2.1, main3 c1 c2 x.2.2.2 x.2.2.1) x.2.1),
     rv c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)
  let sm4 := fun (g : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup)) → Nat) =>
    sumTo ((Q4 * Q4) ^ K) (fun H1 => sumTo (K2 ^ (K * n2)) (fun H2 =>
      sumTo (K3 ^ (K * (n2 * n3))) (fun H3 => sm (fun x => g (H1, H2, H3, x)))))
  let r1 := fun (y : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup))) => rget (Q4 * Q4) (m1 y.2.2.2) y.1
  let r2 := fun (y : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup))) => rget K2 (m2 (r1 y) y.2.2.2) y.2.1
  let r3 := fun (y : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup))) => rget K3 (m3 (r1 y) (r2 y) y.2.2.2) y.2.2.1
  let Mq := fun (y : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup))) => φ (m3 (r1 y) (r2 y) y.2.2.2)
    (oz (rv 0 (r2 y) (r3 y) (efOf (r1 y / Q4)) (efOf (r1 y % Q4)) y.2.2.2.2.2.1 y.2.2.2.2.2.2))
  K4 * (Q4 * Q4 * (K2 * K3) * sumTo (K4 ^ N4) (fun H4 => sm4 (fun y =>
    indB (E y.1 y.2.1 y.2.2.1 H4 (m1 y.2.2.2) (m2 (r1 y) y.2.2.2) (m3 (r1 y) (r2 y) y.2.2.2)
      (rvo y.1 y.2.1 y.2.2.1 H4 (rget K4 (Mq y) H4) (r1 y) (r2 y) (r3 y) y.2.2.2)))))


/-- **The four-round transfer, the queries and openings reading the
    tables**: `rom4_transfer` with the queries `nxtT` at the tables and the
    later openings reading the four tables, the transfer at each choice of
    tables.  Any instance of `fs_open4T` at the ideal opening then bounds
    the real count with the oracle's commitment. -/
theorem rom4_transferT {PV PB D O Pq D2 O2 P2 D3 O3 P3 W : Type}
    {K NR m NSh NSo s k n NS2 NS3 K2 K3 K4 N4 n2 n3 : Nat} (hK : 0 < K)
    (φ : Nat → W → Nat) (rv : Nat → Nat → Nat → EF → EF → Nat → (Nat → Tup) → TViewN PV PB)
    (oz : TViewN PV PB → W)
    (pos : D → Nat → Nat → Nat) (hpos : ∀ d σo σh, pos d σo σh < n) (g : O → Nat → Pq)
    (hs : ∀ d σo v, sumTo NSh (fun σh => indB (decide (pos d σo σh = v))) ≤ s)
    (nxtT : Nat → Nat → Nat → Nat → Pq → Nat → List Nat → Nat) (op1 : Nat → D → O)
    (ov1 : Nat → TViewN PV PB → Option O) (main1 : (Nat → Tup) → Nat → D)
    (Com2 : D2 → Nat → Nat) (Pf2 : Nat → Nat → Nat → Nat → Nat → Nat → D2 → Nat → P2) (ov2 : Nat → TViewN PV PB → Option O2)
    (main2 : Nat → (Nat → Tup) → Nat → D2)
    (Com3 : D3 → Nat → Nat) (Pf3 : Nat → Nat → Nat → Nat → Nat → Nat → D3 → Nat → P3) (ov3 : Nat → TViewN PV PB → Option O3)
    (main3 : Nat → Nat → (Nat → Tup) → Nat → D3)
    (E : Nat → Nat → Nat → Nat → Nat → Nat → Nat → Option (Pq × List Nat) × Option (P2 × P3) × TViewN PV PB → Bool) :
    K * real4T K NR m NS2 NS3 K2 K3 K4 N4 n2 n3 φ rv oz ov1 main1 Com2 Pf2 ov2 main2 Com3 Pf3 ov3 main3 E
      (comR K NSh NSo pos) (fun c4 T1 T2 T3 T4 _ => pfR K NSh NSo k pos (op1 c4) g (nxtT T1 T2 T3 T4)) (NSh * (NSo * K ^ n)) ≤
    real4T K NR m NS2 NS3 K2 K3 K4 N4 n2 n3 φ rv oz ov1 main1 Com2 Pf2 ov2 main2 Com3 Pf3 ov3 main3 E
      (comI K NSh NSo pos) (fun c4 T1 T2 T3 T4 _ => pfI K NSh NSo k pos (op1 c4) g (nxtT T1 T2 T3 T4)) (NSh * (NSo * K ^ n) * K) +
      K4 * (Q4 * Q4 * (K2 * K3) * (K4 ^ N4 * ((Q4 * Q4) ^ K * (K2 ^ (K * n2) * (K3 ^ (K * (n2 * n3)) *
        (K * (NSo * (K ^ n * (s * k))) * (NS2 * NS3 * (NR * (Q4 ^ m * 1))))))))) := by
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
         (fun _ => pfPair NS2 (Pf2 c4 H1 H2 H3 H4 mm3) (Pf3 c4 H1 H2 H3 H4 mm3) (main2 c1 y.2.2 y.2.1, main3 c1 c2 y.2.2 y.2.1) y.1),
       rv c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) y.2.1 y.2.2)
  have hso := smT_lin (NS2 * NS3) NR m
  have so1 := smT_one (NS2 * NS3) NR m
  have step : ∀ H4 H1 H2 H3,
      K * sumTo (NSh * (NSo * K ^ n)) (fun σ1 => smT (NS2 * NS3) NR m (fun y =>
        indB (ev H1 H2 H3 H4 y (comR K NSh NSo pos (main1 y.2.2 y.2.1) σ1)
        (pfR K NSh NSo k pos (op1 (c4f H1 H2 H3 H4 y (comR K NSh NSo pos (main1 y.2.2 y.2.1) σ1))) g (nxtT H1 H2 H3 H4)
          (main1 y.2.2 y.2.1) σ1)))) ≤
      sumTo (NSh * (NSo * K ^ n) * K) (fun σ1 => smT (NS2 * NS3) NR m (fun y =>
        indB (ev H1 H2 H3 H4 y (comI K NSh NSo pos (main1 y.2.2 y.2.1) σ1)
        (pfI K NSh NSo k pos (op1 (c4f H1 H2 H3 H4 y (comI K NSh NSo pos (main1 y.2.2 y.2.1) σ1))) g (nxtT H1 H2 H3 H4)
          (main1 y.2.2 y.2.1) σ1)))) +
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
  unfold real4T
  rw [hb]
  refine Nat.le_trans (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _
    (sumTo_mono _ (fun H4 _ => sumTo_mono _ (fun H1 _ => sumTo_mono _ (fun H2 _ =>
      sumTo_mono _ (fun H3 _ => step H4 H1 H2 H3))))))) ?_
  simp only [sumTo_add, sumTo_const]
  rw [Nat.mul_add (Q4 * Q4 * (K2 * K3)), Nat.mul_add K4]
  exact Nat.le_refl _

section
open B Air Stmt Mach Sudoku SudokuText Compose CompM Wit

set_option maxRecDepth 100000 in
/-- **`sud_fs_open4ROM` with the queries and later openings reading the
    four tables**: the distinguisher's queries `nxtT` and `Pf2T`, `Pf3T`
    read the Fiat–Shamir tables each side uses (`rom4_transferT`, through
    the ideal opening at which `sud_fs_open4T` holds).
    `KQ` times the real count is at most the simulator's, which commits
    through the ideal opening, plus `sud_fs_open4T`'s errors and `sQ kQ / NSh` a draw;
    one direction. -/
theorem sud_fs_open4ROMT {V Wv Pq P2 P3 : Type} (off : EF → String → EF) {puzzle : List Nat} (hc : CluesOK (cluesOf puzzle))
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
    {NSh NSo sQ kQ nQ KQ NS2 NS3 n2 n3 : Nat} (hKQ : 0 < KQ)
    (pos : List (List (List F)) → Nat → Nat → Nat) (hpos : ∀ d σo σh, pos d σo σh < nQ)
    (g : List (List (List F)) → Nat → Pq)
    (hs : ∀ d σo v, sumTo NSh (fun σh => indB (decide (pos d σo σh = v))) ≤ sQ)
    (nxtT : Nat → Nat → Nat → Nat → Pq → Nat → List Nat → Nat) (d1 : List (List (List F)))
    (Com2 : List (List (List F)) → Nat → Nat) (Pf2T : Nat → Nat → Nat → Nat → Nat → Nat → List (List (List F)) → Nat → P2) (hc2 : ComHides NS2 Com2)
    (hp2 : ∀ c4 T1 T2 T3 T4 M, ComPfHides NS2 Com2 (Pf2T c4 T1 T2 T3 T4 M) (opF ((sudGroups tP (S16 c4) (S10 c4) (SP c4) EF.zero qv).map (·.base.S)) [1, 3, 5, 7]))
    (hr2 : ∀ d σ, Com2 d σ < n2) (d2 : List (List (List F)))
    (Com3 : List (List (List (List F))) × List (List (List F)) → Nat → Nat)
    (Pf3T : Nat → Nat → Nat → Nat → Nat → Nat → List (List (List (List F))) × List (List (List F)) → Nat → P3) (hc3 : ComHides NS3 Com3)
    (hp3 : ∀ c4 T1 T2 T3 T4 M, ComPfHides NS3 Com3 (Pf3T c4 T1 T2 T3 T4 M) (fun d => (opQ (sudSsT (S16 c4) (S10 c4) (SP c4)) d.1, opCw (sudSsC tP (S16 c4) (S10 c4) (SP c4)) d.2)))
    (hr3 : ∀ d σ, Com3 d σ < n3) (d3 : List (List (List (List F))) × List (List (List F)))
    (E : Nat → Nat → Nat → Nat → Nat → Nat → Nat → Option (Pq × List Nat) × Option (P2 × P3) × TViewN (SudPV (V × Wv)) EF → Bool) :
    let opS := fun (c4 : Nat) => opF ((sudGroups tP (S16 c4) (S10 c4) (SP c4) EF.zero qv).map (·.base.S)) [0, 2, 4, 6]
    let Com1 := comR KQ NSh NSo pos
    let Pf1 := fun (c4 T1 T2 T3 T4 _ : Nat) => pfR KQ NSh NSo kQ pos (opS c4) g (nxtT T1 T2 T3 T4)
    let Cmi := comI KQ NSh NSo pos
    let Pfi := fun (c4 T1 T2 T3 T4 _ : Nat) => pfI KQ NSh NSo kQ pos (opS c4) g (nxtT T1 T2 T3 T4)
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
      sumTo (NSh * (NSo * KQ ^ nQ) * KQ) (fun σ1 => sumTo (NS2 * NS3) (fun σ => sumTo NR (fun r => sumN 2 (fun t => g (σ1, σ, r, t)))))
    let smR := fun (g : Nat × Nat × Nat × (Nat → Tup) → Nat) =>
      sumTo (NSh * (NSo * KQ ^ nQ)) (fun σ1 => sumTo (NS2 * NS3) (fun σ => sumTo NR (fun r => sumN 2 (fun t => g (σ1, σ, r, t)))))
    let m1 := fun (x : Nat × Nat × Nat × (Nat → Tup)) => Com1 (main1 x.2.2.2 x.2.2.1) x.1
    let m2 := fun (c1 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      m1 x + KQ * Com2 (main2 c1 x.2.2.2 x.2.2.1) (x.2.1 % NS2)
    let m3 := fun (c1 c2 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      m1 x + KQ * comPair NS2 n2 Com2 Com3 (main2 c1 x.2.2.2 x.2.2.1, main3 c1 c2 x.2.2.2 x.2.2.1) x.2.1
    let rvo := fun (T1 T2 T3 T4 c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      ((ov1 c4 (rvF c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)).map (fun _ => Pf1 c4 T1 T2 T3 T4 (m3 c1 c2 x) (main1 x.2.2.2 x.2.2.1) x.1),
       (ovPair (ov2 c4) (ov3 c4) (rvF c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)).map
         (fun _ => pfPair NS2 (Pf2T c4 T1 T2 T3 T4 (m3 c1 c2 x)) (Pf3T c4 T1 T2 T3 T4 (m3 c1 c2 x)) (main2 c1 x.2.2.2 x.2.2.1, main3 c1 c2 x.2.2.2 x.2.2.1) x.2.1),
       rvF c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)
    let s1 := fun (c4 _c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) => Cmi (sdF (Ss c4) mk1 (sop1 c4 c2 c3 x.2.2.1 x.2.2.2)) x.1
    let s2 := fun (c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      s1 c4 c1 c2 c3 x + KQ * Com2 (sdF (Ss c4) mk2 (sop2 c4 c2 c3 c1 x.2.2.1 x.2.2.2)) (x.2.1 % NS2)
    let s3 := fun (c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      s1 c4 c1 c2 c3 x + KQ * comPair NS2 n2 Com2 Com3
        (sdF (Ss c4) mk2 (sop2 c4 c2 c3 c1 x.2.2.1 x.2.2.2), sd3 c4 (sop3 c4 c2 c3 c1 x.2.2.1 x.2.2.2)) x.2.1
    let svo := fun (T1 T2 T3 T4 c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      (some (Pfi c4 T1 T2 T3 T4 (s3 c4 c1 c2 c3 x) (sdF (Ss c4) mk1 (sop1 c4 c2 c3 x.2.2.1 x.2.2.2)) x.1),
       some (pfPair NS2 (Pf2T c4 T1 T2 T3 T4 (s3 c4 c1 c2 c3 x)) (Pf3T c4 T1 T2 T3 T4 (s3 c4 c1 c2 c3 x)) (sdF (Ss c4) mk2 (sop2 c4 c2 c3 c1 x.2.2.1 x.2.2.2), sd3 c4 (sop3 c4 c2 c3 c1 x.2.2.1 x.2.2.2)) x.2.1),
       svF c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)
    let sm4 := fun (g : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup)) → Nat) =>
      sumTo ((Q4 * Q4) ^ KQ) (fun H1 => sumTo (K2 ^ (KQ * n2)) (fun H2 =>
        sumTo (Q4 ^ (KQ * (n2 * n3))) (fun H3 => sm (fun x => g (H1, H2, H3, x)))))
    let sm4R := fun (g : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup)) → Nat) =>
      sumTo ((Q4 * Q4) ^ KQ) (fun H1 => sumTo (K2 ^ (KQ * n2)) (fun H2 =>
        sumTo (Q4 ^ (KQ * (n2 * n3))) (fun H3 => smR (fun x => g (H1, H2, H3, x)))))
    let r1 := fun (y : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup))) => rget (Q4 * Q4) (m1 y.2.2.2) y.1
    let r2 := fun (y : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup))) => rget K2 (m2 (r1 y) y.2.2.2) y.2.1
    let r3 := fun (y : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup))) => rget Q4 (m3 (r1 y) (r2 y) y.2.2.2) y.2.2.1
    let Mq := fun (y : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup))) => φ (m3 (r1 y) (r2 y) y.2.2.2)
      (ozF (rvF 0 (r2 y) (r3 y) (efOf (r1 y / Q4)) (efOf (r1 y % Q4)) y.2.2.2.2.2.1 y.2.2.2.2.2.2))
    KQ * (K4 * (Q4 * Q4 * (K2 * Q4) * sumTo (K4 ^ N4) (fun H4 => sm4R (fun y =>
        indB (E y.1 y.2.1 y.2.2.1 H4 (m1 y.2.2.2) (m2 (r1 y) y.2.2.2) (m3 (r1 y) (r2 y) y.2.2.2)
          (rvo y.1 y.2.1 y.2.2.1 H4 (rget K4 (Mq y) H4) (r1 y) (r2 y) (r3 y) y.2.2.2)))))) ≤
      sumTo (K4 ^ N4) (fun H4 => sumTo K4 (fun c4 =>
        sumTo ((Q4 * Q4) ^ KQ) (fun H1 => sumTo (K2 ^ (KQ * n2)) (fun H2 => sumTo (Q4 ^ (KQ * (n2 * n3))) (fun H3 =>
        sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo Q4 (fun c3 => sm (fun x =>
          indB (E (rset (Q4 * Q4) (s1 c4 c1 c2 c3 x) H1 c1) (rset K2 (s2 c4 c1 c2 c3 x) H2 c2)
            (rset Q4 (s3 c4 c1 c2 c3 x) H3 c3) (rset K4 (φ (s3 c4 c1 c2 c3 x) (ozF (svF c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2))) H4 c4)
            (s1 c4 c1 c2 c3 x) (s2 c4 c1 c2 c3 x) (s3 c4 c1 c2 c3 x)
            (svo (rset (Q4 * Q4) (s1 c4 c1 c2 c3 x) H1 c1) (rset K2 (s2 c4 c1 c2 c3 x) H2 c2) (rset Q4 (s3 c4 c1 c2 c3 x) H3 c3)
              (rset K4 (φ (s3 c4 c1 c2 c3 x) (ozF (svF c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2))) H4 c4)
              c4 c1 c2 c3 x))))))))))) +
        K4 ^ N4 * (K4 * ((Q4 * Q4) ^ KQ * (K2 ^ (KQ * n2) * (Q4 ^ (KQ * (n2 * n3)) *
          (K2 * (Q4 * ((NSh * (NSo * KQ ^ nQ) * KQ) * (NS2 * NS3 * (Q4 * (NR * (Q4 ^ 2 * M)) + Q4 * (Q4 * (Q4 ^ 2 * 0)))))) +
            (Q4 * (P * P) * (K2 * Q4) + Q4 * Q4 * (K2 * (P * P))) * ((NSh * (NSo * KQ ^ nQ) * KQ) * (NS2 * NS3 * (NR * (Q4 ^ 2 * 1)))))))) +
            B4 * (Q4 * Q4 * (K2 * Q4) * sm4 (fun _ => 1))) +
      K4 * (Q4 * Q4 * (K2 * Q4) * (K4 ^ N4 * ((Q4 * Q4) ^ KQ * (K2 ^ (KQ * n2) * (Q4 ^ (KQ * (n2 * n3)) *
        (KQ * (NSo * (KQ ^ nQ * (sQ * kQ))) * (NS2 * NS3 * (NR * (Q4 ^ 2 * 1))))))))) := by
  intro opS Com1 Pf1 Cmi Pfi blank C Pg Wt Mm NR0 pcsZ psimZ NR tabs tv tp M q0 qZ Ss ks cols tqZ qdZ SsT SsC mk1 mk2 main1 main2 main3 vS sop1 sop2 sop3 ov1 ov2 ov3 rvF svF ozF op3 sd3 sm smR m1 m2 m3 rvo s1 s2 s3 svo sm4 sm4R r1 r2 r3 Mq
  have fo := (sud_fs_open4T off hc hA hacc hlen hk htp S16 S10 SP qv wm wc ww wp hlwm hlwc hlww hlwp hK2 hK4 φ hφ hS16 hS10 hSP hsz16 hsz hszP αd hB4 fri hncw NR2 Rb Ro Cmi Pfi (comI_hides hKQ pos hpos) (fun c4 T1 T2 T3 T4 _ => pfI_hides hKQ pos hpos (opS c4) g (nxtT T1 T2 T3 T4)) (fun _ _ => Nat.mod_lt _ hKQ) d1 Com2 Pf2T hc2 hp2 hr2 d2 Com3 Pf3T hc3 hp3 hr3 d3 E)
  exact Nat.le_trans (rom4_transferT (K3 := Q4) (m := 2) (NR := NR) (NSh := NSh) (NSo := NSo) (s := sQ) (k := kQ) (n := nQ)
    (NS2 := NS2) (NS3 := NS3) (K2 := K2) (K4 := K4) (N4 := N4) (n2 := n2) (n3 := n3) hKQ φ rvF ozF pos hpos g hs nxtT opS ov1 main1
    Com2 Pf2T ov2 main2 Com3 Pf3T ov3 main3 E) (Nat.add_le_add_right fo _)

set_option maxRecDepth 100000 in
/-- **`wit_fs_open4ROM` with the queries and later openings reading the
    four tables**: the distinguisher's queries `nxtT` and `Pf2T`, `Pf3T`
    read the Fiat–Shamir tables each side uses (`rom4_transferT`, through
    the ideal opening at which `wit_fs_open4T` holds).
    `KQ` times the real count is at most the simulator's, which commits
    through the ideal opening, plus `wit_fs_open4T`'s errors and `sQ kQ / NSh` a draw;
    one direction. -/
theorem wit_fs_open4ROMT {V Wv Pq P2 P3 : Type} (off : EF → String → EF) {Vt x : Term} {W : Nat} {ws : List Cell} (hwf : WF ws)
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
    {NSh NSo sQ kQ nQ KQ NS2 NS3 n2 n3 : Nat} (hKQ : 0 < KQ)
    (pos : List (List (List F)) → Nat → Nat → Nat) (hpos : ∀ d σo σh, pos d σo σh < nQ)
    (g : List (List (List F)) → Nat → Pq)
    (hs : ∀ d σo v, sumTo NSh (fun σh => indB (decide (pos d σo σh = v))) ≤ sQ)
    (nxtT : Nat → Nat → Nat → Nat → Pq → Nat → List Nat → Nat) (d1 : List (List (List F)))
    (Com2 : List (List (List F)) → Nat → Nat) (Pf2T : Nat → Nat → Nat → Nat → Nat → Nat → List (List (List F)) → Nat → P2) (hc2 : ComHides NS2 Com2)
    (hp2 : ∀ c4 T1 T2 T3 T4 M, ComPfHides NS2 Com2 (Pf2T c4 T1 T2 T3 T4 M) (opF ((wGroups tP (S10 c4) (S9 c4) (SP c4) EF.zero qv).map (·.base.S)) [1, 3, 5, 7]))
    (hr2 : ∀ d σ, Com2 d σ < n2) (d2 : List (List (List F)))
    (Com3 : List (List (List (List F))) × List (List (List F)) → Nat → Nat)
    (Pf3T : Nat → Nat → Nat → Nat → Nat → Nat → List (List (List (List F))) × List (List (List F)) → Nat → P3) (hc3 : ComHides NS3 Com3)
    (hp3 : ∀ c4 T1 T2 T3 T4 M, ComPfHides NS3 Com3 (Pf3T c4 T1 T2 T3 T4 M) (fun d => (opQ (wSsT (S10 c4) (S9 c4) (SP c4)) d.1, opCw (wSsC tP (S10 c4) (S9 c4) (SP c4)) d.2)))
    (hr3 : ∀ d σ, Com3 d σ < n3) (d3 : List (List (List (List F))) × List (List (List F)))
    (E : Nat → Nat → Nat → Nat → Nat → Nat → Nat → Option (Pq × List Nat) × Option (P2 × P3) × TViewN (PcsPV (V × Wv)) EF → Bool) :
    let opS := fun (c4 : Nat) => opF ((wGroups tP (S10 c4) (S9 c4) (SP c4) EF.zero qv).map (·.base.S)) [0, 2, 4, 6]
    let Com1 := comR KQ NSh NSo pos
    let Pf1 := fun (c4 T1 T2 T3 T4 _ : Nat) => pfR KQ NSh NSo kQ pos (opS c4) g (nxtT T1 T2 T3 T4)
    let Cmi := comI KQ NSh NSo pos
    let Pfi := fun (c4 T1 T2 T3 T4 _ : Nat) => pfI KQ NSh NSo kQ pos (opS c4) g (nxtT T1 T2 T3 T4)
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
      sumTo (NSh * (NSo * KQ ^ nQ) * KQ) (fun σ1 => sumTo (NS2 * NS3) (fun σ => sumTo NR (fun r => sumN 2 (fun t => g (σ1, σ, r, t)))))
    let smR := fun (g : Nat × Nat × Nat × (Nat → Tup) → Nat) =>
      sumTo (NSh * (NSo * KQ ^ nQ)) (fun σ1 => sumTo (NS2 * NS3) (fun σ => sumTo NR (fun r => sumN 2 (fun t => g (σ1, σ, r, t)))))
    let m1 := fun (x : Nat × Nat × Nat × (Nat → Tup)) => Com1 (main1 x.2.2.2 x.2.2.1) x.1
    let m2 := fun (c1 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      m1 x + KQ * Com2 (main2 c1 x.2.2.2 x.2.2.1) (x.2.1 % NS2)
    let m3 := fun (c1 c2 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      m1 x + KQ * comPair NS2 n2 Com2 Com3 (main2 c1 x.2.2.2 x.2.2.1, main3 c1 c2 x.2.2.2 x.2.2.1) x.2.1
    let rvo := fun (T1 T2 T3 T4 c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      ((ov1 c4 (rvF c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)).map (fun _ => Pf1 c4 T1 T2 T3 T4 (m3 c1 c2 x) (main1 x.2.2.2 x.2.2.1) x.1),
       (ovPair (ov2 c4) (ov3 c4) (rvF c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)).map
         (fun _ => pfPair NS2 (Pf2T c4 T1 T2 T3 T4 (m3 c1 c2 x)) (Pf3T c4 T1 T2 T3 T4 (m3 c1 c2 x)) (main2 c1 x.2.2.2 x.2.2.1, main3 c1 c2 x.2.2.2 x.2.2.1) x.2.1),
       rvF c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)
    let s1 := fun (c4 _c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) => Cmi (sdF (Ss c4) mk1 (sop1 c4 c2 c3 x.2.2.1 x.2.2.2)) x.1
    let s2 := fun (c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      s1 c4 c1 c2 c3 x + KQ * Com2 (sdF (Ss c4) mk2 (sop2 c4 c2 c3 c1 x.2.2.1 x.2.2.2)) (x.2.1 % NS2)
    let s3 := fun (c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      s1 c4 c1 c2 c3 x + KQ * comPair NS2 n2 Com2 Com3
        (sdF (Ss c4) mk2 (sop2 c4 c2 c3 c1 x.2.2.1 x.2.2.2), sd3 c4 (sop3 c4 c2 c3 c1 x.2.2.1 x.2.2.2)) x.2.1
    let svo := fun (T1 T2 T3 T4 c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      (some (Pfi c4 T1 T2 T3 T4 (s3 c4 c1 c2 c3 x) (sdF (Ss c4) mk1 (sop1 c4 c2 c3 x.2.2.1 x.2.2.2)) x.1),
       some (pfPair NS2 (Pf2T c4 T1 T2 T3 T4 (s3 c4 c1 c2 c3 x)) (Pf3T c4 T1 T2 T3 T4 (s3 c4 c1 c2 c3 x)) (sdF (Ss c4) mk2 (sop2 c4 c2 c3 c1 x.2.2.1 x.2.2.2), sd3 c4 (sop3 c4 c2 c3 c1 x.2.2.1 x.2.2.2)) x.2.1),
       svF c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)
    let sm4 := fun (g : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup)) → Nat) =>
      sumTo ((Q4 * Q4) ^ KQ) (fun H1 => sumTo (K2 ^ (KQ * n2)) (fun H2 =>
        sumTo (Q4 ^ (KQ * (n2 * n3))) (fun H3 => sm (fun x => g (H1, H2, H3, x)))))
    let sm4R := fun (g : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup)) → Nat) =>
      sumTo ((Q4 * Q4) ^ KQ) (fun H1 => sumTo (K2 ^ (KQ * n2)) (fun H2 =>
        sumTo (Q4 ^ (KQ * (n2 * n3))) (fun H3 => smR (fun x => g (H1, H2, H3, x)))))
    let r1 := fun (y : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup))) => rget (Q4 * Q4) (m1 y.2.2.2) y.1
    let r2 := fun (y : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup))) => rget K2 (m2 (r1 y) y.2.2.2) y.2.1
    let r3 := fun (y : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup))) => rget Q4 (m3 (r1 y) (r2 y) y.2.2.2) y.2.2.1
    let Mq := fun (y : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup))) => φ (m3 (r1 y) (r2 y) y.2.2.2)
      (ozF (rvF 0 (r2 y) (r3 y) (efOf (r1 y / Q4)) (efOf (r1 y % Q4)) y.2.2.2.2.2.1 y.2.2.2.2.2.2))
    KQ * (K4 * (Q4 * Q4 * (K2 * Q4) * sumTo (K4 ^ N4) (fun H4 => sm4R (fun y =>
        indB (E y.1 y.2.1 y.2.2.1 H4 (m1 y.2.2.2) (m2 (r1 y) y.2.2.2) (m3 (r1 y) (r2 y) y.2.2.2)
          (rvo y.1 y.2.1 y.2.2.1 H4 (rget K4 (Mq y) H4) (r1 y) (r2 y) (r3 y) y.2.2.2)))))) ≤
      sumTo (K4 ^ N4) (fun H4 => sumTo K4 (fun c4 =>
        sumTo ((Q4 * Q4) ^ KQ) (fun H1 => sumTo (K2 ^ (KQ * n2)) (fun H2 => sumTo (Q4 ^ (KQ * (n2 * n3))) (fun H3 =>
        sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo Q4 (fun c3 => sm (fun x =>
          indB (E (rset (Q4 * Q4) (s1 c4 c1 c2 c3 x) H1 c1) (rset K2 (s2 c4 c1 c2 c3 x) H2 c2)
            (rset Q4 (s3 c4 c1 c2 c3 x) H3 c3) (rset K4 (φ (s3 c4 c1 c2 c3 x) (ozF (svF c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2))) H4 c4)
            (s1 c4 c1 c2 c3 x) (s2 c4 c1 c2 c3 x) (s3 c4 c1 c2 c3 x)
            (svo (rset (Q4 * Q4) (s1 c4 c1 c2 c3 x) H1 c1) (rset K2 (s2 c4 c1 c2 c3 x) H2 c2) (rset Q4 (s3 c4 c1 c2 c3 x) H3 c3)
              (rset K4 (φ (s3 c4 c1 c2 c3 x) (ozF (svF c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2))) H4 c4)
              c4 c1 c2 c3 x))))))))))) +
        K4 ^ N4 * (K4 * ((Q4 * Q4) ^ KQ * (K2 ^ (KQ * n2) * (Q4 ^ (KQ * (n2 * n3)) *
          (K2 * (Q4 * ((NSh * (NSo * KQ ^ nQ) * KQ) * (NS2 * NS3 * (Q4 * (NR * (Q4 ^ 2 * M)) + Q4 * (Q4 * (Q4 ^ 2 * 0)))))) +
            (Q4 * (P * P) * (K2 * Q4) + Q4 * Q4 * (K2 * (P * P))) * ((NSh * (NSo * KQ ^ nQ) * KQ) * (NS2 * NS3 * (NR * (Q4 ^ 2 * 1)))))))) +
            B4 * (Q4 * Q4 * (K2 * Q4) * sm4 (fun _ => 1))) +
      K4 * (Q4 * Q4 * (K2 * Q4) * (K4 ^ N4 * ((Q4 * Q4) ^ KQ * (K2 ^ (KQ * n2) * (Q4 ^ (KQ * (n2 * n3)) *
        (KQ * (NSo * (KQ ^ nQ * (sQ * kQ))) * (NS2 * NS3 * (NR * (Q4 ^ 2 * 1))))))))) := by
  intro opS Com1 Pf1 Cmi Pfi blank C Pg Wt Mm NR0 pcsZ psimZ NR tabs tv ptm M q0 qZ Ss ks cols tqZ qdZ SsT SsC mk1 mk2 main1 main2 main3 vS sop1 sop2 sop3 ov1 ov2 ov3 rvF svF ozF op3 sd3 sm smR m1 m2 m3 rvo s1 s2 s3 svo sm4 sm4R r1 r2 r3 Mq
  have fo := (wit_fs_open4T off hwf hwl hW8 hA hK hlen hk htp S10 S9 SP qv wm wc ww wp hlwm hlwc hlww hlwp hK2 hK4 φ hφ hS10 hS9 hSP hsz10 hsz9 hszP αd hB4 fri hncw NR2 Rb Ro Cmi Pfi (comI_hides hKQ pos hpos) (fun c4 T1 T2 T3 T4 _ => pfI_hides hKQ pos hpos (opS c4) g (nxtT T1 T2 T3 T4)) (fun _ _ => Nat.mod_lt _ hKQ) d1 Com2 Pf2T hc2 hp2 hr2 d2 Com3 Pf3T hc3 hp3 hr3 d3 E)
  exact Nat.le_trans (rom4_transferT (K3 := Q4) (m := 2) (NR := NR) (NSh := NSh) (NSo := NSo) (s := sQ) (k := kQ) (n := nQ)
    (NS2 := NS2) (NS3 := NS3) (K2 := K2) (K4 := K4) (N4 := N4) (n2 := n2) (n3 := n3) hKQ φ rvF ozF pos hpos g hs nxtT opS ov1 main1
    Com2 Pf2T ov2 main2 Com3 Pf3T ov3 main3 E) (Nat.add_le_add_right fo _)

set_option maxRecDepth 100000 in
/-- **`comp_fs_open4ROM` with the queries and later openings reading the
    four tables**: the distinguisher's queries `nxtT` and `Pf2T`, `Pf3T`
    read the Fiat–Shamir tables each side uses (`rom4_transferT`, through
    the ideal opening at which `comp_fs_open4T` holds).
    `KQ` times the real count is at most the simulator's, which commits
    through the ideal opening, plus `comp_fs_open4T`'s errors and `sQ kQ / NSh` a draw;
    one direction. -/
theorem comp_fs_open4ROMT {V Wv Pq P2 P3 : Type} (off : EF → String → EF) {R Lm : Nat} (hR : R ≤ 20) {shp : BT} {Ps : List Term}
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
    {NSh NSo sQ kQ nQ KQ NS2 NS3 n2 n3 : Nat} (hKQ : 0 < KQ)
    (pos : List (List (List F)) → Nat → Nat → Nat) (hpos : ∀ d σo σh, pos d σo σh < nQ)
    (g : List (List (List F)) → Nat → Pq)
    (hs : ∀ d σo v, sumTo NSh (fun σh => indB (decide (pos d σo σh = v))) ≤ sQ)
    (nxtT : Nat → Nat → Nat → Nat → Pq → Nat → List Nat → Nat) (d1 : List (List (List F)))
    (Com2 : List (List (List F)) → Nat → Nat) (Pf2T : Nat → Nat → Nat → Nat → Nat → Nat → List (List (List F)) → Nat → P2) (hc2 : ComHides NS2 Com2)
    (hp2 : ∀ c4 T1 T2 T3 T4 M, ComPfHides NS2 Com2 (Pf2T c4 T1 T2 T3 T4 M) (opF ((cGroups tbM tbC tpP tpS (SM c4) (SC c4) (S9 c4) (SP c4) (SS c4) EF.zero qv).map (·.base.S)) [1, 3, 5, 7, 9]))
    (hr2 : ∀ d σ, Com2 d σ < n2) (d2 : List (List (List F)))
    (Com3 : List (List (List (List F))) × List (List (List F)) → Nat → Nat)
    (Pf3T : Nat → Nat → Nat → Nat → Nat → Nat → List (List (List (List F))) × List (List (List F)) → Nat → P3) (hc3 : ComHides NS3 Com3)
    (hp3 : ∀ c4 T1 T2 T3 T4 M, ComPfHides NS3 Com3 (Pf3T c4 T1 T2 T3 T4 M) (fun d => (opQ (cSsT (SM c4) (SC c4) (S9 c4) (SP c4) (SS c4)) d.1, opCw (cSsC tbM tbC tpP tpS (SM c4) (SC c4) (S9 c4) (SP c4) (SS c4)) d.2)))
    (hr3 : ∀ d σ, Com3 d σ < n3) (d3 : List (List (List (List F))) × List (List (List F)))
    (E : Nat → Nat → Nat → Nat → Nat → Nat → Nat → Option (Pq × List Nat) × Option (P2 × P3) × TViewN (PcsPV (V × Wv)) (EF × EF) → Bool) :
    let opS := fun (c4 : Nat) => opF ((cGroups tbM tbC tpP tpS (SM c4) (SC c4) (S9 c4) (SP c4) (SS c4) EF.zero qv).map (·.base.S)) [0, 2, 4, 6, 8]
    let Com1 := comR KQ NSh NSo pos
    let Pf1 := fun (c4 T1 T2 T3 T4 _ : Nat) => pfR KQ NSh NSo kQ pos (opS c4) g (nxtT T1 T2 T3 T4)
    let Cmi := comI KQ NSh NSo pos
    let Pfi := fun (c4 T1 T2 T3 T4 _ : Nat) => pfI KQ NSh NSo kQ pos (opS c4) g (nxtT T1 T2 T3 T4)
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
      sumTo (NSh * (NSo * KQ ^ nQ) * KQ) (fun σ1 => sumTo (NS2 * NS3) (fun σ => sumTo NR (fun r => sumN 2 (fun t => g (σ1, σ, r, t)))))
    let smR := fun (g : Nat × Nat × Nat × (Nat → Tup) → Nat) =>
      sumTo (NSh * (NSo * KQ ^ nQ)) (fun σ1 => sumTo (NS2 * NS3) (fun σ => sumTo NR (fun r => sumN 2 (fun t => g (σ1, σ, r, t)))))
    let m1 := fun (x : Nat × Nat × Nat × (Nat → Tup)) => Com1 (main1 x.2.2.2 x.2.2.1) x.1
    let m2 := fun (c1 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      m1 x + KQ * Com2 (main2 c1 x.2.2.2 x.2.2.1) (x.2.1 % NS2)
    let m3 := fun (c1 c2 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      m1 x + KQ * comPair NS2 n2 Com2 Com3 (main2 c1 x.2.2.2 x.2.2.1, main3 c1 c2 x.2.2.2 x.2.2.1) x.2.1
    let rvo := fun (T1 T2 T3 T4 c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      ((ov1 c4 (rvF c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)).map (fun _ => Pf1 c4 T1 T2 T3 T4 (m3 c1 c2 x) (main1 x.2.2.2 x.2.2.1) x.1),
       (ovPair (ov2 c4) (ov3 c4) (rvF c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)).map
         (fun _ => pfPair NS2 (Pf2T c4 T1 T2 T3 T4 (m3 c1 c2 x)) (Pf3T c4 T1 T2 T3 T4 (m3 c1 c2 x)) (main2 c1 x.2.2.2 x.2.2.1, main3 c1 c2 x.2.2.2 x.2.2.1) x.2.1),
       rvF c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)
    let s1 := fun (c4 _c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) => Cmi (sdF (Ss c4) mk1 (sop1 c4 c2 c3 x.2.2.1 x.2.2.2)) x.1
    let s2 := fun (c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      s1 c4 c1 c2 c3 x + KQ * Com2 (sdF (Ss c4) mk2 (sop2 c4 c2 c3 c1 x.2.2.1 x.2.2.2)) (x.2.1 % NS2)
    let s3 := fun (c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      s1 c4 c1 c2 c3 x + KQ * comPair NS2 n2 Com2 Com3
        (sdF (Ss c4) mk2 (sop2 c4 c2 c3 c1 x.2.2.1 x.2.2.2), sd3 c4 (sop3 c4 c2 c3 c1 x.2.2.1 x.2.2.2)) x.2.1
    let svo := fun (T1 T2 T3 T4 c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      (some (Pfi c4 T1 T2 T3 T4 (s3 c4 c1 c2 c3 x) (sdF (Ss c4) mk1 (sop1 c4 c2 c3 x.2.2.1 x.2.2.2)) x.1),
       some (pfPair NS2 (Pf2T c4 T1 T2 T3 T4 (s3 c4 c1 c2 c3 x)) (Pf3T c4 T1 T2 T3 T4 (s3 c4 c1 c2 c3 x)) (sdF (Ss c4) mk2 (sop2 c4 c2 c3 c1 x.2.2.1 x.2.2.2), sd3 c4 (sop3 c4 c2 c3 c1 x.2.2.1 x.2.2.2)) x.2.1),
       svF c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)
    let sm4 := fun (g : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup)) → Nat) =>
      sumTo ((Q4 * Q4) ^ KQ) (fun H1 => sumTo (K2 ^ (KQ * n2)) (fun H2 =>
        sumTo (Q4 ^ (KQ * (n2 * n3))) (fun H3 => sm (fun x => g (H1, H2, H3, x)))))
    let sm4R := fun (g : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup)) → Nat) =>
      sumTo ((Q4 * Q4) ^ KQ) (fun H1 => sumTo (K2 ^ (KQ * n2)) (fun H2 =>
        sumTo (Q4 ^ (KQ * (n2 * n3))) (fun H3 => smR (fun x => g (H1, H2, H3, x)))))
    let r1 := fun (y : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup))) => rget (Q4 * Q4) (m1 y.2.2.2) y.1
    let r2 := fun (y : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup))) => rget K2 (m2 (r1 y) y.2.2.2) y.2.1
    let r3 := fun (y : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup))) => rget Q4 (m3 (r1 y) (r2 y) y.2.2.2) y.2.2.1
    let Mq := fun (y : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup))) => φ (m3 (r1 y) (r2 y) y.2.2.2)
      (ozF (rvF 0 (r2 y) (r3 y) (efOf (r1 y / Q4)) (efOf (r1 y % Q4)) y.2.2.2.2.2.1 y.2.2.2.2.2.2))
    KQ * (K4 * (Q4 * Q4 * (K2 * Q4) * sumTo (K4 ^ N4) (fun H4 => sm4R (fun y =>
        indB (E y.1 y.2.1 y.2.2.1 H4 (m1 y.2.2.2) (m2 (r1 y) y.2.2.2) (m3 (r1 y) (r2 y) y.2.2.2)
          (rvo y.1 y.2.1 y.2.2.1 H4 (rget K4 (Mq y) H4) (r1 y) (r2 y) (r3 y) y.2.2.2)))))) ≤
      sumTo (K4 ^ N4) (fun H4 => sumTo K4 (fun c4 =>
        sumTo ((Q4 * Q4) ^ KQ) (fun H1 => sumTo (K2 ^ (KQ * n2)) (fun H2 => sumTo (Q4 ^ (KQ * (n2 * n3))) (fun H3 =>
        sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo Q4 (fun c3 => sm (fun x =>
          indB (E (rset (Q4 * Q4) (s1 c4 c1 c2 c3 x) H1 c1) (rset K2 (s2 c4 c1 c2 c3 x) H2 c2)
            (rset Q4 (s3 c4 c1 c2 c3 x) H3 c3) (rset K4 (φ (s3 c4 c1 c2 c3 x) (ozF (svF c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2))) H4 c4)
            (s1 c4 c1 c2 c3 x) (s2 c4 c1 c2 c3 x) (s3 c4 c1 c2 c3 x)
            (svo (rset (Q4 * Q4) (s1 c4 c1 c2 c3 x) H1 c1) (rset K2 (s2 c4 c1 c2 c3 x) H2 c2) (rset Q4 (s3 c4 c1 c2 c3 x) H3 c3)
              (rset K4 (φ (s3 c4 c1 c2 c3 x) (ozF (svF c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2))) H4 c4)
              c4 c1 c2 c3 x))))))))))) +
        K4 ^ N4 * (K4 * ((Q4 * Q4) ^ KQ * (K2 ^ (KQ * n2) * (Q4 ^ (KQ * (n2 * n3)) *
          (K2 * (Q4 * ((NSh * (NSo * KQ ^ nQ) * KQ) * (NS2 * NS3 * (Q4 * (NR * (Q4 ^ 2 * M)) + Q4 * (Q4 * (Q4 ^ 2 * 0)))))) +
            (Q4 * (P * P) * (K2 * Q4) + Q4 * Q4 * (K2 * (P * P))) * ((NSh * (NSo * KQ ^ nQ) * KQ) * (NS2 * NS3 * (NR * (Q4 ^ 2 * 1)))))))) +
            B4 * (Q4 * Q4 * (K2 * Q4) * sm4 (fun _ => 1))) +
      K4 * (Q4 * Q4 * (K2 * Q4) * (K4 ^ N4 * ((Q4 * Q4) ^ KQ * (K2 ^ (KQ * n2) * (Q4 ^ (KQ * (n2 * n3)) *
        (KQ * (NSo * (KQ ^ nQ * (sQ * kQ))) * (NS2 * NS3 * (NR * (Q4 ^ 2 * 1))))))))) := by
  intro opS Com1 Pf1 Cmi Pfi m roots N C Pg Wt Mm NR0 pcsZ psimZ NR tabs tv pb ptm M q0 qZ Ss ks cols tqZ qdZ SsT SsC mk1 mk2 main1 main2 main3 vS sop1 sop2 sop3 ov1 ov2 ov3 rvF svF ozF op3 sd3 sm smR m1 m2 m3 rvo s1 s2 s3 svo sm4 sm4R r1 r2 r3 Mq
  have fo := (comp_fs_open4T off hR hrl hr hA hlen hLm hK hNW htM htC htP htS SM SC S9 SP SS qv wm wc ww wp wsg hlwm hlwc hlww hlwp hlwsg hK2 hK4 φ hφ hSM hSC hS9 hSP hSS hszM hszC hsz9 hszP hszS αd hB4 fri hncw NR2 Rb Ro Cmi Pfi (comI_hides hKQ pos hpos) (fun c4 T1 T2 T3 T4 _ => pfI_hides hKQ pos hpos (opS c4) g (nxtT T1 T2 T3 T4)) (fun _ _ => Nat.mod_lt _ hKQ) d1 Com2 Pf2T hc2 hp2 hr2 d2 Com3 Pf3T hc3 hp3 hr3 d3 E)
  exact Nat.le_trans (rom4_transferT (K3 := Q4) (m := 2) (NR := NR) (NSh := NSh) (NSo := NSo) (s := sQ) (k := kQ) (n := nQ)
    (NS2 := NS2) (NS3 := NS3) (K2 := K2) (K4 := K4) (N4 := N4) (n2 := n2) (n3 := n3) hKQ φ rvF ozF pos hpos g hs nxtT opS ov1 main1
    Com2 Pf2T ov2 main2 Com3 Pf3T ov3 main3 E) (Nat.add_le_add_right fo _)

end
end Circuit
