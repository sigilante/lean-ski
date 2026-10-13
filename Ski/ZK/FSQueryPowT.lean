import Ski.ZK.FSQueryAbsT

/-!
# `n` statements of each circuit, the openings reading the tables

`FSQueryAbs`'s `n`-statement theorems with each statement's openings
`Pf? c4 T1 T2 T3 T4 M` reading the four Fiat–Shamir tables and the third
message `M`: a statement's data
is a `FS4DT` (`sudFS4T`, `witFS4T`, `compFS4T`), its bound a `ZKBT`
(`sud_fs4T`, `wit_fs4T`, `comp_fs4T`, over `*_fs_open4_absT`), and `n` of
them compose by `fs4_powDT` (`sud_fs_open4_powDT`, `wit_fs_open4_powDT`,
`comp_fs_open4_powDT`).  Each statement's output's table reads are flagged
by `hqr ix`; `hout` and `hpq` stay hypotheses on the openings.  A read of
the first three tables at a point whose low digit mod `n1` is the reader's
first commitment meets them (`read2_hout` shows `hout` for one read of the
second table); a read of the fourth table must sit at `φ m w` with
`m % n1` the reader's first commitment, since `hφs` constrains `φ`'s input,
not its output's digit.  `FSMultiOpen` discharges both for openings that
read only at the digit `M % n1`.  One direction; `FSMultiT`'s limits hold.
-/

set_option autoImplicit false

namespace Circuit
open ZKF
section
open B Air Stmt Mach Sudoku SudokuText Compose CompM Wit

set_option maxRecDepth 100000 in
/-- One Sudoku statement's four-round data with the openings reading the tables (`sud_fs_open4_absT`'s), its output's table reads flagged by `hqr`. -/
def sudFS4T {V Wv P1 P2 P3 : Type} (off : EF → String → EF) (puzzle : List Nat) (A : List Cell) (k : Nat) (row : Nat → Air.Row) (tP : Nat) (S16 : Nat → List F) (S10 : Nat → List F) (SP : Nat → List F) (qv : EF → EF → List EF → F → List F → List F → List EF) (wm : Nat → List (EF → EF → List F)) (wc : Nat → List (EF → EF → List F)) (ww : Nat → List (EF → EF → List F)) (wp : Nat → List (EF → EF → List F)) (K2 : Nat) (K4 : Nat) (φ : Nat → Option (List (List (List EF)) × List (List (List (List EF))) × List (List (List EF))) → Nat) (N4 : Nat) (ncw : Nat) (αd : Nat → EF) (B4 : Nat) (fri : Nat → EF → EF → List (EF → EF) → V) (NR2 : Nat) (Rb : Nat → EF → EF → Nat → List (EF → EF)) (Ro : Nat → EF → EF → Nat → Wv) (NS1 : Nat) (NS2 : Nat) (NS3 : Nat) (n1 : Nat) (n2 : Nat) (n3 : Nat) (Com1 : List (List (List F)) → Nat → Nat) (Pf1 : Nat → Nat → Nat → Nat → Nat → Nat → List (List (List F)) → Nat → P1) (Com2 : List (List (List F)) → Nat → Nat) (Pf2 : Nat → Nat → Nat → Nat → Nat → Nat → List (List (List F)) → Nat → P2) (Com3 : List (List (List (List F))) × List (List (List F)) → Nat → Nat) (Pf3 : Nat → Nat → Nat → Nat → Nat → Nat → List (List (List (List F))) × List (List (List F)) → Nat → P3) (hqr : Nat × Nat × Nat × Nat → Nat × Nat × Nat × Nat → Nat × Nat × Nat × (Nat → Tup) → Bool) : FS4DT (Option P1 × Option (P2 × P3) × TViewN (SudPV (V × Wv)) EF) :=
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
    let rvo := fun (T1 T2 T3 T4 c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      ((ov1 c4 (rvF c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)).map (fun _ => Pf1 c4 T1 T2 T3 T4 (m3 c1 c2 x) (main1 x.2.2.2 x.2.2.1) x.1),
       (ovPair (ov2 c4) (ov3 c4) (rvF c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)).map
         (fun _ => pfPair NS2 (Pf2 c4 T1 T2 T3 T4 (m3 c1 c2 x)) (Pf3 c4 T1 T2 T3 T4 (m3 c1 c2 x)) (main2 c1 x.2.2.2 x.2.2.1, main3 c1 c2 x.2.2.2 x.2.2.1) x.2.1),
       rvF c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)
    let s1 := fun (c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) => Com1 (sdF (Ss c4) mk1 (sop1 c4 c2 c3 x.2.2.1 x.2.2.2)) x.1
    let s2 := fun (c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      s1 c4 c1 c2 c3 x + n1 * Com2 (sdF (Ss c4) mk2 (sop2 c4 c2 c3 c1 x.2.2.1 x.2.2.2)) (x.2.1 % NS2)
    let s3 := fun (c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      s1 c4 c1 c2 c3 x + n1 * comPair NS2 n2 Com2 Com3
        (sdF (Ss c4) mk2 (sop2 c4 c2 c3 c1 x.2.2.1 x.2.2.2), sd3 c4 (sop3 c4 c2 c3 c1 x.2.2.1 x.2.2.2)) x.2.1
    let svo := fun (T1 T2 T3 T4 c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      (some (Pf1 c4 T1 T2 T3 T4 (s3 c4 c1 c2 c3 x) (sdF (Ss c4) mk1 (sop1 c4 c2 c3 x.2.2.1 x.2.2.2)) x.1),
       some (pfPair NS2 (Pf2 c4 T1 T2 T3 T4 (s3 c4 c1 c2 c3 x)) (Pf3 c4 T1 T2 T3 T4 (s3 c4 c1 c2 c3 x)) (sdF (Ss c4) mk2 (sop2 c4 c2 c3 c1 x.2.2.1 x.2.2.2), sd3 c4 (sop3 c4 c2 c3 c1 x.2.2.1 x.2.2.2)) x.2.1),
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
    fun H c4 c1 c2 c3 x => rvo H.1 H.2.1 H.2.2.1 H.2.2.2 c4 c1 c2 c3 x,
    hqr,
    fun c x => (s1 c.2.2.2 c.1 c.2.1 c.2.2.1 x, s2 c.2.2.2 c.1 c.2.1 c.2.2.1 x, s3 c.2.2.2 c.1 c.2.1 c.2.2.1 x,
      φ (s3 c.2.2.2 c.1 c.2.1 c.2.2.1 x) (ozF (svF c.2.2.2 c.2.1 c.2.2.1 (efOf (c.1 / Q4)) (efOf (c.1 % Q4)) x.2.2.1 x.2.2.2))),
    fun H c x => (s1 c.2.2.2 c.1 c.2.1 c.2.2.1 x, s2 c.2.2.2 c.1 c.2.1 c.2.2.1 x, s3 c.2.2.2 c.1 c.2.1 c.2.2.1 x,
      svo (rset (Q4 * Q4) (s1 c.2.2.2 c.1 c.2.1 c.2.2.1 x) H.1 c.1) (rset K2 (s2 c.2.2.2 c.1 c.2.1 c.2.2.1 x) H.2.1 c.2.1) (rset Q4 (s3 c.2.2.2 c.1 c.2.1 c.2.2.1 x) H.2.2.1 c.2.2.1) (rset K4 (φ (s3 c.2.2.2 c.1 c.2.1 c.2.2.1 x) (ozF (svF c.2.2.2 c.2.1 c.2.2.1 (efOf (c.1 / Q4)) (efOf (c.1 % Q4)) x.2.2.1 x.2.2.2))) H.2.2.2 c.2.2.2) c.2.2.2 c.1 c.2.1 c.2.2.1 x),
    K4 ^ N4 * (K4 * ((Q4 * Q4) ^ n1 * (K2 ^ (n1 * n2) * (Q4 ^ (n1 * (n2 * n3)) *
          (K2 * (Q4 * (NS1 * (NS2 * NS3 * (Q4 * (NR * (Q4 ^ 2 * M)) + Q4 * (Q4 * (Q4 ^ 2 * 0)))))) +
            (Q4 * (P * P) * (K2 * Q4) + Q4 * Q4 * (K2 * (P * P))) * (NS1 * (NS2 * NS3 * (NR * (Q4 ^ 2 * 1)))))))) +
            B4 * (Q4 * Q4 * (K2 * Q4) * sm4 (fun _ => 1)))⟩


set_option maxRecDepth 100000 in
/-- **`sud_fs_open4_absT` on its data** (`sudFS4T`). -/
theorem sud_fs4T {V Wv P1 P2 P3 : Type} (off : EF → String → EF) {puzzle : List Nat} (hc : CluesOK (cluesOf puzzle))
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
    (Com1 : List (List (List F)) → Nat → Nat) (Pf1 : Nat → Nat → Nat → Nat → Nat → Nat → List (List (List F)) → Nat → P1) (hc1 : ComHides NS1 Com1)
    (hp1 : ∀ c4 T1 T2 T3 T4 M, ComPfHides NS1 Com1 (Pf1 c4 T1 T2 T3 T4 M) (opF ((sudGroups tP (S16 c4) (S10 c4) (SP c4) EF.zero qv).map (·.base.S)) [0, 2, 4, 6]))
    (hr1 : ∀ d σ, Com1 d σ < n1) (d1 : List (List (List F)))
    (Com2 : List (List (List F)) → Nat → Nat) (Pf2 : Nat → Nat → Nat → Nat → Nat → Nat → List (List (List F)) → Nat → P2) (hc2 : ComHides NS2 Com2)
    (hp2 : ∀ c4 T1 T2 T3 T4 M, ComPfHides NS2 Com2 (Pf2 c4 T1 T2 T3 T4 M) (opF ((sudGroups tP (S16 c4) (S10 c4) (SP c4) EF.zero qv).map (·.base.S)) [1, 3, 5, 7]))
    (hr2 : ∀ d σ, Com2 d σ < n2) (d2 : List (List (List F)))
    (Com3 : List (List (List (List F))) × List (List (List F)) → Nat → Nat)
    (Pf3 : Nat → Nat → Nat → Nat → Nat → Nat → List (List (List (List F))) × List (List (List F)) → Nat → P3) (hc3 : ComHides NS3 Com3)
    (hp3 : ∀ c4 T1 T2 T3 T4 M, ComPfHides NS3 Com3 (Pf3 c4 T1 T2 T3 T4 M) (fun d => (opQ (sudSsT (S16 c4) (S10 c4) (SP c4)) d.1, opCw (sudSsC tP (S16 c4) (S10 c4) (SP c4)) d.2)))
    (hr3 : ∀ d σ, Com3 d σ < n3) (d3 : List (List (List (List F))) × List (List (List F))) (hqr : Nat × Nat × Nat × Nat → Nat × Nat × Nat × Nat → Nat × Nat × Nat × (Nat → Tup) → Bool) :
    ZKBT (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo (K4 ^ N4) (fun H4 => sumTo ((Q4 * Q4) ^ n1) (fun H1 =>
      sumTo (K2 ^ (n1 * n2)) (fun H2 => sumTo (Q4 ^ (n1 * (n2 * n3))) (fun H3 => f (H1, H2, H3, H4))))))
      (K4 * (Q4 * Q4 * (K2 * Q4))) ((sudFS4T off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 φ N4 ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Pf1 Com2 Pf2 Com3 Pf3 hqr).sm 2)
      (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo K4 (fun c4 => sumTo (Q4 * Q4) (fun c1 =>
        sumTo K2 (fun c2 => sumTo Q4 (fun c3 => f (c1, c2, c3, c4))))))
      (read4T (Q4 * Q4) K2 Q4 K4 (sudFS4T off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 φ N4 ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Pf1 Com2 Pf2 Com3 Pf3 hqr).m1 (sudFS4T off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 φ N4 ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Pf1 Com2 Pf2 Com3 Pf3 hqr).m2 (sudFS4T off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 φ N4 ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Pf1 Com2 Pf2 Com3 Pf3 hqr).m3 (sudFS4T off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 φ N4 ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Pf1 Com2 Pf2 Com3 Pf3 hqr).q (sudFS4T off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 φ N4 ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Pf1 Com2 Pf2 Com3 Pf3 hqr).out)
      (fun H c xx => prog4 (Q4 * Q4) K2 Q4 K4 H ((sudFS4T off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 φ N4 ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Pf1 Com2 Pf2 Com3 Pf3 hqr).pts c xx) c) (sudFS4T off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 φ N4 ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Pf1 Com2 Pf2 Com3 Pf3 hqr).sv (sudFS4T off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 φ N4 ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Pf1 Com2 Pf2 Com3 Pf3 hqr).ε :=
  sud_fs_open4_absT off hc hA hacc hlen hk htp S16 S10 SP qv wm wc ww wp hlwm hlwc hlww hlwp hK2 hK4 φ hφ hS16 hS10 hSP hsz16 hsz hszP αd hB4 fri hncw NR2 Rb Ro Com1 Pf1 hc1 hp1 hr1 d1 Com2 Pf2 hc2 hp2 hr2 d2 Com3 Pf3 hc3 hp3 hr3 d3


set_option maxRecDepth 100000 in
/-- **`n` Sudoku statements under one oracle, the openings reading the
    tables** (`fs4_powDT` over `sud_fs4T`): `sud_fs_open4_powD`'s hypotheses
    with each statement's openings `Pf? c4 T1 T2 T3 T4 M`, their output's table
    reads flagged by `hqr ix`, unchanged by an in-range programming they
    miss (`hout`), a hit carrying the reader's first commitment (`hpq`);
    as there, the query hashes keep the first commitment's digit (`hφs`) and
    each first commitment spreads (`hsp`). -/
theorem sud_fs_open4_powDT {V Wv P1 P2 P3 : Type}  (off : EF → String → EF) {puzzle : ∀ ix : Nat, List Nat} (hc : ∀ ix : Nat, CluesOK (cluesOf (puzzle ix))) {ρ : ∀ ix : Nat, Nat → Bool} {A : ∀ ix : Nat, List Cell} {k : ∀ ix : Nat, Nat} {row : ∀ ix : Nat, Nat → Air.Row} (hA : ∀ ix : Nat, AcceptsFrom (A ix) (stmtMachine (ρ ix) 729 (sudokuExpr (cluesOf (puzzle ix))) ACC REJ) (k ix) (row ix)) (hacc : ∀ ix : Nat, rd (A ix) ((row ix) ((k ix) - 1)).ctr ((row ix) ((k ix) - 1)).hd = some (.atom ACC)) (hlen : ∀ ix : Nat, (A ix).length = 2 ^ 16) (hk : ∀ ix : Nat, (k ix) ≤ 2 ^ 16) {tP : ∀ ix : Nat, Nat} (htp : ∀ ix : Nat, (tP ix) = progTp (stmtMachine (fun _ => false) 729 (sudokuExpr (cluesOf (puzzle ix))) ACC REJ).heap) (S16 S10 SP : ∀ ix : Nat, Nat → List F) (qv : ∀ ix : Nat, EF → EF → List EF → F → List F → List F → List EF) (wm wc ww wp : ∀ ix : Nat, Nat → List (EF → EF → List F)) {Lwm Lwc Lww Lwp : ∀ ix : Nat, Nat} (hlwm : ∀ ix : Nat, ∀ c, ((wm ix) c).length = (Lwm ix)) (hlwc : ∀ ix : Nat, ∀ c, ((wc ix) c).length = (Lwc ix)) (hlww : ∀ ix : Nat, ∀ c, ((ww ix) c).length = (Lww ix)) (hlwp : ∀ ix : Nat, ∀ c, ((wp ix) c).length = (Lwp ix)) {K2 K4 : Nat} (hK2 : 0 < K2) (hK4 : 0 < K4) (φ : ∀ ix : Nat, Nat → Option (List (List (List EF)) × List (List (List (List EF))) × List (List (List EF))) → Nat) {N4 : Nat} (hφ : ∀ ix : Nat, ∀ m w, (φ ix) m w < N4) (hS16 : ∀ ix : Nat, ∀ c4, ∀ x ∈ (S16 ix) c4, x ∉ cosetL 1 (bbGen 16) (2 ^ 16)) (hS10 : ∀ ix : Nat, ∀ c4, ∀ x ∈ (S10 ix) c4, x ∉ cosetL 1 (bbGen 10) (2 ^ 10)) (hSP : ∀ ix : Nat, ∀ c4, ∀ x ∈ (SP ix) c4, x ∉ cosetL 1 (bbGen ((tP ix) + 1)) (2 ^ ((tP ix) + 1))) (hsz16 : ∀ ix : Nat, ∀ c4, 2 * ((S16 ix) c4).length + 8 ≤ 2 ^ 16) (hsz : ∀ ix : Nat, ∀ c4, 2 * ((S10 ix) c4).length + 8 ≤ 2 ^ 10) (hszP : ∀ ix : Nat, ∀ c4, 2 * ((SP ix) c4).length + 8 ≤ 2 ^ ((tP ix) + 1)) {ncw : ∀ ix : Nat, Nat} (αd : ∀ ix : Nat, Nat → EF) {B4 : ∀ ix : Nat, Nat} (hB4 : ∀ ix : Nat, sumTo K4 (fun c4 => indB (!genB ((αd ix) c4))) ≤ (B4 ix)) (fri : ∀ ix : Nat, Nat → EF → EF → List (EF → EF) → V) (hncw : ∀ ix : Nat, 4 ≤ (ncw ix)) (NR2 : ∀ ix : Nat, Nat) (Rb : ∀ ix : Nat, Nat → EF → EF → Nat → List (EF → EF)) (Ro : ∀ ix : Nat, Nat → EF → EF → Nat → Wv) {n1 n2 n3 : Nat} {NS1 NS2 NS3 : ∀ ix : Nat, Nat} (Com1 : ∀ ix : Nat, List (List (List F)) → Nat → Nat) (Pf1 : ∀ ix : Nat, Nat → Nat → Nat → Nat → Nat → Nat → List (List (List F)) → Nat → P1) (hc1 : ∀ ix : Nat, ComHides (NS1 ix) (Com1 ix)) (hp1 : ∀ ix : Nat, ∀ c4 T1 T2 T3 T4 M, ComPfHides (NS1 ix) (Com1 ix) ((Pf1 ix) c4 T1 T2 T3 T4 M) (opF ((sudGroups (tP ix) ((S16 ix) c4) ((S10 ix) c4) ((SP ix) c4) EF.zero (qv ix)).map (·.base.S)) [0, 2, 4, 6])) (hr1 : ∀ ix : Nat, ∀ d σ, (Com1 ix) d σ < n1) (d1 : ∀ ix : Nat, List (List (List F))) (Com2 : ∀ ix : Nat, List (List (List F)) → Nat → Nat) (Pf2 : ∀ ix : Nat, Nat → Nat → Nat → Nat → Nat → Nat → List (List (List F)) → Nat → P2) (hc2 : ∀ ix : Nat, ComHides (NS2 ix) (Com2 ix)) (hp2 : ∀ ix : Nat, ∀ c4 T1 T2 T3 T4 M, ComPfHides (NS2 ix) (Com2 ix) ((Pf2 ix) c4 T1 T2 T3 T4 M) (opF ((sudGroups (tP ix) ((S16 ix) c4) ((S10 ix) c4) ((SP ix) c4) EF.zero (qv ix)).map (·.base.S)) [1, 3, 5, 7])) (hr2 : ∀ ix : Nat, ∀ d σ, (Com2 ix) d σ < n2) (d2 : ∀ ix : Nat, List (List (List F))) (Com3 : ∀ ix : Nat, List (List (List (List F))) × List (List (List F)) → Nat → Nat) (Pf3 : ∀ ix : Nat, Nat → Nat → Nat → Nat → Nat → Nat → List (List (List (List F))) × List (List (List F)) → Nat → P3) (hc3 : ∀ ix : Nat, ComHides (NS3 ix) (Com3 ix)) (hp3 : ∀ ix : Nat, ∀ c4 T1 T2 T3 T4 M, ComPfHides (NS3 ix) (Com3 ix) ((Pf3 ix) c4 T1 T2 T3 T4 M) (fun d => (opQ (sudSsT ((S16 ix) c4) ((S10 ix) c4) ((SP ix) c4)) d.1, opCw (sudSsC (tP ix) ((S16 ix) c4) ((S10 ix) c4) ((SP ix) c4)) d.2))) (hr3 : ∀ ix : Nat, ∀ d σ, (Com3 ix) d σ < n3) (d3 : ∀ ix : Nat, List (List (List (List F))) × List (List (List F))) (hqr : ∀ ix : Nat, Nat × Nat × Nat × Nat → Nat × Nat × Nat × Nat → Nat × Nat × Nat × (Nat → Tup) → Bool)
    (hout : ∀ ix H p a c4 c1 c2 c3 xq, a.1 < Q4 * Q4 ∧ a.2.1 < K2 ∧ a.2.2.1 < Q4 ∧ a.2.2.2 < K4 → hqr ix H p xq = false →
      (sudFS4T off (puzzle ix) (A ix) (k ix) (row ix) (tP ix) (S16 ix) (S10 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NS1 ix) (NS2 ix) (NS3 ix) n1 n2 n3 (Com1 ix) (Pf1 ix) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix) (hqr ix)).out (prog4 (Q4 * Q4) K2 Q4 K4 H p a) c4 c1 c2 c3 xq = (sudFS4T off (puzzle ix) (A ix) (k ix) (row ix) (tP ix) (S16 ix) (S10 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NS1 ix) (NS2 ix) (NS3 ix) n1 n2 n3 (Com1 ix) (Pf1 ix) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix) (hqr ix)).out H c4 c1 c2 c3 xq)
    (hpq : ∀ i j c xa H xq, hqr i H ((sudFS4T off (puzzle j) (A j) (k j) (row j) (tP j) (S16 j) (S10 j) (SP j) (qv j) (wm j) (wc j) (ww j) (wp j) K2 K4 (φ j) N4 (ncw j) (αd j) (B4 j) (fri j) (NR2 j) (Rb j) (Ro j) (NS1 j) (NS2 j) (NS3 j) n1 n2 n3 (Com1 j) (Pf1 j) (Com2 j) (Pf2 j) (Com3 j) (Pf3 j) (hqr j)).pts c xa) xq = true → (sudFS4T off (puzzle i) (A i) (k i) (row i) (tP i) (S16 i) (S10 i) (SP i) (qv i) (wm i) (wc i) (ww i) (wp i) K2 K4 (φ i) N4 (ncw i) (αd i) (B4 i) (fri i) (NR2 i) (Rb i) (Ro i) (NS1 i) (NS2 i) (NS3 i) n1 n2 n3 (Com1 i) (Pf1 i) (Com2 i) (Pf2 i) (Com3 i) (Pf3 i) (hqr i)).m1 xq = ((sudFS4T off (puzzle j) (A j) (k j) (row j) (tP j) (S16 j) (S10 j) (SP j) (qv j) (wm j) (wc j) (ww j) (wp j) K2 K4 (φ j) N4 (ncw j) (αd j) (B4 j) (fri j) (NR2 j) (Rb j) (Ro j) (NS1 j) (NS2 j) (NS3 j) n1 n2 n3 (Com1 j) (Pf1 j) (Com2 j) (Pf2 j) (Com3 j) (Pf3 j) (hqr j)).pts c xa).1)
    (hφs : ∀ i j m w m' w', φ i m w = φ j m' w' → m % n1 = m' % n1) (δs : Nat → Nat)
    (hsp : ∀ ix d v, sumTo (NS1 ix) (fun σ => indB (decide (Com1 ix d σ = v))) ≤ δs ix) :
    ∀ n, ZKBT (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo (K4 ^ N4) (fun H4 => sumTo ((Q4 * Q4) ^ n1) (fun H1 =>
        sumTo (K2 ^ (n1 * n2)) (fun H2 => sumTo (Q4 ^ (n1 * (n2 * n3))) (fun H3 => f (H1, H2, H3, H4))))))
      (KPowD (fun _ => K4 * (Q4 * Q4 * (K2 * Q4))) n)
      (smPowD (X := fun _ => Nat × Nat × Nat × (Nat → Tup)) (fun ix => (sudFS4T off (puzzle ix) (A ix) (k ix) (row ix) (tP ix) (S16 ix) (S10 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NS1 ix) (NS2 ix) (NS3 ix) n1 n2 n3 (Com1 ix) (Pf1 ix) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix) (hqr ix)).sm 2) n)
      (scPowD (C := fun _ => Nat × Nat × Nat × Nat) (fun _ => fun (f : Nat × Nat × Nat × Nat → Nat) =>
        sumTo K4 (fun c4 => sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo Q4 (fun c3 => f (c1, c2, c3, c4)))))) n)
      (rvPowD (fun ix => read4T (Q4 * Q4) K2 Q4 K4 (sudFS4T off (puzzle ix) (A ix) (k ix) (row ix) (tP ix) (S16 ix) (S10 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NS1 ix) (NS2 ix) (NS3 ix) n1 n2 n3 (Com1 ix) (Pf1 ix) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix) (hqr ix)).m1 (sudFS4T off (puzzle ix) (A ix) (k ix) (row ix) (tP ix) (S16 ix) (S10 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NS1 ix) (NS2 ix) (NS3 ix) n1 n2 n3 (Com1 ix) (Pf1 ix) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix) (hqr ix)).m2 (sudFS4T off (puzzle ix) (A ix) (k ix) (row ix) (tP ix) (S16 ix) (S10 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NS1 ix) (NS2 ix) (NS3 ix) n1 n2 n3 (Com1 ix) (Pf1 ix) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix) (hqr ix)).m3 (sudFS4T off (puzzle ix) (A ix) (k ix) (row ix) (tP ix) (S16 ix) (S10 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NS1 ix) (NS2 ix) (NS3 ix) n1 n2 n3 (Com1 ix) (Pf1 ix) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix) (hqr ix)).q (sudFS4T off (puzzle ix) (A ix) (k ix) (row ix) (tP ix) (S16 ix) (S10 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NS1 ix) (NS2 ix) (NS3 ix) n1 n2 n3 (Com1 ix) (Pf1 ix) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix) (hqr ix)).out) n)
      (pgPowD (fun ix H c xx => prog4 (Q4 * Q4) K2 Q4 K4 H ((sudFS4T off (puzzle ix) (A ix) (k ix) (row ix) (tP ix) (S16 ix) (S10 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NS1 ix) (NS2 ix) (NS3 ix) n1 n2 n3 (Com1 ix) (Pf1 ix) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix) (hqr ix)).pts c xx) c) n) (svPowDT (fun ix H c xx => prog4 (Q4 * Q4) K2 Q4 K4 H ((sudFS4T off (puzzle ix) (A ix) (k ix) (row ix) (tP ix) (S16 ix) (S10 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NS1 ix) (NS2 ix) (NS3 ix) n1 n2 n3 (Com1 ix) (Pf1 ix) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix) (hqr ix)).pts c xx) c) (fun ix => (sudFS4T off (puzzle ix) (A ix) (k ix) (row ix) (tP ix) (S16 ix) (S10 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NS1 ix) (NS2 ix) (NS3 ix) n1 n2 n3 (Com1 ix) (Pf1 ix) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix) (hqr ix)).sv) n)
      (errPowD (fun _ => K4 * (Q4 * Q4 * (K2 * Q4))) (fun ix => (sudFS4T off (puzzle ix) (A ix) (k ix) (row ix) (tP ix) (S16 ix) (S10 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NS1 ix) (NS2 ix) (NS3 ix) n1 n2 n3 (Com1 ix) (Pf1 ix) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix) (hqr ix)).sm 2)
        (fun _ => fun (f : Nat × Nat × Nat × Nat → Nat) =>
          sumTo K4 (fun c4 => sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo Q4 (fun c3 => f (c1, c2, c3, c4))))))
        (fun ix => (sudFS4T off (puzzle ix) (A ix) (k ix) (row ix) (tP ix) (S16 ix) (S10 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NS1 ix) (NS2 ix) (NS3 ix) n1 n2 n3 (Com1 ix) (Pf1 ix) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix) (hqr ix)).ε)
        (fun j => sumTo K4 (fun c4 => sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo Q4 (fun c3 =>
          (sudFS4T off (puzzle j) (A j) (k j) (row j) (tP j) (S16 j) (S10 j) (SP j) (qv j) (wm j) (wc j) (ww j) (wp j) K2 K4 (φ j) N4 (ncw j) (αd j) (B4 j) (fri j) (NR2 j) (Rb j) (Ro j) (NS1 j) (NS2 j) (NS3 j) n1 n2 n3 (Com1 j) (Pf1 j) (Com2 j) (Pf2 j) (Com3 j) (Pf3 j) (hqr j)).sm 2 (fun _ => sumTo (K4 ^ N4) (fun H4 => sumTo ((Q4 * Q4) ^ n1) (fun H1 =>
            sumTo (K2 ^ (n1 * n2)) (fun H2 => sumTo (Q4 ^ (n1 * (n2 * n3))) (fun H3 =>
              hitBD (fun ix => (sudFS4T off (puzzle ix) (A ix) (k ix) (row ix) (tP ix) (S16 ix) (S10 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NS1 ix) (NS2 ix) (NS3 ix) n1 n2 n3 (Com1 ix) (Pf1 ix) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix) (hqr ix)).sm 2) (fun ix => (sudFS4T off (puzzle ix) (A ix) (k ix) (row ix) (tP ix) (S16 ix) (S10 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NS1 ix) (NS2 ix) (NS3 ix) n1 n2 n3 (Com1 ix) (Pf1 ix) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix) (hqr ix)).NS * ((sudFS4T off (puzzle ix) (A ix) (k ix) (row ix) (tP ix) (S16 ix) (S10 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NS1 ix) (NS2 ix) (NS3 ix) n1 n2 n3 (Com1 ix) (Pf1 ix) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix) (hqr ix)).NR * (Q4 ^ 2 * δs ix))) j)))))))))) n) := by
  intro n
  exact fs4_powDT (n1 := n1) hK2 hK4 (fun ix => (sudFS4T off (puzzle ix) (A ix) (k ix) (row ix) (tP ix) (S16 ix) (S10 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NS1 ix) (NS2 ix) (NS3 ix) n1 n2 n3 (Com1 ix) (Pf1 ix) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix) (hqr ix)))
    (fun ix c1 x => (Nat.add_mul_mod_self_left _ _ _).trans (Nat.mod_eq_of_lt (hr1 ix _ _)))
    (fun ix c1 c2 x => (Nat.add_mul_mod_self_left _ _ _).trans (Nat.mod_eq_of_lt (hr1 ix _ _)))
    (fun ix c x => (Nat.add_mul_mod_self_left _ _ _).trans (Nat.mod_eq_of_lt (hr1 ix _ _)))
    (fun ix c x => (Nat.add_mul_mod_self_left _ _ _).trans (Nat.mod_eq_of_lt (hr1 ix _ _)))
    (fun i j c1 c2 c3 x c xa h => hφs i j _ _ _ _ h) hout hpq
    (fun ix => (sudFS4T off (puzzle ix) (A ix) (k ix) (row ix) (tP ix) (S16 ix) (S10 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NS1 ix) (NS2 ix) (NS3 ix) n1 n2 n3 (Com1 ix) (Pf1 ix) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix) (hqr ix)).NS * ((sudFS4T off (puzzle ix) (A ix) (k ix) (row ix) (tP ix) (S16 ix) (S10 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NS1 ix) (NS2 ix) (NS3 ix) n1 n2 n3 (Com1 ix) (Pf1 ix) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix) (hqr ix)).NR * (Q4 ^ 2 * δs ix)))
    (fun ix v => spread_sum (Com1 ix) (sudMain1 V Wv off (puzzle ix) (A ix) (k ix) (row ix) (tP ix) (S16 ix) (S10 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (ncw ix) (αd ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix)) (hsp ix) v)
    (fun ix => sud_fs4T off (hc ix) (hA ix) (hacc ix) (hlen ix) (hk ix) (htp ix) (S16 ix) (S10 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (hlwm ix) (hlwc ix) (hlww ix) (hlwp ix) hK2 hK4 (φ ix) (hφ ix) (hS16 ix) (hS10 ix) (hSP ix) (hsz16 ix) (hsz ix) (hszP ix) (αd ix) (hB4 ix) (fri ix) (hncw ix) (NR2 ix) (Rb ix) (Ro ix) (Com1 ix) (Pf1 ix) (hc1 ix) (hp1 ix) (hr1 ix) (d1 ix) (Com2 ix) (Pf2 ix) (hc2 ix) (hp2 ix) (hr2 ix) (d2 ix) (Com3 ix) (Pf3 ix) (hc3 ix) (hp3 ix) (hr3 ix) (d3 ix) (hqr ix)) n


set_option maxRecDepth 100000 in
/-- One hidden-term statement's four-round data with the openings reading the tables (`wit_fs_open4_absT`'s), its output's table reads flagged by `hqr`. -/
def witFS4T {V Wv P1 P2 P3 : Type} (off : EF → String → EF) (Vt : Term) (x : Term) (W : Nat) (A : List Cell) (k : Nat) (row : Nat → Air.Row) (tP : Nat) (S10 : Nat → List F) (S9 : Nat → List F) (SP : Nat → List F) (qv : EF → EF → List EF → F → List F → List F → List EF) (wm : Nat → List (EF → EF → List F)) (wc : Nat → List (EF → EF → List F)) (ww : Nat → List (EF → EF → List F)) (wp : Nat → List (EF → EF → List F)) (K2 : Nat) (K4 : Nat) (φ : Nat → Option (List (List (List EF)) × List (List (List (List EF))) × List (List (List EF))) → Nat) (N4 : Nat) (ncw : Nat) (αd : Nat → EF) (B4 : Nat) (fri : Nat → EF → EF → List (EF → EF) → V) (NR2 : Nat) (Rb : Nat → EF → EF → Nat → List (EF → EF)) (Ro : Nat → EF → EF → Nat → Wv) (NS1 : Nat) (NS2 : Nat) (NS3 : Nat) (n1 : Nat) (n2 : Nat) (n3 : Nat) (Com1 : List (List (List F)) → Nat → Nat) (Pf1 : Nat → Nat → Nat → Nat → Nat → Nat → List (List (List F)) → Nat → P1) (Com2 : List (List (List F)) → Nat → Nat) (Pf2 : Nat → Nat → Nat → Nat → Nat → Nat → List (List (List F)) → Nat → P2) (Com3 : List (List (List (List F))) × List (List (List F)) → Nat → Nat) (Pf3 : Nat → Nat → Nat → Nat → Nat → Nat → List (List (List (List F))) × List (List (List F)) → Nat → P3) (hqr : Nat × Nat × Nat × Nat → Nat × Nat × Nat × Nat → Nat × Nat × Nat × (Nat → Tup) → Bool) : FS4DT (Option P1 × Option (P2 × P3) × TViewN (PcsPV (V × Wv)) EF) :=
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
    let rvo := fun (T1 T2 T3 T4 c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      ((ov1 c4 (rvF c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)).map (fun _ => Pf1 c4 T1 T2 T3 T4 (m3 c1 c2 x) (main1 x.2.2.2 x.2.2.1) x.1),
       (ovPair (ov2 c4) (ov3 c4) (rvF c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)).map
         (fun _ => pfPair NS2 (Pf2 c4 T1 T2 T3 T4 (m3 c1 c2 x)) (Pf3 c4 T1 T2 T3 T4 (m3 c1 c2 x)) (main2 c1 x.2.2.2 x.2.2.1, main3 c1 c2 x.2.2.2 x.2.2.1) x.2.1),
       rvF c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)
    let s1 := fun (c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) => Com1 (sdF (Ss c4) mk1 (sop1 c4 c2 c3 x.2.2.1 x.2.2.2)) x.1
    let s2 := fun (c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      s1 c4 c1 c2 c3 x + n1 * Com2 (sdF (Ss c4) mk2 (sop2 c4 c2 c3 c1 x.2.2.1 x.2.2.2)) (x.2.1 % NS2)
    let s3 := fun (c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      s1 c4 c1 c2 c3 x + n1 * comPair NS2 n2 Com2 Com3
        (sdF (Ss c4) mk2 (sop2 c4 c2 c3 c1 x.2.2.1 x.2.2.2), sd3 c4 (sop3 c4 c2 c3 c1 x.2.2.1 x.2.2.2)) x.2.1
    let svo := fun (T1 T2 T3 T4 c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      (some (Pf1 c4 T1 T2 T3 T4 (s3 c4 c1 c2 c3 x) (sdF (Ss c4) mk1 (sop1 c4 c2 c3 x.2.2.1 x.2.2.2)) x.1),
       some (pfPair NS2 (Pf2 c4 T1 T2 T3 T4 (s3 c4 c1 c2 c3 x)) (Pf3 c4 T1 T2 T3 T4 (s3 c4 c1 c2 c3 x)) (sdF (Ss c4) mk2 (sop2 c4 c2 c3 c1 x.2.2.1 x.2.2.2), sd3 c4 (sop3 c4 c2 c3 c1 x.2.2.1 x.2.2.2)) x.2.1),
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
    fun H c4 c1 c2 c3 x => rvo H.1 H.2.1 H.2.2.1 H.2.2.2 c4 c1 c2 c3 x,
    hqr,
    fun c x => (s1 c.2.2.2 c.1 c.2.1 c.2.2.1 x, s2 c.2.2.2 c.1 c.2.1 c.2.2.1 x, s3 c.2.2.2 c.1 c.2.1 c.2.2.1 x,
      φ (s3 c.2.2.2 c.1 c.2.1 c.2.2.1 x) (ozF (svF c.2.2.2 c.2.1 c.2.2.1 (efOf (c.1 / Q4)) (efOf (c.1 % Q4)) x.2.2.1 x.2.2.2))),
    fun H c x => (s1 c.2.2.2 c.1 c.2.1 c.2.2.1 x, s2 c.2.2.2 c.1 c.2.1 c.2.2.1 x, s3 c.2.2.2 c.1 c.2.1 c.2.2.1 x,
      svo (rset (Q4 * Q4) (s1 c.2.2.2 c.1 c.2.1 c.2.2.1 x) H.1 c.1) (rset K2 (s2 c.2.2.2 c.1 c.2.1 c.2.2.1 x) H.2.1 c.2.1) (rset Q4 (s3 c.2.2.2 c.1 c.2.1 c.2.2.1 x) H.2.2.1 c.2.2.1) (rset K4 (φ (s3 c.2.2.2 c.1 c.2.1 c.2.2.1 x) (ozF (svF c.2.2.2 c.2.1 c.2.2.1 (efOf (c.1 / Q4)) (efOf (c.1 % Q4)) x.2.2.1 x.2.2.2))) H.2.2.2 c.2.2.2) c.2.2.2 c.1 c.2.1 c.2.2.1 x),
    K4 ^ N4 * (K4 * ((Q4 * Q4) ^ n1 * (K2 ^ (n1 * n2) * (Q4 ^ (n1 * (n2 * n3)) *
          (K2 * (Q4 * (NS1 * (NS2 * NS3 * (Q4 * (NR * (Q4 ^ 2 * M)) + Q4 * (Q4 * (Q4 ^ 2 * 0)))))) +
            (Q4 * (P * P) * (K2 * Q4) + Q4 * Q4 * (K2 * (P * P))) * (NS1 * (NS2 * NS3 * (NR * (Q4 ^ 2 * 1)))))))) +
            B4 * (Q4 * Q4 * (K2 * Q4) * sm4 (fun _ => 1)))⟩


set_option maxRecDepth 100000 in
/-- **`wit_fs_open4_absT` on its data** (`witFS4T`). -/
theorem wit_fs4T {V Wv P1 P2 P3 : Type} (off : EF → String → EF) {Vt x : Term} {W : Nat} {ws : List Cell} (hwf : WF ws)
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
    (Com1 : List (List (List F)) → Nat → Nat) (Pf1 : Nat → Nat → Nat → Nat → Nat → Nat → List (List (List F)) → Nat → P1) (hc1 : ComHides NS1 Com1)
    (hp1 : ∀ c4 T1 T2 T3 T4 M, ComPfHides NS1 Com1 (Pf1 c4 T1 T2 T3 T4 M) (opF ((wGroups tP (S10 c4) (S9 c4) (SP c4) EF.zero qv).map (·.base.S)) [0, 2, 4, 6]))
    (hr1 : ∀ d σ, Com1 d σ < n1) (d1 : List (List (List F)))
    (Com2 : List (List (List F)) → Nat → Nat) (Pf2 : Nat → Nat → Nat → Nat → Nat → Nat → List (List (List F)) → Nat → P2) (hc2 : ComHides NS2 Com2)
    (hp2 : ∀ c4 T1 T2 T3 T4 M, ComPfHides NS2 Com2 (Pf2 c4 T1 T2 T3 T4 M) (opF ((wGroups tP (S10 c4) (S9 c4) (SP c4) EF.zero qv).map (·.base.S)) [1, 3, 5, 7]))
    (hr2 : ∀ d σ, Com2 d σ < n2) (d2 : List (List (List F)))
    (Com3 : List (List (List (List F))) × List (List (List F)) → Nat → Nat)
    (Pf3 : Nat → Nat → Nat → Nat → Nat → Nat → List (List (List (List F))) × List (List (List F)) → Nat → P3) (hc3 : ComHides NS3 Com3)
    (hp3 : ∀ c4 T1 T2 T3 T4 M, ComPfHides NS3 Com3 (Pf3 c4 T1 T2 T3 T4 M) (fun d => (opQ (wSsT (S10 c4) (S9 c4) (SP c4)) d.1, opCw (wSsC tP (S10 c4) (S9 c4) (SP c4)) d.2)))
    (hr3 : ∀ d σ, Com3 d σ < n3) (d3 : List (List (List (List F))) × List (List (List F))) (hqr : Nat × Nat × Nat × Nat → Nat × Nat × Nat × Nat → Nat × Nat × Nat × (Nat → Tup) → Bool) :
    ZKBT (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo (K4 ^ N4) (fun H4 => sumTo ((Q4 * Q4) ^ n1) (fun H1 =>
      sumTo (K2 ^ (n1 * n2)) (fun H2 => sumTo (Q4 ^ (n1 * (n2 * n3))) (fun H3 => f (H1, H2, H3, H4))))))
      (K4 * (Q4 * Q4 * (K2 * Q4))) ((witFS4T off Vt x W A k row tP S10 S9 SP qv wm wc ww wp K2 K4 φ N4 ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Pf1 Com2 Pf2 Com3 Pf3 hqr).sm 2)
      (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo K4 (fun c4 => sumTo (Q4 * Q4) (fun c1 =>
        sumTo K2 (fun c2 => sumTo Q4 (fun c3 => f (c1, c2, c3, c4))))))
      (read4T (Q4 * Q4) K2 Q4 K4 (witFS4T off Vt x W A k row tP S10 S9 SP qv wm wc ww wp K2 K4 φ N4 ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Pf1 Com2 Pf2 Com3 Pf3 hqr).m1 (witFS4T off Vt x W A k row tP S10 S9 SP qv wm wc ww wp K2 K4 φ N4 ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Pf1 Com2 Pf2 Com3 Pf3 hqr).m2 (witFS4T off Vt x W A k row tP S10 S9 SP qv wm wc ww wp K2 K4 φ N4 ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Pf1 Com2 Pf2 Com3 Pf3 hqr).m3 (witFS4T off Vt x W A k row tP S10 S9 SP qv wm wc ww wp K2 K4 φ N4 ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Pf1 Com2 Pf2 Com3 Pf3 hqr).q (witFS4T off Vt x W A k row tP S10 S9 SP qv wm wc ww wp K2 K4 φ N4 ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Pf1 Com2 Pf2 Com3 Pf3 hqr).out)
      (fun H c xx => prog4 (Q4 * Q4) K2 Q4 K4 H ((witFS4T off Vt x W A k row tP S10 S9 SP qv wm wc ww wp K2 K4 φ N4 ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Pf1 Com2 Pf2 Com3 Pf3 hqr).pts c xx) c) (witFS4T off Vt x W A k row tP S10 S9 SP qv wm wc ww wp K2 K4 φ N4 ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Pf1 Com2 Pf2 Com3 Pf3 hqr).sv (witFS4T off Vt x W A k row tP S10 S9 SP qv wm wc ww wp K2 K4 φ N4 ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Pf1 Com2 Pf2 Com3 Pf3 hqr).ε :=
  wit_fs_open4_absT off hwf hwl hW8 hA hK hlen hk htp S10 S9 SP qv wm wc ww wp hlwm hlwc hlww hlwp hK2 hK4 φ hφ hS10 hS9 hSP hsz10 hsz9 hszP αd hB4 fri hncw NR2 Rb Ro Com1 Pf1 hc1 hp1 hr1 d1 Com2 Pf2 hc2 hp2 hr2 d2 Com3 Pf3 hc3 hp3 hr3 d3


set_option maxRecDepth 100000 in
/-- **`n` hidden-term statements under one oracle, the openings reading the
    tables** (`fs4_powDT` over `wit_fs4T`): `wit_fs_open4_powD`'s hypotheses
    with each statement's openings `Pf? c4 T1 T2 T3 T4 M`, their output's table
    reads flagged by `hqr ix`, unchanged by an in-range programming they
    miss (`hout`), a hit carrying the reader's first commitment (`hpq`);
    as there, the query hashes keep the first commitment's digit (`hφs`) and
    each first commitment spreads (`hsp`). -/
theorem wit_fs_open4_powDT {V Wv P1 P2 P3 : Type}  (off : EF → String → EF) {Vt x : ∀ ix : Nat, Term} {W : ∀ ix : Nat, Nat} {ws : ∀ ix : Nat, List Cell} (hwf : ∀ ix : Nat, WF (ws ix)) (hwl : ∀ ix : Nat, (ws ix).length = (W ix)) (hW8 : ∀ ix : Nat, (W ix) ≤ 2 ^ 8) {A : ∀ ix : Nat, List Cell} {k : ∀ ix : Nat, Nat} {row : ∀ ix : Nat, Nat → Air.Row} (hA : ∀ ix : Nat, AcceptsFrom (A ix) (wMachine (ws ix) ((Vt ix) ⬝ (x ix))) (k ix) (row ix)) (hK : ∀ ix : Nat, rd (A ix) ((row ix) ((k ix) - 1)).ctr ((row ix) ((k ix) - 1)).hd = some .K ∧ rd (A ix) ((row ix) ((k ix) - 1)).ctr ((row ix) ((k ix) - 1)).stk = some .nil) (hlen : ∀ ix : Nat, (A ix).length = 2 ^ 10) (hk : ∀ ix : Nat, (k ix) ≤ 2 ^ 10) {tP : ∀ ix : Nat, Nat} (htp : ∀ ix : Nat, (tP ix) = progTpW (wMachine (List.replicate (W ix) .S) ((Vt ix) ⬝ (x ix))).heap (W ix)) (S10 S9 SP : ∀ ix : Nat, Nat → List F) (qv : ∀ ix : Nat, EF → EF → List EF → F → List F → List F → List EF) (wm wc ww wp : ∀ ix : Nat, Nat → List (EF → EF → List F)) {Lwm Lwc Lww Lwp : ∀ ix : Nat, Nat} (hlwm : ∀ ix : Nat, ∀ c, ((wm ix) c).length = (Lwm ix)) (hlwc : ∀ ix : Nat, ∀ c, ((wc ix) c).length = (Lwc ix)) (hlww : ∀ ix : Nat, ∀ c, ((ww ix) c).length = (Lww ix)) (hlwp : ∀ ix : Nat, ∀ c, ((wp ix) c).length = (Lwp ix)) {K2 K4 : Nat} (hK2 : 0 < K2) (hK4 : 0 < K4) (φ : ∀ ix : Nat, Nat → Option (List (List (List EF)) × List (List (List (List EF))) × List (List (List EF))) → Nat) {N4 : Nat} (hφ : ∀ ix : Nat, ∀ m w, (φ ix) m w < N4) (hS10 : ∀ ix : Nat, ∀ c4, ∀ x ∈ (S10 ix) c4, x ∉ cosetL 1 (bbGen 10) (2 ^ 10)) (hS9 : ∀ ix : Nat, ∀ c4, ∀ x ∈ (S9 ix) c4, x ∉ cosetL 1 (bbGen 9) (2 ^ 9)) (hSP : ∀ ix : Nat, ∀ c4, ∀ x ∈ (SP ix) c4, x ∉ cosetL 1 (bbGen ((tP ix) + 1)) (2 ^ ((tP ix) + 1))) (hsz10 : ∀ ix : Nat, ∀ c4, 2 * ((S10 ix) c4).length + 8 ≤ 2 ^ 10) (hsz9 : ∀ ix : Nat, ∀ c4, 2 * ((S9 ix) c4).length + 8 ≤ 2 ^ 9) (hszP : ∀ ix : Nat, ∀ c4, 2 * ((SP ix) c4).length + 8 ≤ 2 ^ ((tP ix) + 1)) {ncw : ∀ ix : Nat, Nat} (αd : ∀ ix : Nat, Nat → EF) {B4 : ∀ ix : Nat, Nat} (hB4 : ∀ ix : Nat, sumTo K4 (fun c4 => indB (!genB ((αd ix) c4))) ≤ (B4 ix)) (fri : ∀ ix : Nat, Nat → EF → EF → List (EF → EF) → V) (hncw : ∀ ix : Nat, 4 ≤ (ncw ix)) (NR2 : ∀ ix : Nat, Nat) (Rb : ∀ ix : Nat, Nat → EF → EF → Nat → List (EF → EF)) (Ro : ∀ ix : Nat, Nat → EF → EF → Nat → Wv) {n1 n2 n3 : Nat} {NS1 NS2 NS3 : ∀ ix : Nat, Nat} (Com1 : ∀ ix : Nat, List (List (List F)) → Nat → Nat) (Pf1 : ∀ ix : Nat, Nat → Nat → Nat → Nat → Nat → Nat → List (List (List F)) → Nat → P1) (hc1 : ∀ ix : Nat, ComHides (NS1 ix) (Com1 ix)) (hp1 : ∀ ix : Nat, ∀ c4 T1 T2 T3 T4 M, ComPfHides (NS1 ix) (Com1 ix) ((Pf1 ix) c4 T1 T2 T3 T4 M) (opF ((wGroups (tP ix) ((S10 ix) c4) ((S9 ix) c4) ((SP ix) c4) EF.zero (qv ix)).map (·.base.S)) [0, 2, 4, 6])) (hr1 : ∀ ix : Nat, ∀ d σ, (Com1 ix) d σ < n1) (d1 : ∀ ix : Nat, List (List (List F))) (Com2 : ∀ ix : Nat, List (List (List F)) → Nat → Nat) (Pf2 : ∀ ix : Nat, Nat → Nat → Nat → Nat → Nat → Nat → List (List (List F)) → Nat → P2) (hc2 : ∀ ix : Nat, ComHides (NS2 ix) (Com2 ix)) (hp2 : ∀ ix : Nat, ∀ c4 T1 T2 T3 T4 M, ComPfHides (NS2 ix) (Com2 ix) ((Pf2 ix) c4 T1 T2 T3 T4 M) (opF ((wGroups (tP ix) ((S10 ix) c4) ((S9 ix) c4) ((SP ix) c4) EF.zero (qv ix)).map (·.base.S)) [1, 3, 5, 7])) (hr2 : ∀ ix : Nat, ∀ d σ, (Com2 ix) d σ < n2) (d2 : ∀ ix : Nat, List (List (List F))) (Com3 : ∀ ix : Nat, List (List (List (List F))) × List (List (List F)) → Nat → Nat) (Pf3 : ∀ ix : Nat, Nat → Nat → Nat → Nat → Nat → Nat → List (List (List (List F))) × List (List (List F)) → Nat → P3) (hc3 : ∀ ix : Nat, ComHides (NS3 ix) (Com3 ix)) (hp3 : ∀ ix : Nat, ∀ c4 T1 T2 T3 T4 M, ComPfHides (NS3 ix) (Com3 ix) ((Pf3 ix) c4 T1 T2 T3 T4 M) (fun d => (opQ (wSsT ((S10 ix) c4) ((S9 ix) c4) ((SP ix) c4)) d.1, opCw (wSsC (tP ix) ((S10 ix) c4) ((S9 ix) c4) ((SP ix) c4)) d.2))) (hr3 : ∀ ix : Nat, ∀ d σ, (Com3 ix) d σ < n3) (d3 : ∀ ix : Nat, List (List (List (List F))) × List (List (List F))) (hqr : ∀ ix : Nat, Nat × Nat × Nat × Nat → Nat × Nat × Nat × Nat → Nat × Nat × Nat × (Nat → Tup) → Bool)
    (hout : ∀ ix H p a c4 c1 c2 c3 xq, a.1 < Q4 * Q4 ∧ a.2.1 < K2 ∧ a.2.2.1 < Q4 ∧ a.2.2.2 < K4 → hqr ix H p xq = false →
      (witFS4T off (Vt ix) (x ix) (W ix) (A ix) (k ix) (row ix) (tP ix) (S10 ix) (S9 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NS1 ix) (NS2 ix) (NS3 ix) n1 n2 n3 (Com1 ix) (Pf1 ix) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix) (hqr ix)).out (prog4 (Q4 * Q4) K2 Q4 K4 H p a) c4 c1 c2 c3 xq = (witFS4T off (Vt ix) (x ix) (W ix) (A ix) (k ix) (row ix) (tP ix) (S10 ix) (S9 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NS1 ix) (NS2 ix) (NS3 ix) n1 n2 n3 (Com1 ix) (Pf1 ix) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix) (hqr ix)).out H c4 c1 c2 c3 xq)
    (hpq : ∀ i j c xa H xq, hqr i H ((witFS4T off (Vt j) (x j) (W j) (A j) (k j) (row j) (tP j) (S10 j) (S9 j) (SP j) (qv j) (wm j) (wc j) (ww j) (wp j) K2 K4 (φ j) N4 (ncw j) (αd j) (B4 j) (fri j) (NR2 j) (Rb j) (Ro j) (NS1 j) (NS2 j) (NS3 j) n1 n2 n3 (Com1 j) (Pf1 j) (Com2 j) (Pf2 j) (Com3 j) (Pf3 j) (hqr j)).pts c xa) xq = true → (witFS4T off (Vt i) (x i) (W i) (A i) (k i) (row i) (tP i) (S10 i) (S9 i) (SP i) (qv i) (wm i) (wc i) (ww i) (wp i) K2 K4 (φ i) N4 (ncw i) (αd i) (B4 i) (fri i) (NR2 i) (Rb i) (Ro i) (NS1 i) (NS2 i) (NS3 i) n1 n2 n3 (Com1 i) (Pf1 i) (Com2 i) (Pf2 i) (Com3 i) (Pf3 i) (hqr i)).m1 xq = ((witFS4T off (Vt j) (x j) (W j) (A j) (k j) (row j) (tP j) (S10 j) (S9 j) (SP j) (qv j) (wm j) (wc j) (ww j) (wp j) K2 K4 (φ j) N4 (ncw j) (αd j) (B4 j) (fri j) (NR2 j) (Rb j) (Ro j) (NS1 j) (NS2 j) (NS3 j) n1 n2 n3 (Com1 j) (Pf1 j) (Com2 j) (Pf2 j) (Com3 j) (Pf3 j) (hqr j)).pts c xa).1)
    (hφs : ∀ i j m w m' w', φ i m w = φ j m' w' → m % n1 = m' % n1) (δs : Nat → Nat)
    (hsp : ∀ ix d v, sumTo (NS1 ix) (fun σ => indB (decide (Com1 ix d σ = v))) ≤ δs ix) :
    ∀ n, ZKBT (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo (K4 ^ N4) (fun H4 => sumTo ((Q4 * Q4) ^ n1) (fun H1 =>
        sumTo (K2 ^ (n1 * n2)) (fun H2 => sumTo (Q4 ^ (n1 * (n2 * n3))) (fun H3 => f (H1, H2, H3, H4))))))
      (KPowD (fun _ => K4 * (Q4 * Q4 * (K2 * Q4))) n)
      (smPowD (X := fun _ => Nat × Nat × Nat × (Nat → Tup)) (fun ix => (witFS4T off (Vt ix) (x ix) (W ix) (A ix) (k ix) (row ix) (tP ix) (S10 ix) (S9 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NS1 ix) (NS2 ix) (NS3 ix) n1 n2 n3 (Com1 ix) (Pf1 ix) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix) (hqr ix)).sm 2) n)
      (scPowD (C := fun _ => Nat × Nat × Nat × Nat) (fun _ => fun (f : Nat × Nat × Nat × Nat → Nat) =>
        sumTo K4 (fun c4 => sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo Q4 (fun c3 => f (c1, c2, c3, c4)))))) n)
      (rvPowD (fun ix => read4T (Q4 * Q4) K2 Q4 K4 (witFS4T off (Vt ix) (x ix) (W ix) (A ix) (k ix) (row ix) (tP ix) (S10 ix) (S9 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NS1 ix) (NS2 ix) (NS3 ix) n1 n2 n3 (Com1 ix) (Pf1 ix) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix) (hqr ix)).m1 (witFS4T off (Vt ix) (x ix) (W ix) (A ix) (k ix) (row ix) (tP ix) (S10 ix) (S9 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NS1 ix) (NS2 ix) (NS3 ix) n1 n2 n3 (Com1 ix) (Pf1 ix) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix) (hqr ix)).m2 (witFS4T off (Vt ix) (x ix) (W ix) (A ix) (k ix) (row ix) (tP ix) (S10 ix) (S9 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NS1 ix) (NS2 ix) (NS3 ix) n1 n2 n3 (Com1 ix) (Pf1 ix) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix) (hqr ix)).m3 (witFS4T off (Vt ix) (x ix) (W ix) (A ix) (k ix) (row ix) (tP ix) (S10 ix) (S9 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NS1 ix) (NS2 ix) (NS3 ix) n1 n2 n3 (Com1 ix) (Pf1 ix) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix) (hqr ix)).q (witFS4T off (Vt ix) (x ix) (W ix) (A ix) (k ix) (row ix) (tP ix) (S10 ix) (S9 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NS1 ix) (NS2 ix) (NS3 ix) n1 n2 n3 (Com1 ix) (Pf1 ix) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix) (hqr ix)).out) n)
      (pgPowD (fun ix H c xx => prog4 (Q4 * Q4) K2 Q4 K4 H ((witFS4T off (Vt ix) (x ix) (W ix) (A ix) (k ix) (row ix) (tP ix) (S10 ix) (S9 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NS1 ix) (NS2 ix) (NS3 ix) n1 n2 n3 (Com1 ix) (Pf1 ix) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix) (hqr ix)).pts c xx) c) n) (svPowDT (fun ix H c xx => prog4 (Q4 * Q4) K2 Q4 K4 H ((witFS4T off (Vt ix) (x ix) (W ix) (A ix) (k ix) (row ix) (tP ix) (S10 ix) (S9 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NS1 ix) (NS2 ix) (NS3 ix) n1 n2 n3 (Com1 ix) (Pf1 ix) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix) (hqr ix)).pts c xx) c) (fun ix => (witFS4T off (Vt ix) (x ix) (W ix) (A ix) (k ix) (row ix) (tP ix) (S10 ix) (S9 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NS1 ix) (NS2 ix) (NS3 ix) n1 n2 n3 (Com1 ix) (Pf1 ix) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix) (hqr ix)).sv) n)
      (errPowD (fun _ => K4 * (Q4 * Q4 * (K2 * Q4))) (fun ix => (witFS4T off (Vt ix) (x ix) (W ix) (A ix) (k ix) (row ix) (tP ix) (S10 ix) (S9 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NS1 ix) (NS2 ix) (NS3 ix) n1 n2 n3 (Com1 ix) (Pf1 ix) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix) (hqr ix)).sm 2)
        (fun _ => fun (f : Nat × Nat × Nat × Nat → Nat) =>
          sumTo K4 (fun c4 => sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo Q4 (fun c3 => f (c1, c2, c3, c4))))))
        (fun ix => (witFS4T off (Vt ix) (x ix) (W ix) (A ix) (k ix) (row ix) (tP ix) (S10 ix) (S9 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NS1 ix) (NS2 ix) (NS3 ix) n1 n2 n3 (Com1 ix) (Pf1 ix) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix) (hqr ix)).ε)
        (fun j => sumTo K4 (fun c4 => sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo Q4 (fun c3 =>
          (witFS4T off (Vt j) (x j) (W j) (A j) (k j) (row j) (tP j) (S10 j) (S9 j) (SP j) (qv j) (wm j) (wc j) (ww j) (wp j) K2 K4 (φ j) N4 (ncw j) (αd j) (B4 j) (fri j) (NR2 j) (Rb j) (Ro j) (NS1 j) (NS2 j) (NS3 j) n1 n2 n3 (Com1 j) (Pf1 j) (Com2 j) (Pf2 j) (Com3 j) (Pf3 j) (hqr j)).sm 2 (fun _ => sumTo (K4 ^ N4) (fun H4 => sumTo ((Q4 * Q4) ^ n1) (fun H1 =>
            sumTo (K2 ^ (n1 * n2)) (fun H2 => sumTo (Q4 ^ (n1 * (n2 * n3))) (fun H3 =>
              hitBD (fun ix => (witFS4T off (Vt ix) (x ix) (W ix) (A ix) (k ix) (row ix) (tP ix) (S10 ix) (S9 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NS1 ix) (NS2 ix) (NS3 ix) n1 n2 n3 (Com1 ix) (Pf1 ix) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix) (hqr ix)).sm 2) (fun ix => (witFS4T off (Vt ix) (x ix) (W ix) (A ix) (k ix) (row ix) (tP ix) (S10 ix) (S9 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NS1 ix) (NS2 ix) (NS3 ix) n1 n2 n3 (Com1 ix) (Pf1 ix) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix) (hqr ix)).NS * ((witFS4T off (Vt ix) (x ix) (W ix) (A ix) (k ix) (row ix) (tP ix) (S10 ix) (S9 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NS1 ix) (NS2 ix) (NS3 ix) n1 n2 n3 (Com1 ix) (Pf1 ix) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix) (hqr ix)).NR * (Q4 ^ 2 * δs ix))) j)))))))))) n) := by
  intro n
  exact fs4_powDT (n1 := n1) hK2 hK4 (fun ix => (witFS4T off (Vt ix) (x ix) (W ix) (A ix) (k ix) (row ix) (tP ix) (S10 ix) (S9 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NS1 ix) (NS2 ix) (NS3 ix) n1 n2 n3 (Com1 ix) (Pf1 ix) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix) (hqr ix)))
    (fun ix c1 x => (Nat.add_mul_mod_self_left _ _ _).trans (Nat.mod_eq_of_lt (hr1 ix _ _)))
    (fun ix c1 c2 x => (Nat.add_mul_mod_self_left _ _ _).trans (Nat.mod_eq_of_lt (hr1 ix _ _)))
    (fun ix c x => (Nat.add_mul_mod_self_left _ _ _).trans (Nat.mod_eq_of_lt (hr1 ix _ _)))
    (fun ix c x => (Nat.add_mul_mod_self_left _ _ _).trans (Nat.mod_eq_of_lt (hr1 ix _ _)))
    (fun i j c1 c2 c3 x c xa h => hφs i j _ _ _ _ h) hout hpq
    (fun ix => (witFS4T off (Vt ix) (x ix) (W ix) (A ix) (k ix) (row ix) (tP ix) (S10 ix) (S9 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NS1 ix) (NS2 ix) (NS3 ix) n1 n2 n3 (Com1 ix) (Pf1 ix) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix) (hqr ix)).NS * ((witFS4T off (Vt ix) (x ix) (W ix) (A ix) (k ix) (row ix) (tP ix) (S10 ix) (S9 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NS1 ix) (NS2 ix) (NS3 ix) n1 n2 n3 (Com1 ix) (Pf1 ix) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix) (hqr ix)).NR * (Q4 ^ 2 * δs ix)))
    (fun ix v => spread_sum (Com1 ix) (witMain1 V Wv off (Vt ix) (x ix) (W ix) (A ix) (k ix) (row ix) (tP ix) (S10 ix) (S9 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (ncw ix) (αd ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix)) (hsp ix) v)
    (fun ix => wit_fs4T off (hwf ix) (hwl ix) (hW8 ix) (hA ix) (hK ix) (hlen ix) (hk ix) (htp ix) (S10 ix) (S9 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (hlwm ix) (hlwc ix) (hlww ix) (hlwp ix) hK2 hK4 (φ ix) (hφ ix) (hS10 ix) (hS9 ix) (hSP ix) (hsz10 ix) (hsz9 ix) (hszP ix) (αd ix) (hB4 ix) (fri ix) (hncw ix) (NR2 ix) (Rb ix) (Ro ix) (Com1 ix) (Pf1 ix) (hc1 ix) (hp1 ix) (hr1 ix) (d1 ix) (Com2 ix) (Pf2 ix) (hc2 ix) (hp2 ix) (hr2 ix) (d2 ix) (Com3 ix) (Pf3 ix) (hc3 ix) (hp3 ix) (hr3 ix) (d3 ix) (hqr ix)) n


set_option maxRecDepth 100000 in
/-- One composed statement's four-round data with the openings reading the tables (`comp_fs_open4_absT`'s), its output's table reads flagged by `hqr`. -/
def compFS4T {V Wv P1 P2 P3 : Type} (off : EF → String → EF) (R : Nat) (shp : BT) (Ps : List Term) (W : Nat) (A : List Cell) (e : Nat → Nat) (row : Nat → Air.Row) (tbM : Nat) (tbC : Nat) (tpP : Nat) (tpS : Nat) (SM : Nat → List F) (SC : Nat → List F) (S9 : Nat → List F) (SP : Nat → List F) (SS : Nat → List F) (qv : EF → EF → List EF → F → List F → List F → List EF) (wm : Nat → List (EF → EF → List F)) (wc : Nat → List (EF → EF → List F)) (ww : Nat → List (EF → EF → List F)) (wp : Nat → List (EF → EF → List F)) (wsg : Nat → List (EF → EF → List F)) (K2 : Nat) (K4 : Nat) (φ : Nat → Option (List (List (List EF)) × List (List (List (List EF))) × List (List (List EF))) → Nat) (N4 : Nat) (ncw : Nat) (αd : Nat → EF) (B4 : Nat) (fri : Nat → EF → EF → List (EF → EF) → V) (NR2 : Nat) (Rb : Nat → EF → EF → Nat → List (EF → EF)) (Ro : Nat → EF → EF → Nat → Wv) (NS1 : Nat) (NS2 : Nat) (NS3 : Nat) (n1 : Nat) (n2 : Nat) (n3 : Nat) (Com1 : List (List (List F)) → Nat → Nat) (Pf1 : Nat → Nat → Nat → Nat → Nat → Nat → List (List (List F)) → Nat → P1) (Com2 : List (List (List F)) → Nat → Nat) (Pf2 : Nat → Nat → Nat → Nat → Nat → Nat → List (List (List F)) → Nat → P2) (Com3 : List (List (List (List F))) × List (List (List F)) → Nat → Nat) (Pf3 : Nat → Nat → Nat → Nat → Nat → Nat → List (List (List (List F))) × List (List (List F)) → Nat → P3) (hqr : Nat × Nat × Nat × Nat → Nat × Nat × Nat × Nat → Nat × Nat × Nat × (Nat → Tup) → Bool) : FS4DT (Option P1 × Option (P2 × P3) × TViewN (PcsPV (V × Wv)) (EF × EF)) :=
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
    let rvo := fun (T1 T2 T3 T4 c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      ((ov1 c4 (rvF c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)).map (fun _ => Pf1 c4 T1 T2 T3 T4 (m3 c1 c2 x) (main1 x.2.2.2 x.2.2.1) x.1),
       (ovPair (ov2 c4) (ov3 c4) (rvF c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)).map
         (fun _ => pfPair NS2 (Pf2 c4 T1 T2 T3 T4 (m3 c1 c2 x)) (Pf3 c4 T1 T2 T3 T4 (m3 c1 c2 x)) (main2 c1 x.2.2.2 x.2.2.1, main3 c1 c2 x.2.2.2 x.2.2.1) x.2.1),
       rvF c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)
    let s1 := fun (c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) => Com1 (sdF (Ss c4) mk1 (sop1 c4 c2 c3 x.2.2.1 x.2.2.2)) x.1
    let s2 := fun (c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      s1 c4 c1 c2 c3 x + n1 * Com2 (sdF (Ss c4) mk2 (sop2 c4 c2 c3 c1 x.2.2.1 x.2.2.2)) (x.2.1 % NS2)
    let s3 := fun (c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      s1 c4 c1 c2 c3 x + n1 * comPair NS2 n2 Com2 Com3
        (sdF (Ss c4) mk2 (sop2 c4 c2 c3 c1 x.2.2.1 x.2.2.2), sd3 c4 (sop3 c4 c2 c3 c1 x.2.2.1 x.2.2.2)) x.2.1
    let svo := fun (T1 T2 T3 T4 c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      (some (Pf1 c4 T1 T2 T3 T4 (s3 c4 c1 c2 c3 x) (sdF (Ss c4) mk1 (sop1 c4 c2 c3 x.2.2.1 x.2.2.2)) x.1),
       some (pfPair NS2 (Pf2 c4 T1 T2 T3 T4 (s3 c4 c1 c2 c3 x)) (Pf3 c4 T1 T2 T3 T4 (s3 c4 c1 c2 c3 x)) (sdF (Ss c4) mk2 (sop2 c4 c2 c3 c1 x.2.2.1 x.2.2.2), sd3 c4 (sop3 c4 c2 c3 c1 x.2.2.1 x.2.2.2)) x.2.1),
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
    fun H c4 c1 c2 c3 x => rvo H.1 H.2.1 H.2.2.1 H.2.2.2 c4 c1 c2 c3 x,
    hqr,
    fun c x => (s1 c.2.2.2 c.1 c.2.1 c.2.2.1 x, s2 c.2.2.2 c.1 c.2.1 c.2.2.1 x, s3 c.2.2.2 c.1 c.2.1 c.2.2.1 x,
      φ (s3 c.2.2.2 c.1 c.2.1 c.2.2.1 x) (ozF (svF c.2.2.2 c.2.1 c.2.2.1 (efOf (c.1 / Q4)) (efOf (c.1 % Q4)) x.2.2.1 x.2.2.2))),
    fun H c x => (s1 c.2.2.2 c.1 c.2.1 c.2.2.1 x, s2 c.2.2.2 c.1 c.2.1 c.2.2.1 x, s3 c.2.2.2 c.1 c.2.1 c.2.2.1 x,
      svo (rset (Q4 * Q4) (s1 c.2.2.2 c.1 c.2.1 c.2.2.1 x) H.1 c.1) (rset K2 (s2 c.2.2.2 c.1 c.2.1 c.2.2.1 x) H.2.1 c.2.1) (rset Q4 (s3 c.2.2.2 c.1 c.2.1 c.2.2.1 x) H.2.2.1 c.2.2.1) (rset K4 (φ (s3 c.2.2.2 c.1 c.2.1 c.2.2.1 x) (ozF (svF c.2.2.2 c.2.1 c.2.2.1 (efOf (c.1 / Q4)) (efOf (c.1 % Q4)) x.2.2.1 x.2.2.2))) H.2.2.2 c.2.2.2) c.2.2.2 c.1 c.2.1 c.2.2.1 x),
    K4 ^ N4 * (K4 * ((Q4 * Q4) ^ n1 * (K2 ^ (n1 * n2) * (Q4 ^ (n1 * (n2 * n3)) *
          (K2 * (Q4 * (NS1 * (NS2 * NS3 * (Q4 * (NR * (Q4 ^ 2 * M)) + Q4 * (Q4 * (Q4 ^ 2 * 0)))))) +
            (Q4 * (P * P) * (K2 * Q4) + Q4 * Q4 * (K2 * (P * P))) * (NS1 * (NS2 * NS3 * (NR * (Q4 ^ 2 * 1)))))))) +
            B4 * (Q4 * Q4 * (K2 * Q4) * sm4 (fun _ => 1)))⟩


set_option maxRecDepth 100000 in
/-- **`comp_fs_open4_absT` on its data** (`compFS4T`). -/
theorem comp_fs4T {V Wv P1 P2 P3 : Type} (off : EF → String → EF) {R Lm : Nat} (hR : R ≤ 20) {shp : BT} {Ps : List Term}
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
    (Com1 : List (List (List F)) → Nat → Nat) (Pf1 : Nat → Nat → Nat → Nat → Nat → Nat → List (List (List F)) → Nat → P1) (hc1 : ComHides NS1 Com1)
    (hp1 : ∀ c4 T1 T2 T3 T4 M, ComPfHides NS1 Com1 (Pf1 c4 T1 T2 T3 T4 M) (opF ((cGroups tbM tbC tpP tpS (SM c4) (SC c4) (S9 c4) (SP c4) (SS c4) EF.zero qv).map (·.base.S)) [0, 2, 4, 6, 8]))
    (hr1 : ∀ d σ, Com1 d σ < n1) (d1 : List (List (List F)))
    (Com2 : List (List (List F)) → Nat → Nat) (Pf2 : Nat → Nat → Nat → Nat → Nat → Nat → List (List (List F)) → Nat → P2) (hc2 : ComHides NS2 Com2)
    (hp2 : ∀ c4 T1 T2 T3 T4 M, ComPfHides NS2 Com2 (Pf2 c4 T1 T2 T3 T4 M) (opF ((cGroups tbM tbC tpP tpS (SM c4) (SC c4) (S9 c4) (SP c4) (SS c4) EF.zero qv).map (·.base.S)) [1, 3, 5, 7, 9]))
    (hr2 : ∀ d σ, Com2 d σ < n2) (d2 : List (List (List F)))
    (Com3 : List (List (List (List F))) × List (List (List F)) → Nat → Nat)
    (Pf3 : Nat → Nat → Nat → Nat → Nat → Nat → List (List (List (List F))) × List (List (List F)) → Nat → P3) (hc3 : ComHides NS3 Com3)
    (hp3 : ∀ c4 T1 T2 T3 T4 M, ComPfHides NS3 Com3 (Pf3 c4 T1 T2 T3 T4 M) (fun d => (opQ (cSsT (SM c4) (SC c4) (S9 c4) (SP c4) (SS c4)) d.1, opCw (cSsC tbM tbC tpP tpS (SM c4) (SC c4) (S9 c4) (SP c4) (SS c4)) d.2)))
    (hr3 : ∀ d σ, Com3 d σ < n3) (d3 : List (List (List (List F))) × List (List (List F))) (hqr : Nat × Nat × Nat × Nat → Nat × Nat × Nat × Nat → Nat × Nat × Nat × (Nat → Tup) → Bool) :
    ZKBT (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo (K4 ^ N4) (fun H4 => sumTo ((Q4 * Q4) ^ n1) (fun H1 =>
      sumTo (K2 ^ (n1 * n2)) (fun H2 => sumTo (Q4 ^ (n1 * (n2 * n3))) (fun H3 => f (H1, H2, H3, H4))))))
      (K4 * (Q4 * Q4 * (K2 * Q4))) ((compFS4T off R shp Ps W A e row tbM tbC tpP tpS SM SC S9 SP SS qv wm wc ww wp wsg K2 K4 φ N4 ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Pf1 Com2 Pf2 Com3 Pf3 hqr).sm 2)
      (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo K4 (fun c4 => sumTo (Q4 * Q4) (fun c1 =>
        sumTo K2 (fun c2 => sumTo Q4 (fun c3 => f (c1, c2, c3, c4))))))
      (read4T (Q4 * Q4) K2 Q4 K4 (compFS4T off R shp Ps W A e row tbM tbC tpP tpS SM SC S9 SP SS qv wm wc ww wp wsg K2 K4 φ N4 ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Pf1 Com2 Pf2 Com3 Pf3 hqr).m1 (compFS4T off R shp Ps W A e row tbM tbC tpP tpS SM SC S9 SP SS qv wm wc ww wp wsg K2 K4 φ N4 ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Pf1 Com2 Pf2 Com3 Pf3 hqr).m2 (compFS4T off R shp Ps W A e row tbM tbC tpP tpS SM SC S9 SP SS qv wm wc ww wp wsg K2 K4 φ N4 ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Pf1 Com2 Pf2 Com3 Pf3 hqr).m3 (compFS4T off R shp Ps W A e row tbM tbC tpP tpS SM SC S9 SP SS qv wm wc ww wp wsg K2 K4 φ N4 ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Pf1 Com2 Pf2 Com3 Pf3 hqr).q (compFS4T off R shp Ps W A e row tbM tbC tpP tpS SM SC S9 SP SS qv wm wc ww wp wsg K2 K4 φ N4 ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Pf1 Com2 Pf2 Com3 Pf3 hqr).out)
      (fun H c x => prog4 (Q4 * Q4) K2 Q4 K4 H ((compFS4T off R shp Ps W A e row tbM tbC tpP tpS SM SC S9 SP SS qv wm wc ww wp wsg K2 K4 φ N4 ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Pf1 Com2 Pf2 Com3 Pf3 hqr).pts c x) c) (compFS4T off R shp Ps W A e row tbM tbC tpP tpS SM SC S9 SP SS qv wm wc ww wp wsg K2 K4 φ N4 ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Pf1 Com2 Pf2 Com3 Pf3 hqr).sv (compFS4T off R shp Ps W A e row tbM tbC tpP tpS SM SC S9 SP SS qv wm wc ww wp wsg K2 K4 φ N4 ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Pf1 Com2 Pf2 Com3 Pf3 hqr).ε :=
  comp_fs_open4_absT off hR hrl hr hA hlen hLm hK hNW htM htC htP htS SM SC S9 SP SS qv wm wc ww wp wsg hlwm hlwc hlww hlwp hlwsg hK2 hK4 φ hφ hSM hSC hS9 hSP hSS hszM hszC hsz9 hszP hszS αd hB4 fri hncw NR2 Rb Ro Com1 Pf1 hc1 hp1 hr1 d1 Com2 Pf2 hc2 hp2 hr2 d2 Com3 Pf3 hc3 hp3 hr3 d3


set_option maxRecDepth 100000 in
/-- **`n` composed statements of different shapes under one oracle, the openings reading the
    tables** (`fs4_powDT` over `comp_fs4T`): `comp_fs_open4_powD`'s hypotheses
    with each statement's openings `Pf? c4 T1 T2 T3 T4 M`, their output's table
    reads flagged by `hqr ix`, unchanged by an in-range programming they
    miss (`hout`), a hit carrying the reader's first commitment (`hpq`);
    as there, the query hashes keep the first commitment's digit (`hφs`) and
    each first commitment spreads (`hsp`). -/
theorem comp_fs_open4_powDT {V Wv P1 P2 P3 : Type}  (off : EF → String → EF) {R Lm : ∀ ix : Nat, Nat} (hR : ∀ ix : Nat, (R ix) ≤ 20) {shp : ∀ ix : Nat, BT} {Ps : ∀ ix : Nat, List Term} {W : ∀ ix : Nat, Nat} {ρ : ∀ ix : Nat, Nat → Bool} {region : ∀ ix : Nat, List Cell} (hrl : ∀ ix : Nat, (region ix).length = (W ix)) (hr : ∀ ix : Nat, ∀ i c, (region ix)[i]? = some c → cellOK (BT.nleaves (shp ix) + 3 + i) c = true) {A : ∀ ix : Nat, List Cell} {e : ∀ ix : Nat, Nat → Nat} {row : ∀ ix : Nat, Nat → Air.Row} (hA : ∀ ix : Nat, AcceptsC (A ix) (cMachine (ρ ix) (shp ix) (region ix) (Ps ix)) (cHeap (ρ ix) (shp ix) (region ix) (Ps ix)).2
      (cHeap (ρ ix) (shp ix) (region ix) (Ps ix)).1.length (Ps ix).length (e ix) (row ix)) (hlen : ∀ ix : Nat, (A ix).length = 2 ^ (Lm ix)) (hLm : ∀ ix : Nat, (Lm ix) ≤ 20) (hK : ∀ ix : Nat, (e ix) ((Ps ix).length - 1) < 2 ^ (R ix)) (hNW : ∀ ix : Nat, BT.nleaves (shp ix) + (W ix) ≤ 2 ^ 8) {tbM tbC tpP tpS : ∀ ix : Nat, Nat} (htM : ∀ ix : Nat, (tbM ix) + 1 = (Lm ix)) (htC : ∀ ix : Nat, (tbC ix) + 1 = (R ix)) (htP : ∀ ix : Nat, (tpP ix) = progTpC (blankM (shp ix) (W ix) (Ps ix)).heap (BT.nleaves (shp ix)) (W ix)) (htS : ∀ ix : Nat, (tpS ix) = segTp (blankRoots (shp ix) (W ix) (Ps ix))) (SM SC S9 SP SS : ∀ ix : Nat, Nat → List F) (qv : ∀ ix : Nat, EF → EF → List EF → F → List F → List F → List EF) (wm wc ww wp wsg : ∀ ix : Nat, Nat → List (EF → EF → List F)) {Lwm Lwc Lww Lwp Lwsg : ∀ ix : Nat, Nat} (hlwm : ∀ ix : Nat, ∀ c, ((wm ix) c).length = (Lwm ix)) (hlwc : ∀ ix : Nat, ∀ c, ((wc ix) c).length = (Lwc ix)) (hlww : ∀ ix : Nat, ∀ c, ((ww ix) c).length = (Lww ix)) (hlwp : ∀ ix : Nat, ∀ c, ((wp ix) c).length = (Lwp ix)) (hlwsg : ∀ ix : Nat, ∀ c, ((wsg ix) c).length = (Lwsg ix)) {K2 K4 : Nat} (hK2 : 0 < K2) (hK4 : 0 < K4) (φ : ∀ ix : Nat, Nat → Option (List (List (List EF)) × List (List (List (List EF))) × List (List (List EF))) → Nat) {N4 : Nat} (hφ : ∀ ix : Nat, ∀ m w, (φ ix) m w < N4) (hSM : ∀ ix : Nat, ∀ c4, ∀ x ∈ (SM ix) c4, x ∉ cosetL 1 (bbGen ((tbM ix) + 1)) (2 ^ ((tbM ix) + 1))) (hSC : ∀ ix : Nat, ∀ c4, ∀ x ∈ (SC ix) c4, x ∉ cosetL 1 (bbGen ((tbC ix) + 1)) (2 ^ ((tbC ix) + 1))) (hS9 : ∀ ix : Nat, ∀ c4, ∀ x ∈ (S9 ix) c4, x ∉ cosetL 1 (bbGen 9) (2 ^ 9)) (hSP : ∀ ix : Nat, ∀ c4, ∀ x ∈ (SP ix) c4, x ∉ cosetL 1 (bbGen ((tpP ix) + 1)) (2 ^ ((tpP ix) + 1))) (hSS : ∀ ix : Nat, ∀ c4, ∀ x ∈ (SS ix) c4, x ∉ cosetL 1 (bbGen ((tpS ix) + 1)) (2 ^ ((tpS ix) + 1))) (hszM : ∀ ix : Nat, ∀ c4, 2 * ((SM ix) c4).length + 8 ≤ 2 ^ ((tbM ix) + 1)) (hszC : ∀ ix : Nat, ∀ c4, 2 * ((SC ix) c4).length + 8 ≤ 2 ^ ((tbC ix) + 1)) (hsz9 : ∀ ix : Nat, ∀ c4, 2 * ((S9 ix) c4).length + 8 ≤ 2 ^ 9) (hszP : ∀ ix : Nat, ∀ c4, 2 * ((SP ix) c4).length + 8 ≤ 2 ^ ((tpP ix) + 1)) (hszS : ∀ ix : Nat, ∀ c4, 2 * ((SS ix) c4).length + 8 ≤ 2 ^ ((tpS ix) + 1)) {ncw : ∀ ix : Nat, Nat} (αd : ∀ ix : Nat, Nat → EF) {B4 : ∀ ix : Nat, Nat} (hB4 : ∀ ix : Nat, sumTo K4 (fun c4 => indB (!genB ((αd ix) c4))) ≤ (B4 ix)) (fri : ∀ ix : Nat, Nat → EF → EF → List (EF → EF) → V) (hncw : ∀ ix : Nat, 4 ≤ (ncw ix)) (NR2 : ∀ ix : Nat, Nat) (Rb : ∀ ix : Nat, Nat → EF → EF → Nat → List (EF → EF)) (Ro : ∀ ix : Nat, Nat → EF → EF → Nat → Wv) {n1 n2 n3 : Nat} {NS1 NS2 NS3 : ∀ ix : Nat, Nat} (Com1 : ∀ ix : Nat, List (List (List F)) → Nat → Nat) (Pf1 : ∀ ix : Nat, Nat → Nat → Nat → Nat → Nat → Nat → List (List (List F)) → Nat → P1) (hc1 : ∀ ix : Nat, ComHides (NS1 ix) (Com1 ix)) (hp1 : ∀ ix : Nat, ∀ c4 T1 T2 T3 T4 M, ComPfHides (NS1 ix) (Com1 ix) ((Pf1 ix) c4 T1 T2 T3 T4 M) (opF ((cGroups (tbM ix) (tbC ix) (tpP ix) (tpS ix) ((SM ix) c4) ((SC ix) c4) ((S9 ix) c4) ((SP ix) c4) ((SS ix) c4) EF.zero (qv ix)).map (·.base.S)) [0, 2, 4, 6, 8])) (hr1 : ∀ ix : Nat, ∀ d σ, (Com1 ix) d σ < n1) (d1 : ∀ ix : Nat, List (List (List F))) (Com2 : ∀ ix : Nat, List (List (List F)) → Nat → Nat) (Pf2 : ∀ ix : Nat, Nat → Nat → Nat → Nat → Nat → Nat → List (List (List F)) → Nat → P2) (hc2 : ∀ ix : Nat, ComHides (NS2 ix) (Com2 ix)) (hp2 : ∀ ix : Nat, ∀ c4 T1 T2 T3 T4 M, ComPfHides (NS2 ix) (Com2 ix) ((Pf2 ix) c4 T1 T2 T3 T4 M) (opF ((cGroups (tbM ix) (tbC ix) (tpP ix) (tpS ix) ((SM ix) c4) ((SC ix) c4) ((S9 ix) c4) ((SP ix) c4) ((SS ix) c4) EF.zero (qv ix)).map (·.base.S)) [1, 3, 5, 7, 9])) (hr2 : ∀ ix : Nat, ∀ d σ, (Com2 ix) d σ < n2) (d2 : ∀ ix : Nat, List (List (List F))) (Com3 : ∀ ix : Nat, List (List (List (List F))) × List (List (List F)) → Nat → Nat) (Pf3 : ∀ ix : Nat, Nat → Nat → Nat → Nat → Nat → Nat → List (List (List (List F))) × List (List (List F)) → Nat → P3) (hc3 : ∀ ix : Nat, ComHides (NS3 ix) (Com3 ix)) (hp3 : ∀ ix : Nat, ∀ c4 T1 T2 T3 T4 M, ComPfHides (NS3 ix) (Com3 ix) ((Pf3 ix) c4 T1 T2 T3 T4 M) (fun d => (opQ (cSsT ((SM ix) c4) ((SC ix) c4) ((S9 ix) c4) ((SP ix) c4) ((SS ix) c4)) d.1, opCw (cSsC (tbM ix) (tbC ix) (tpP ix) (tpS ix) ((SM ix) c4) ((SC ix) c4) ((S9 ix) c4) ((SP ix) c4) ((SS ix) c4)) d.2))) (hr3 : ∀ ix : Nat, ∀ d σ, (Com3 ix) d σ < n3) (d3 : ∀ ix : Nat, List (List (List (List F))) × List (List (List F))) (hqr : ∀ ix : Nat, Nat × Nat × Nat × Nat → Nat × Nat × Nat × Nat → Nat × Nat × Nat × (Nat → Tup) → Bool)
    (hout : ∀ ix H p a c4 c1 c2 c3 xq, a.1 < Q4 * Q4 ∧ a.2.1 < K2 ∧ a.2.2.1 < Q4 ∧ a.2.2.2 < K4 → hqr ix H p xq = false →
      (compFS4T off (R ix) (shp ix) (Ps ix) (W ix) (A ix) (e ix) (row ix) (tbM ix) (tbC ix) (tpP ix) (tpS ix) (SM ix) (SC ix) (S9 ix) (SP ix) (SS ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (wsg ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NS1 ix) (NS2 ix) (NS3 ix) n1 n2 n3 (Com1 ix) (Pf1 ix) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix) (hqr ix)).out (prog4 (Q4 * Q4) K2 Q4 K4 H p a) c4 c1 c2 c3 xq = (compFS4T off (R ix) (shp ix) (Ps ix) (W ix) (A ix) (e ix) (row ix) (tbM ix) (tbC ix) (tpP ix) (tpS ix) (SM ix) (SC ix) (S9 ix) (SP ix) (SS ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (wsg ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NS1 ix) (NS2 ix) (NS3 ix) n1 n2 n3 (Com1 ix) (Pf1 ix) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix) (hqr ix)).out H c4 c1 c2 c3 xq)
    (hpq : ∀ i j c xa H xq, hqr i H ((compFS4T off (R j) (shp j) (Ps j) (W j) (A j) (e j) (row j) (tbM j) (tbC j) (tpP j) (tpS j) (SM j) (SC j) (S9 j) (SP j) (SS j) (qv j) (wm j) (wc j) (ww j) (wp j) (wsg j) K2 K4 (φ j) N4 (ncw j) (αd j) (B4 j) (fri j) (NR2 j) (Rb j) (Ro j) (NS1 j) (NS2 j) (NS3 j) n1 n2 n3 (Com1 j) (Pf1 j) (Com2 j) (Pf2 j) (Com3 j) (Pf3 j) (hqr j)).pts c xa) xq = true → (compFS4T off (R i) (shp i) (Ps i) (W i) (A i) (e i) (row i) (tbM i) (tbC i) (tpP i) (tpS i) (SM i) (SC i) (S9 i) (SP i) (SS i) (qv i) (wm i) (wc i) (ww i) (wp i) (wsg i) K2 K4 (φ i) N4 (ncw i) (αd i) (B4 i) (fri i) (NR2 i) (Rb i) (Ro i) (NS1 i) (NS2 i) (NS3 i) n1 n2 n3 (Com1 i) (Pf1 i) (Com2 i) (Pf2 i) (Com3 i) (Pf3 i) (hqr i)).m1 xq = ((compFS4T off (R j) (shp j) (Ps j) (W j) (A j) (e j) (row j) (tbM j) (tbC j) (tpP j) (tpS j) (SM j) (SC j) (S9 j) (SP j) (SS j) (qv j) (wm j) (wc j) (ww j) (wp j) (wsg j) K2 K4 (φ j) N4 (ncw j) (αd j) (B4 j) (fri j) (NR2 j) (Rb j) (Ro j) (NS1 j) (NS2 j) (NS3 j) n1 n2 n3 (Com1 j) (Pf1 j) (Com2 j) (Pf2 j) (Com3 j) (Pf3 j) (hqr j)).pts c xa).1)
    (hφs : ∀ i j m w m' w', φ i m w = φ j m' w' → m % n1 = m' % n1) (δs : Nat → Nat)
    (hsp : ∀ ix d v, sumTo (NS1 ix) (fun σ => indB (decide (Com1 ix d σ = v))) ≤ δs ix) :
    ∀ n, ZKBT (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo (K4 ^ N4) (fun H4 => sumTo ((Q4 * Q4) ^ n1) (fun H1 =>
        sumTo (K2 ^ (n1 * n2)) (fun H2 => sumTo (Q4 ^ (n1 * (n2 * n3))) (fun H3 => f (H1, H2, H3, H4))))))
      (KPowD (fun _ => K4 * (Q4 * Q4 * (K2 * Q4))) n)
      (smPowD (X := fun _ => Nat × Nat × Nat × (Nat → Tup)) (fun ix => (compFS4T off (R ix) (shp ix) (Ps ix) (W ix) (A ix) (e ix) (row ix) (tbM ix) (tbC ix) (tpP ix) (tpS ix) (SM ix) (SC ix) (S9 ix) (SP ix) (SS ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (wsg ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NS1 ix) (NS2 ix) (NS3 ix) n1 n2 n3 (Com1 ix) (Pf1 ix) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix) (hqr ix)).sm 2) n)
      (scPowD (C := fun _ => Nat × Nat × Nat × Nat) (fun _ => fun (f : Nat × Nat × Nat × Nat → Nat) =>
        sumTo K4 (fun c4 => sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo Q4 (fun c3 => f (c1, c2, c3, c4)))))) n)
      (rvPowD (fun ix => read4T (Q4 * Q4) K2 Q4 K4 (compFS4T off (R ix) (shp ix) (Ps ix) (W ix) (A ix) (e ix) (row ix) (tbM ix) (tbC ix) (tpP ix) (tpS ix) (SM ix) (SC ix) (S9 ix) (SP ix) (SS ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (wsg ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NS1 ix) (NS2 ix) (NS3 ix) n1 n2 n3 (Com1 ix) (Pf1 ix) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix) (hqr ix)).m1 (compFS4T off (R ix) (shp ix) (Ps ix) (W ix) (A ix) (e ix) (row ix) (tbM ix) (tbC ix) (tpP ix) (tpS ix) (SM ix) (SC ix) (S9 ix) (SP ix) (SS ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (wsg ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NS1 ix) (NS2 ix) (NS3 ix) n1 n2 n3 (Com1 ix) (Pf1 ix) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix) (hqr ix)).m2 (compFS4T off (R ix) (shp ix) (Ps ix) (W ix) (A ix) (e ix) (row ix) (tbM ix) (tbC ix) (tpP ix) (tpS ix) (SM ix) (SC ix) (S9 ix) (SP ix) (SS ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (wsg ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NS1 ix) (NS2 ix) (NS3 ix) n1 n2 n3 (Com1 ix) (Pf1 ix) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix) (hqr ix)).m3 (compFS4T off (R ix) (shp ix) (Ps ix) (W ix) (A ix) (e ix) (row ix) (tbM ix) (tbC ix) (tpP ix) (tpS ix) (SM ix) (SC ix) (S9 ix) (SP ix) (SS ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (wsg ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NS1 ix) (NS2 ix) (NS3 ix) n1 n2 n3 (Com1 ix) (Pf1 ix) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix) (hqr ix)).q (compFS4T off (R ix) (shp ix) (Ps ix) (W ix) (A ix) (e ix) (row ix) (tbM ix) (tbC ix) (tpP ix) (tpS ix) (SM ix) (SC ix) (S9 ix) (SP ix) (SS ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (wsg ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NS1 ix) (NS2 ix) (NS3 ix) n1 n2 n3 (Com1 ix) (Pf1 ix) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix) (hqr ix)).out) n)
      (pgPowD (fun ix H c x => prog4 (Q4 * Q4) K2 Q4 K4 H ((compFS4T off (R ix) (shp ix) (Ps ix) (W ix) (A ix) (e ix) (row ix) (tbM ix) (tbC ix) (tpP ix) (tpS ix) (SM ix) (SC ix) (S9 ix) (SP ix) (SS ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (wsg ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NS1 ix) (NS2 ix) (NS3 ix) n1 n2 n3 (Com1 ix) (Pf1 ix) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix) (hqr ix)).pts c x) c) n) (svPowDT (fun ix H c xx => prog4 (Q4 * Q4) K2 Q4 K4 H ((compFS4T off (R ix) (shp ix) (Ps ix) (W ix) (A ix) (e ix) (row ix) (tbM ix) (tbC ix) (tpP ix) (tpS ix) (SM ix) (SC ix) (S9 ix) (SP ix) (SS ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (wsg ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NS1 ix) (NS2 ix) (NS3 ix) n1 n2 n3 (Com1 ix) (Pf1 ix) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix) (hqr ix)).pts c xx) c) (fun ix => (compFS4T off (R ix) (shp ix) (Ps ix) (W ix) (A ix) (e ix) (row ix) (tbM ix) (tbC ix) (tpP ix) (tpS ix) (SM ix) (SC ix) (S9 ix) (SP ix) (SS ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (wsg ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NS1 ix) (NS2 ix) (NS3 ix) n1 n2 n3 (Com1 ix) (Pf1 ix) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix) (hqr ix)).sv) n)
      (errPowD (fun _ => K4 * (Q4 * Q4 * (K2 * Q4))) (fun ix => (compFS4T off (R ix) (shp ix) (Ps ix) (W ix) (A ix) (e ix) (row ix) (tbM ix) (tbC ix) (tpP ix) (tpS ix) (SM ix) (SC ix) (S9 ix) (SP ix) (SS ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (wsg ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NS1 ix) (NS2 ix) (NS3 ix) n1 n2 n3 (Com1 ix) (Pf1 ix) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix) (hqr ix)).sm 2)
        (fun _ => fun (f : Nat × Nat × Nat × Nat → Nat) =>
          sumTo K4 (fun c4 => sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo Q4 (fun c3 => f (c1, c2, c3, c4))))))
        (fun ix => (compFS4T off (R ix) (shp ix) (Ps ix) (W ix) (A ix) (e ix) (row ix) (tbM ix) (tbC ix) (tpP ix) (tpS ix) (SM ix) (SC ix) (S9 ix) (SP ix) (SS ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (wsg ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NS1 ix) (NS2 ix) (NS3 ix) n1 n2 n3 (Com1 ix) (Pf1 ix) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix) (hqr ix)).ε)
        (fun j => sumTo K4 (fun c4 => sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo Q4 (fun c3 =>
          (compFS4T off (R j) (shp j) (Ps j) (W j) (A j) (e j) (row j) (tbM j) (tbC j) (tpP j) (tpS j) (SM j) (SC j) (S9 j) (SP j) (SS j) (qv j) (wm j) (wc j) (ww j) (wp j) (wsg j) K2 K4 (φ j) N4 (ncw j) (αd j) (B4 j) (fri j) (NR2 j) (Rb j) (Ro j) (NS1 j) (NS2 j) (NS3 j) n1 n2 n3 (Com1 j) (Pf1 j) (Com2 j) (Pf2 j) (Com3 j) (Pf3 j) (hqr j)).sm 2 (fun _ => sumTo (K4 ^ N4) (fun H4 => sumTo ((Q4 * Q4) ^ n1) (fun H1 =>
            sumTo (K2 ^ (n1 * n2)) (fun H2 => sumTo (Q4 ^ (n1 * (n2 * n3))) (fun H3 =>
              hitBD (fun ix => (compFS4T off (R ix) (shp ix) (Ps ix) (W ix) (A ix) (e ix) (row ix) (tbM ix) (tbC ix) (tpP ix) (tpS ix) (SM ix) (SC ix) (S9 ix) (SP ix) (SS ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (wsg ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NS1 ix) (NS2 ix) (NS3 ix) n1 n2 n3 (Com1 ix) (Pf1 ix) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix) (hqr ix)).sm 2) (fun ix => (compFS4T off (R ix) (shp ix) (Ps ix) (W ix) (A ix) (e ix) (row ix) (tbM ix) (tbC ix) (tpP ix) (tpS ix) (SM ix) (SC ix) (S9 ix) (SP ix) (SS ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (wsg ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NS1 ix) (NS2 ix) (NS3 ix) n1 n2 n3 (Com1 ix) (Pf1 ix) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix) (hqr ix)).NS * ((compFS4T off (R ix) (shp ix) (Ps ix) (W ix) (A ix) (e ix) (row ix) (tbM ix) (tbC ix) (tpP ix) (tpS ix) (SM ix) (SC ix) (S9 ix) (SP ix) (SS ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (wsg ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NS1 ix) (NS2 ix) (NS3 ix) n1 n2 n3 (Com1 ix) (Pf1 ix) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix) (hqr ix)).NR * (Q4 ^ 2 * δs ix))) j)))))))))) n) := by
  intro n
  exact fs4_powDT (n1 := n1) hK2 hK4 (fun ix => (compFS4T off (R ix) (shp ix) (Ps ix) (W ix) (A ix) (e ix) (row ix) (tbM ix) (tbC ix) (tpP ix) (tpS ix) (SM ix) (SC ix) (S9 ix) (SP ix) (SS ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (wsg ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NS1 ix) (NS2 ix) (NS3 ix) n1 n2 n3 (Com1 ix) (Pf1 ix) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix) (hqr ix)))
    (fun ix c1 x => (Nat.add_mul_mod_self_left _ _ _).trans (Nat.mod_eq_of_lt (hr1 ix _ _)))
    (fun ix c1 c2 x => (Nat.add_mul_mod_self_left _ _ _).trans (Nat.mod_eq_of_lt (hr1 ix _ _)))
    (fun ix c x => (Nat.add_mul_mod_self_left _ _ _).trans (Nat.mod_eq_of_lt (hr1 ix _ _)))
    (fun ix c x => (Nat.add_mul_mod_self_left _ _ _).trans (Nat.mod_eq_of_lt (hr1 ix _ _)))
    (fun i j c1 c2 c3 x c xa h => hφs i j _ _ _ _ h) hout hpq
    (fun ix => (compFS4T off (R ix) (shp ix) (Ps ix) (W ix) (A ix) (e ix) (row ix) (tbM ix) (tbC ix) (tpP ix) (tpS ix) (SM ix) (SC ix) (S9 ix) (SP ix) (SS ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (wsg ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NS1 ix) (NS2 ix) (NS3 ix) n1 n2 n3 (Com1 ix) (Pf1 ix) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix) (hqr ix)).NS * ((compFS4T off (R ix) (shp ix) (Ps ix) (W ix) (A ix) (e ix) (row ix) (tbM ix) (tbC ix) (tpP ix) (tpS ix) (SM ix) (SC ix) (S9 ix) (SP ix) (SS ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (wsg ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NS1 ix) (NS2 ix) (NS3 ix) n1 n2 n3 (Com1 ix) (Pf1 ix) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix) (hqr ix)).NR * (Q4 ^ 2 * δs ix)))
    (fun ix v => spread_sum (Com1 ix) (compMain1 V Wv off (R ix) (shp ix) (Ps ix) (W ix) (A ix) (e ix) (row ix) (tbM ix) (tbC ix) (tpP ix) (tpS ix) (SM ix) (SC ix) (S9 ix) (SP ix) (SS ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (wsg ix) (ncw ix) (αd ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix)) (hsp ix) v)
    (fun ix => comp_fs4T off (hR ix) (hrl ix) (hr ix) (hA ix) (hlen ix) (hLm ix) (hK ix) (hNW ix) (htM ix) (htC ix) (htP ix) (htS ix) (SM ix) (SC ix) (S9 ix) (SP ix) (SS ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (wsg ix) (hlwm ix) (hlwc ix) (hlww ix) (hlwp ix) (hlwsg ix) hK2 hK4 (φ ix) (hφ ix) (hSM ix) (hSC ix) (hS9 ix) (hSP ix) (hSS ix) (hszM ix) (hszC ix) (hsz9 ix) (hszP ix) (hszS ix) (αd ix) (hB4 ix) (fri ix) (hncw ix) (NR2 ix) (Rb ix) (Ro ix) (Com1 ix) (Pf1 ix) (hc1 ix) (hp1 ix) (hr1 ix) (d1 ix) (Com2 ix) (Pf2 ix) (hc2 ix) (hp2 ix) (hr2 ix) (d2 ix) (Com3 ix) (Pf3 ix) (hc3 ix) (hp3 ix) (hr3 ix) (d3 ix) (hqr ix)) n

end
end Circuit
