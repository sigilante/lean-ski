import Ski.ZK.ROMMerkleIdx
import Ski.ZK.ROMInstMC
import Ski.ZK.ROMMerkleRowsP

/-!
# The Sudoku proof at FRI's leaves, Plonky3's leaf hash

`ROMMerkleIdx`'s `sud_fs_open4ROMM_fri` with the leaves at Plonky3's
positions, the row and salt alone (`posRowsP`): two leaves with equal rows
and salts share a hash, counted by `sud_fs_open4ROMMC`.  The opened
positions are fixed by the opened values as the indexed ones are
(`posRowsP_of_posRows`).  One direction.
-/

set_option autoImplicit false
namespace Circuit
open ZKF

section
open B Air Stmt Mach Sudoku SudokuText Compose CompM Wit

set_option maxRecDepth 100000 in
/-- **`sud_fs_open4ROMM_fri` at Plonky3's leaf positions**: the leaf hash
    its row and salt alone, no index (`posRowsP`), so leaves may share a
    hash (`sud_fs_open4ROMMC`).  The bound gains `L sQ (kQ + L) / NSl +
    2 L² sQ / NSl` a draw; one direction. -/
theorem sud_fs_open4ROMMC_fri {V Wv Pq P2 P3 : Type} (off : EF → String → EF) {puzzle : List Nat} (hc : CluesOK (cluesOf puzzle))
    {ρ : Nat → Bool} {A : List Cell} {k : Nat} {row : Nat → Air.Row}
    (hA : AcceptsFrom A (stmtMachine ρ 729 (sudokuExpr (cluesOf puzzle)) ACC REJ) k row)
    (hacc : rd A (row (k - 1)).ctr (row (k - 1)).hd = some (.atom ACC))
    (hlen : A.length = 2 ^ 16) (hk : k ≤ 2 ^ 16)
    {tP : Nat} (htp : tP = progTp (stmtMachine (fun _ => false) 729 (sudokuExpr (cluesOf puzzle)) ACC REJ).heap)
    {bl sh : Nat → Nat} {idx : Nat → List Nat}
    (qv : EF → EF → List EF → F → List F → List F → List EF)
    (wm wc ww wp : Nat → List (EF → EF → List F)) {Lwm Lwc Lww Lwp : Nat} (hlwm : ∀ c, (wm c).length = Lwm)
    (hlwc : ∀ c, (wc c).length = Lwc) (hlww : ∀ c, (ww c).length = Lww) (hlwp : ∀ c, (wp c).length = Lwp)
    {K2 K4 : Nat} (hK2 : 0 < K2) (hK4 : 0 < K4)
    (φ : Nat → Option (List (List (List EF)) × List (List (List (List EF))) × List (List (List EF))) → Nat) {N4 : Nat} (hφ : ∀ m w, φ m w < N4)
    (hsz16 : ∀ c4, 2 * ((friS bl sh idx 0) c4).length + 8 ≤ 2 ^ 16) (hsz : ∀ c4, 2 * ((friS bl sh idx 4) c4).length + 8 ≤ 2 ^ 10)
    (hszP : ∀ c4, 2 * ((friS bl sh idx 6) c4).length + 8 ≤ 2 ^ (tP + 1)) {ncw : Nat} (αd : Nat → EF) {B4 : Nat}
    (hB4 : sumTo K4 (fun c4 => indB (!genB (αd c4))) ≤ B4) (fri : Nat → EF → EF → List (EF → EF) → V)
    (hncw : 4 ≤ ncw)
    (NR2 : Nat) (Rb : Nat → EF → EF → Nat → List (EF → EF)) (Ro : Nat → EF → EF → Nat → Wv)
    {NSl L KA sQ kQ nQ KQ NS2 NS3 n2 n3 : Nat} (hKA : 0 < KA) (hN : 0 < NSl) (hKL : KQ = KA ^ L)
    (hbl : ∀ k, bl k ≤ 26) (h20 : bl 2 = bl 0) (s20 : sh 2 = sh 0) (hs0 : sh 0 = 0)
    (hidx : ∀ c4, ∀ l ∈ idx c4, l < L) (hL : L = 2 ^ (bl 0 + 1))
    {h : List (List F) → Nat} {Mh : Nat} (hMh : 0 < Mh) (hnQ : L * (NSl * Mh) ≤ nQ) (hsQ : 1 ≤ sQ) (g : List (List (List F)) → List Nat → Pq)
    (nxt : Pq → Nat → List Nat → Nat) (d1 : List (List (List F)))
    (Com2 : List (List (List F)) → Nat → Nat) (Pf2 : Nat → List (List (List F)) → Nat → P2) (hc2 : ComHides NS2 Com2)
    (hp2 : ∀ c4, ComPfHides NS2 Com2 (Pf2 c4) (opF ((sudGroups tP ((friS bl sh idx 0) c4) ((friS bl sh idx 4) c4) ((friS bl sh idx 6) c4) EF.zero qv).map (·.base.S)) [1, 3, 5, 7]))
    (hr2 : ∀ d σ, Com2 d σ < n2) (d2 : List (List (List F)))
    (Com3 : List (List (List (List F))) × List (List (List F)) → Nat → Nat)
    (Pf3 : Nat → List (List (List (List F))) × List (List (List F)) → Nat → P3) (hc3 : ComHides NS3 Com3)
    (hp3 : ∀ c4, ComPfHides NS3 Com3 (Pf3 c4) (fun d => (opQ (sudSsT ((friS bl sh idx 0) c4) ((friS bl sh idx 4) c4) ((friS bl sh idx 6) c4)) d.1, opCw (sudSsC tP ((friS bl sh idx 0) c4) ((friS bl sh idx 4) c4) ((friS bl sh idx 6) c4)) d.2)))
    (hr3 : ∀ d σ, Com3 d σ < n3) (d3 : List (List (List (List F))) × List (List (List F)))
    (E : Nat → Nat → Nat → Nat → Nat → Nat → Nat → Option (Pq × List Nat) × Option (P2 × P3) × TViewN (SudPV (V × Wv)) EF → Bool) :
    let opS := fun (c4 : Nat) => opF ((sudGroups tP ((friS bl sh idx 0) c4) ((friS bl sh idx 4) c4) ((friS bl sh idx 6) c4) EF.zero qv).map (·.base.S)) [0, 2, 4, 6]
    let Com1 := comM KA NSl L (posRowsP (xsL bl sh) [0, 2, 4, 6] h NSl Mh)
    let Pf1 := fun (c4 : Nat) => pfM KA NSl L kQ (posRowsP (xsL bl sh) [0, 2, 4, 6] h NSl Mh) ((fun c4 l => decide (l ∈ idx c4)) c4) (opS c4) g nxt
    let Cmi := comMI KA NSl L L (posRowsP (xsL bl sh) [0, 2, 4, 6] h NSl Mh)
    let Pfi := fun (c4 : Nat) => pfMI KA NSl L L kQ (posRowsP (xsL bl sh) [0, 2, 4, 6] h NSl Mh) ((fun c4 l => decide (l ∈ idx c4)) c4) (opS c4) g nxt
    let blank := stmtMachine (fun _ => false) 729 (sudokuExpr (cluesOf puzzle)) ACC REJ
    let C := cpuTableW A row k (2 ^ 16)
    let Pg := progTableS blank.heap
    let Wt := witTableS A
    let Mm := memTableC A (cpuAirS blank.hd blank.stk blank.heap.length ACC) (progAirS blank.heap) witAirS C Pg Wt
    let NR0 := sudNR off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt tP ((friS bl sh idx 0) 0) ((friS bl sh idx 4) 0) ((friS bl sh idx 6) 0) EF.zero qv (wm 0) (wc 0) (ww 0) (wp 0) ncw
    let pcsZ := fun (c4 c2 : Nat) (ζ : EF) t α β r => sudPcs off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt tP ((friS bl sh idx 0) c4) ((friS bl sh idx 4) c4) ((friS bl sh idx 6) c4) ζ qv (wm c2) (wc c2) (ww c2) (wp c2) ncw (αd c4)
      (friX (fri c4) (Rb c4) (Ro c4) (r / NR0)) t α β (r % NR0)
    let psimZ := fun (c4 c2 : Nat) (ζ : EF) α β v r => sudPsim off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt tP ((friS bl sh idx 0) c4) ((friS bl sh idx 4) c4) ((friS bl sh idx 6) c4) ζ qv (wm c2) (wc c2) (ww c2) (wp c2) ncw (αd c4)
      (friX (fri c4) (Rb c4) (Ro c4) (r / NR0)) α β v (r % NR0)
    let NR := NR0 * NR2
    let tabs := fun t : Nat → Tup => sudTables blank.hd blank.stk blank.heap.length blank.heap
      ((C.setBlind BLA (t 1)).setBlind BLB (t 0)) (Mm.setBlind 5 (t 0)) (progTableS blank.heap) (Wt.setBlind 1 (t 1))
    let tv := fun pre β t => sudViewN pre β blank.hd blank.stk blank.heap.length C Mm Wt t
    let tp := fun pre β => terminal pre β (progAirS blank.heap) (progTableS blank.heap)
    let M := (allEntries (sudTables blank.hd blank.stk blank.heap.length blank.heap C Mm (progTableS blank.heap) Wt)).length
    let q0 := sudGroups tP ((friS bl sh idx 0) 0) ((friS bl sh idx 4) 0) ((friS bl sh idx 6) 0) EF.zero qv
    let qZ := fun (c4 : Nat) (ζ : EF) => sudGroups tP ((friS bl sh idx 0) c4) ((friS bl sh idx 4) c4) ((friS bl sh idx 6) c4) ζ qv
    let Ss := fun c4 => (qZ c4 EF.zero).map (·.base.S)
    let ks := sudKs blank.hd blank.stk blank.heap.length blank.heap
    let cols := sudCols off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt
    let tqZ := fun (c4 c2 : Nat) (ζ : EF) => (sudTs off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt tP ((friS bl sh idx 0) c4) ((friS bl sh idx 4) c4) ((friS bl sh idx 6) c4) ζ qv (wm c2) (wc c2) (ww c2) (wp c2)).map Prod.fst
    let qdZ := fun (c4 c2 : Nat) (ζ : EF) (t : Nat → Tup) (α β : EF) (ms : List F) =>
      (sudTs off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt tP ((friS bl sh idx 0) c4) ((friS bl sh idx 4) c4) ((friS bl sh idx 6) c4) ζ qv (wm c2) (wc c2) (ww c2) (wp c2)).map (fun p => p.2 t α β ms)
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
      sumTo (NSl ^ L * KA ^ nQ * KQ) (fun σ1 => sumTo (NS2 * NS3) (fun σ => sumTo NR (fun r => sumN 2 (fun t => g (σ1, σ, r, t)))))
    let smR := fun (g : Nat × Nat × Nat × (Nat → Tup) → Nat) =>
      sumTo (NSl ^ L * KA ^ nQ) (fun σ1 => sumTo (NS2 * NS3) (fun σ => sumTo NR (fun r => sumN 2 (fun t => g (σ1, σ, r, t)))))
    let m1 := fun (x : Nat × Nat × Nat × (Nat → Tup)) => Com1 (main1 x.2.2.2 x.2.2.1) x.1
    let m2 := fun (c1 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      m1 x + KQ * Com2 (main2 c1 x.2.2.2 x.2.2.1) (x.2.1 % NS2)
    let m3 := fun (c1 c2 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      m1 x + KQ * comPair NS2 n2 Com2 Com3 (main2 c1 x.2.2.2 x.2.2.1, main3 c1 c2 x.2.2.2 x.2.2.1) x.2.1
    let rvo := fun (c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      ((ov1 c4 (rvF c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)).map (fun _ => Pf1 c4 (main1 x.2.2.2 x.2.2.1) x.1),
       (ovPair (ov2 c4) (ov3 c4) (rvF c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)).map
         (fun _ => pfPair NS2 (Pf2 c4) (Pf3 c4) (main2 c1 x.2.2.2 x.2.2.1, main3 c1 c2 x.2.2.2 x.2.2.1) x.2.1),
       rvF c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)
    let s1 := fun (c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) => Cmi (sdF (Ss c4) mk1 (sop1 c4 c2 c3 x.2.2.1 x.2.2.2)) x.1
    let s2 := fun (c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      s1 c4 c1 c2 c3 x + KQ * Com2 (sdF (Ss c4) mk2 (sop2 c4 c2 c3 c1 x.2.2.1 x.2.2.2)) (x.2.1 % NS2)
    let s3 := fun (c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      s1 c4 c1 c2 c3 x + KQ * comPair NS2 n2 Com2 Com3
        (sdF (Ss c4) mk2 (sop2 c4 c2 c3 c1 x.2.2.1 x.2.2.2), sd3 c4 (sop3 c4 c2 c3 c1 x.2.2.1 x.2.2.2)) x.2.1
    let svo := fun (c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      (some (Pfi c4 (sdF (Ss c4) mk1 (sop1 c4 c2 c3 x.2.2.1 x.2.2.2)) x.1),
       some (pfPair NS2 (Pf2 c4) (Pf3 c4) (sdF (Ss c4) mk2 (sop2 c4 c2 c3 c1 x.2.2.1 x.2.2.2), sd3 c4 (sop3 c4 c2 c3 c1 x.2.2.1 x.2.2.2)) x.2.1),
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
          (rvo (rget K4 (Mq y) H4) (r1 y) (r2 y) (r3 y) y.2.2.2)))))) ≤
      sumTo (K4 ^ N4) (fun H4 => sumTo K4 (fun c4 =>
        sumTo ((Q4 * Q4) ^ KQ) (fun H1 => sumTo (K2 ^ (KQ * n2)) (fun H2 => sumTo (Q4 ^ (KQ * (n2 * n3))) (fun H3 =>
        sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo Q4 (fun c3 => sm (fun x =>
          indB (E (rset (Q4 * Q4) (s1 c4 c1 c2 c3 x) H1 c1) (rset K2 (s2 c4 c1 c2 c3 x) H2 c2)
            (rset Q4 (s3 c4 c1 c2 c3 x) H3 c3) (rset K4 (φ (s3 c4 c1 c2 c3 x) (ozF (svF c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2))) H4 c4)
            (s1 c4 c1 c2 c3 x) (s2 c4 c1 c2 c3 x) (s3 c4 c1 c2 c3 x) (svo c4 c1 c2 c3 x))))))))))) +
        K4 ^ N4 * (K4 * ((Q4 * Q4) ^ KQ * (K2 ^ (KQ * n2) * (Q4 ^ (KQ * (n2 * n3)) *
          (K2 * (Q4 * ((NSl ^ L * KA ^ nQ * KQ) * (NS2 * NS3 * (Q4 * (NR * (Q4 ^ 2 * M)) + Q4 * (Q4 * (Q4 ^ 2 * 0)))) +
            Q4 * Q4 * (NS2 * NS3 * (NR * (Q4 ^ 2 * (2 * (L * (L * (NSl ^ (L - 1) * sQ))) * (KA ^ nQ * KQ))))))) +
            (Q4 * (P * P) * (K2 * Q4) + Q4 * Q4 * (K2 * (P * P))) * ((NSl ^ L * KA ^ nQ * KQ) * (NS2 * NS3 * (NR * (Q4 ^ 2 * 1)))))))) +
            B4 * (Q4 * Q4 * (K2 * Q4) * sm4 (fun _ => 1))) +
      K4 * (Q4 * Q4 * (K2 * Q4) * (K4 ^ N4 * ((Q4 * Q4) ^ KQ * (K2 ^ (KQ * n2) * (Q4 ^ (KQ * (n2 * n3)) *
        (KQ * (L * (KA ^ nQ * (NSl ^ (L - 1) * (sQ * (kQ + L))))) * (NS2 * NS3 * (NR * (Q4 ^ 2 * 1))))))))) := by
  have htP26 : tP ≤ 26 := by
    rw [htp]; exact Nat.le_trans (sud_prog_height hc hA hlen).1 (by decide)
  subst hL
  exact sud_fs_open4ROMMC (kQ := kQ) (nQ := nQ) (sQ := sQ) off hc hA hacc hlen hk htp (friS bl sh idx 0) (friS bl sh idx 4) (friS bl sh idx 6)
    qv wm wc ww wp hlwm hlwc hlww hlwp hK2
    hK4 φ hφ (sud_fri_leaves (tP := tP) (qv := qv) (h := h) (NSl := NSl) (Mh := Mh) hbl h20 s20 hs0 htP26 hidx).1 (sud_fri_leaves (tP := tP) (qv := qv) (h := h) (NSl := NSl) (Mh := Mh) hbl h20 s20 hs0 htP26 hidx).2.1 (sud_fri_leaves (tP := tP) (qv := qv) (h := h) (NSl := NSl) (Mh := Mh) hbl h20 s20 hs0 htP26 hidx).2.2.1 hsz16 hsz hszP αd
    hB4 fri hncw NR2 Rb Ro hKA hN hKL (posRowsP (xsL bl sh) [0, 2, 4, 6] h NSl Mh)
    (fun d l a hl => Nat.lt_of_lt_of_le (posRowsP_lt (L := 2 ^ (bl 0 + 1)) hN hMh d l a hl)
      (Nat.le_trans (Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _)) hnQ)) g (fun d l v => Nat.le_trans (posRowsP_spread d l v) hsQ) nxt (fun c4 l => decide (l ∈ idx c4)) (fun c4 d d' e l a hl => by
      rw [posRowsP_of_posRows (Nat.two_pow_pos (bl 0 + 1)), posRowsP_of_posRows (Nat.two_pow_pos (bl 0 + 1)),
        (sud_fri_leaves (tP := tP) (qv := qv) (h := h) (NSl := NSl) (Mh := Mh) hbl h20 s20 hs0 htP26 hidx).2.2.2.1 c4 d d' e l a hl]) d1 Com2 Pf2
    hc2 hp2 hr2 d2 Com3 Pf3 hc3 hp3 hr3 d3
    E

end

end Circuit
