import Ski.ZK.FSQueryJA
import Ski.ZK.ROMInstMC

/-!
# The proof with jets over Merkle leaves that may share a hash

`comp_fs_open4ROMMC` for the circuit with jets (`compJ_fs_open4ROMMC`): the
first commitment Merkle leaves under the random oracle, which may share a
hash, entering through `compJ_fs_open4A` (`rom4_transferMC`,
`pfMIP_hidesA`).  One direction.
-/

set_option autoImplicit false
namespace Circuit

open ZKF B Air JetTable Compose CompM Stmt Mach Wit

set_option maxRecDepth 100000 in
/-- **`comp_fs_open4ROMMC` with jets**: the first commitment Merkle leaves
    that may share a hash, its hiding up to the salt vectors where leaves
    meet; one direction. -/
theorem compJ_fs_open4ROMMC {V Wv Pq P2 P3 : Type} (off : EF → String → EF) {R Lm Lp Li : Nat} (hR : R ≤ 20)
    (hLm : Lm ≤ 20) (hLp : Lp ≤ 20) (hLi : Li ≤ 20)
    {shp : BT} {Ps : List Term} {W : Nat} {roots : List (Nat × Nat)} {jets : List Air.Jet}
    (hprov : 0 < (rootsRowsCJ roots).length ∧ 0 < (hdrRowsCJ jets).length ∧ 0 < (tmplRowsCJ jets).length)
    (hprov24 : (rootsRowsCJ roots).length ≤ 2 ^ 24 ∧ (hdrRowsCJ jets).length ≤ 2 ^ 24 ∧
      (tmplRowsCJ jets).length ≤ 2 ^ 24)
    {ρ : Nat → Bool} {region : List Cell} (hrl : region.length = W)
    (hr : ∀ i c, region[i]? = some c → cellOK (BT.nleaves shp + 3 + i) c = true)
    (hroots : RootsOK (cMachine ρ shp region Ps).heap roots jets)
    {A : List Cell} {e : Nat → Nat} {row : Nat → Air.Row}
    (hA : AcceptsCJ A (cMachine ρ shp region Ps) roots jets (cHeap ρ shp region Ps).2
      (cHeap ρ shp region Ps).1.length Ps.length e row)
    (hlen : A.length = 2 ^ Lm) (hK : e (Ps.length - 1) < 2 ^ R)
    (hHP : (JRun.popRows ⟨A, roots, jets, e (Ps.length - 1) + 1, row, isRestart e Ps.length⟩ (2 ^ R)).length ≤
      2 ^ Lp)
    (hHW : (JRun.instwRows ⟨A, roots, jets, e (Ps.length - 1) + 1, row, isRestart e Ps.length⟩ (2 ^ R)).length ≤
      2 ^ Li)
    (hNW : BT.nleaves shp + W ≤ 2 ^ 8)
    {tbM tbC tbPo tbI tpT tpH tpR tpP tpS : Nat} (htM : tbM + 1 = Lm) (htC : tbC + 1 = R)
    (htPo : tbPo + 1 = Lp) (htI : tbI + 1 = Li)
    (htT : tpT = provTpCJ (tmplRowsCJ jets)) (htH : tpH = provTpCJ (hdrRowsCJ jets))
    (htR : tpR = provTpCJ (rootsRowsCJ roots))
    (htP : tpP = progTpC (blankM shp W Ps).heap (BT.nleaves shp) W) (htS : tpS = segTp (blankRoots shp W Ps))
    (SM SC S9 SPo SI ST SH SR SP SS : Nat → List F) (qv : EF → EF → List EF → F → List F → List F → List EF)
    (wm wc ww wpo wi wt wh wr wp wsg : Nat → List (EF → EF → List F))
    {Lwm Lwc Lww Lwpo Lwi Lwt Lwh Lwr Lwp Lwsg : Nat} (hlwm : ∀ c, (wm c).length = Lwm)
    (hlwc : ∀ c, (wc c).length = Lwc) (hlww : ∀ c, (ww c).length = Lww) (hlwpo : ∀ c, (wpo c).length = Lwpo)
    (hlwi : ∀ c, (wi c).length = Lwi) (hlwt : ∀ c, (wt c).length = Lwt) (hlwh : ∀ c, (wh c).length = Lwh)
    (hlwr : ∀ c, (wr c).length = Lwr) (hlwp : ∀ c, (wp c).length = Lwp) (hlwsg : ∀ c, (wsg c).length = Lwsg)
    {K2 K4 : Nat} (hK2 : 0 < K2) (hK4 : 0 < K4)
    (φ : Nat → Option (List (List (List EF)) × List (List (List (List EF))) × List (List (List EF))) → Nat) {N4 : Nat}
    (hφ : ∀ m w, φ m w < N4)
    (hSM : ∀ c4, ∀ x ∈ SM c4, x ∉ cosetL 1 (bbGen (tbM + 1)) (2 ^ (tbM + 1)))
    (hSC : ∀ c4, ∀ x ∈ SC c4, x ∉ cosetL 1 (bbGen (tbC + 1)) (2 ^ (tbC + 1)))
    (hS9 : ∀ c4, ∀ x ∈ S9 c4, x ∉ cosetL 1 (bbGen 9) (2 ^ 9))
    (hSPo : ∀ c4, ∀ x ∈ SPo c4, x ∉ cosetL 1 (bbGen (tbPo + 1)) (2 ^ (tbPo + 1)))
    (hSI : ∀ c4, ∀ x ∈ SI c4, x ∉ cosetL 1 (bbGen (tbI + 1)) (2 ^ (tbI + 1)))
    (hST : ∀ c4, ∀ x ∈ ST c4, x ∉ cosetL 1 (bbGen (tpT + 1)) (2 ^ (tpT + 1)))
    (hSH : ∀ c4, ∀ x ∈ SH c4, x ∉ cosetL 1 (bbGen (tpH + 1)) (2 ^ (tpH + 1)))
    (hSR : ∀ c4, ∀ x ∈ SR c4, x ∉ cosetL 1 (bbGen (tpR + 1)) (2 ^ (tpR + 1)))
    (hSP : ∀ c4, ∀ x ∈ SP c4, x ∉ cosetL 1 (bbGen (tpP + 1)) (2 ^ (tpP + 1)))
    (hSS : ∀ c4, ∀ x ∈ SS c4, x ∉ cosetL 1 (bbGen (tpS + 1)) (2 ^ (tpS + 1)))
    (hszM : ∀ c4, 2 * (SM c4).length + 8 ≤ 2 ^ (tbM + 1)) (hszC : ∀ c4, 2 * (SC c4).length + 8 ≤ 2 ^ (tbC + 1))
    (hsz9 : ∀ c4, 2 * (S9 c4).length + 8 ≤ 2 ^ 9) (hszPo : ∀ c4, 2 * (SPo c4).length + 8 ≤ 2 ^ (tbPo + 1))
    (hszI : ∀ c4, 2 * (SI c4).length + 8 ≤ 2 ^ (tbI + 1)) (hszT : ∀ c4, 2 * (ST c4).length + 8 ≤ 2 ^ (tpT + 1))
    (hszH : ∀ c4, 2 * (SH c4).length + 8 ≤ 2 ^ (tpH + 1)) (hszR : ∀ c4, 2 * (SR c4).length + 8 ≤ 2 ^ (tpR + 1))
    (hszP : ∀ c4, 2 * (SP c4).length + 8 ≤ 2 ^ (tpP + 1))
    (hszS : ∀ c4, 2 * (SS c4).length + 8 ≤ 2 ^ (tpS + 1)) {ncw : Nat} (αd : Nat → EF) {B4 : Nat}
    (hB4 : sumTo K4 (fun c4 => indB (!genB (αd c4))) ≤ B4) (fri : Nat → EF → EF → List (EF → EF) → V) (hncw : 4 ≤ ncw)
    (NR2 : Nat) (Rb : Nat → EF → EF → Nat → List (EF → EF)) (Ro : Nat → EF → EF → Nat → Wv)
    {NSl L KA sQ kQ nQ KQ NS2 NS3 n2 n3 : Nat} (hKA : 0 < KA) (hN : 0 < NSl) (hKL : KQ = KA ^ L)
    (pos : List (List (List F)) → Nat → Nat → Nat)
    (hlt : ∀ d l a, l < L → pos d l a < nQ) (g : List (List (List F)) → List Nat → Pq)
    (hs : ∀ d l v, sumTo NSl (fun x => indB (decide (pos d l x = v))) ≤ sQ)
    (nxt : Pq → Nat → List Nat → Nat) (isOf : Nat → Nat → Bool)
    (hposO : ∀ c4 d d', opF ((jGroups tbM tbC tbPo tbI tpT tpH tpR tpP tpS (SM c4) (SC c4) (S9 c4) (SPo c4) (SI c4) (ST c4) (SH c4) (SR c4) (SP c4) (SS c4) EF.zero qv).map (·.base.S)) [0, 2, 4, 6, 8, 10, 12, 14, 16, 18] d = opF ((jGroups tbM tbC tbPo tbI tpT tpH tpR tpP tpS (SM c4) (SC c4) (S9 c4) (SPo c4) (SI c4) (ST c4) (SH c4) (SR c4) (SP c4) (SS c4) EF.zero qv).map (·.base.S)) [0, 2, 4, 6, 8, 10, 12, 14, 16, 18] d' →
      ∀ l a, isOf c4 l = true → pos d l a = pos d' l a) (d1 : List (List (List F)))
    (Com2 : List (List (List F)) → Nat → Nat) (Pf2 : Nat → List (List (List F)) → Nat → P2) (hc2 : ComHides NS2 Com2)
    (hp2 : ∀ c4, ComPfHides NS2 Com2 (Pf2 c4) (opF ((jGroups tbM tbC tbPo tbI tpT tpH tpR tpP tpS (SM c4) (SC c4) (S9 c4) (SPo c4) (SI c4) (ST c4) (SH c4) (SR c4) (SP c4) (SS c4) EF.zero qv).map (·.base.S)) [1, 3, 5, 7, 9, 11, 13, 15, 17, 19]))
    (hr2 : ∀ d σ, Com2 d σ < n2) (d2 : List (List (List F)))
    (Com3 : List (List (List (List F))) × List (List (List F)) → Nat → Nat)
    (Pf3 : Nat → List (List (List (List F))) × List (List (List F)) → Nat → P3) (hc3 : ComHides NS3 Com3)
    (hp3 : ∀ c4, ComPfHides NS3 Com3 (Pf3 c4) (fun d => (opQ (jSsT (SM c4) (SC c4) (S9 c4) (SPo c4) (SI c4) (ST c4) (SH c4) (SR c4) (SP c4) (SS c4)) d.1, opCw (jSsC tbM tbC tbPo tbI tpT tpH tpR tpP tpS (SM c4) (SC c4) (S9 c4) (SPo c4) (SI c4) (ST c4) (SH c4) (SR c4) (SP c4) (SS c4)) d.2)))
    (hr3 : ∀ d σ, Com3 d σ < n3) (d3 : List (List (List (List F))) × List (List (List F)))
    (E : Nat → Nat → Nat → Nat → Nat → Nat → Nat → Option (Pq × List Nat) × Option (P2 × P3) × TViewN (PcsPV (V × Wv)) (EF × EF) → Bool) :
    let opS := fun (c4 : Nat) => opF ((jGroups tbM tbC tbPo tbI tpT tpH tpR tpP tpS (SM c4) (SC c4) (S9 c4) (SPo c4) (SI c4) (ST c4) (SH c4) (SR c4) (SP c4) (SS c4) EF.zero qv).map (·.base.S)) [0, 2, 4, 6, 8, 10, 12, 14, 16, 18]
    let Com1 := comM KA NSl L pos
    let Pf1 := fun (c4 : Nat) => pfM KA NSl L kQ pos (isOf c4) (opS c4) g nxt
    let Cmi := comMI KA NSl L L pos
    let Pfi := fun (c4 : Nat) => pfMI KA NSl L L kQ pos (isOf c4) (opS c4) g nxt
    let m := blankM shp W Ps
    let segRoots := blankRoots shp W Ps
    let N := BT.nleaves shp
    let Rn : CRun := ⟨A, roots, jets, segRoots, e, Ps.length, row⟩
    let C := Rn.cpuTableCJ (2 ^ R)
    let Pg := progTableC m.heap N W
    let Wt := witTable A N W
    let Po := Rn.J.popTable (2 ^ R) (2 ^ Lp)
    let Iw := Rn.J.instwTable (2 ^ R) (2 ^ Li)
    let Mm := memTable5 A (cpuAirCJ m.hd m.stk m.heap.length Ps.length m.stk) (progAirC m.heap N W) popAirCJ
      instwAirCJ (witAir N W) C Pg Po Iw Wt
    let Rt := provTableCJ (rootsRowsCJ roots) (Rn.J.cntRoots (2 ^ R))
    let Hd := provTableCJ (hdrRowsCJ jets) (Rn.J.cntHdr (2 ^ R))
    let Tm := provTableCJ (tmplRowsCJ jets) (Rn.J.cntTmpl (2 ^ R))
    let NR0 := jNR off m.hd m.stk m.heap.length Ps.length m.stk m.heap N W segRoots roots jets C Mm Wt Rt Hd Tm Po Iw tbM tbC tbPo tbI tpT tpH tpR tpP tpS (SM 0) (SC 0) (S9 0) (SPo 0) (SI 0) (ST 0) (SH 0) (SR 0) (SP 0) (SS 0) EF.zero qv (wm 0) (wc 0) (ww 0) (wpo 0) (wi 0) (wt 0) (wh 0) (wr 0) (wp 0) (wsg 0) ncw
    let pcsZ := fun (c4 c2 : Nat) (ζ : EF) t α β r => jPcs off m.hd m.stk m.heap.length Ps.length m.stk m.heap N W segRoots roots jets C Mm Wt Rt Hd Tm Po Iw tbM tbC tbPo tbI tpT tpH tpR tpP tpS (SM c4) (SC c4) (S9 c4) (SPo c4) (SI c4) (ST c4) (SH c4) (SR c4) (SP c4) (SS c4) ζ qv (wm c2) (wc c2) (ww c2) (wpo c2) (wi c2) (wt c2) (wh c2) (wr c2) (wp c2) (wsg c2) ncw (αd c4)
      (friX (fri c4) (Rb c4) (Ro c4) (r / NR0)) t α β (r % NR0)
    let psimZ := fun (c4 c2 : Nat) (ζ : EF) α β v r => jPsim off m.hd m.stk m.heap.length Ps.length m.stk m.heap N W segRoots roots jets C Mm Wt Rt Hd Tm Po Iw tbM tbC tbPo tbI tpT tpH tpR tpP tpS (SM c4) (SC c4) (S9 c4) (SPo c4) (SI c4) (ST c4) (SH c4) (SR c4) (SP c4) (SS c4) ζ qv (wm c2) (wc c2) (ww c2) (wpo c2) (wi c2) (wt c2) (wh c2) (wr c2) (wp c2) (wsg c2) ncw (αd c4)
      (friX (fri c4) (Rb c4) (Ro c4) (r / NR0)) α β v (r % NR0)
    let NR := NR0 * NR2
    let tabs := fun t : Nat → Tup => compJTables m.hd m.stk m.heap.length Ps.length m.stk m.heap N W segRoots roots jets
      (((C.setBlind BLAJ (t 1)).setBlind BLBJ (t 0)).setBlind BLCJ (t 2)) (Mm.setBlind 5 (t 0))
      (progTableC m.heap N W) (Wt.setBlind WT_BLIND (t 1)) (segsPub segRoots) (Rt.setBlind 1 (t 6))
      ((Hd.setBlind 1 (t 5)).setBlind 6 (t 6)) ((Tm.setBlind 1 (t 4)).setBlind 6 (t 5))
      ((Po.setBlind popAir.width (t 2)).setBlind (popAir.width + 5) (t 3))
      ((Iw.setBlind instwAir.width (t 3)).setBlind (instwAir.width + 5) (t 4))
    let tv := fun pre β t => compJViewN pre β m.hd m.stk m.heap.length Ps.length m.stk N W roots jets C Mm Wt Rt Hd Tm Po Iw t
    let pb := fun pre β => (terminal pre β (progAirC m.heap N W) (progTableC m.heap N W),
      terminal pre β (segsAir segRoots) (segsPub segRoots))
    let ptm := fun pre β => (terminal pre β (progAirC m.heap N W) (progTableC m.heap N W)).add
      (terminal pre β (segsAir segRoots) (segsPub segRoots))
    let M := (allEntries (compJTables m.hd m.stk m.heap.length Ps.length m.stk m.heap N W segRoots roots jets C Mm
      (progTableC m.heap N W) Wt (segsPub segRoots) Rt Hd Tm Po Iw)).length
    let q0 := jGroups tbM tbC tbPo tbI tpT tpH tpR tpP tpS (SM 0) (SC 0) (S9 0) (SPo 0) (SI 0) (ST 0) (SH 0) (SR 0) (SP 0) (SS 0) EF.zero qv
    let qZ := fun (c4 : Nat) (ζ : EF) => jGroups tbM tbC tbPo tbI tpT tpH tpR tpP tpS (SM c4) (SC c4) (S9 c4) (SPo c4) (SI c4) (ST c4) (SH c4) (SR c4) (SP c4) (SS c4) ζ qv
    let Ss := fun c4 => (qZ c4 EF.zero).map (·.base.S)
    let ks := jKs m.hd m.stk m.heap.length Ps.length m.stk m.heap N W segRoots roots jets
    let cols := jCols off m.hd m.stk m.heap.length Ps.length m.stk m.heap N W segRoots roots jets C Mm Wt Rt Hd Tm Po Iw
    let tqZ := fun (c4 c2 : Nat) (ζ : EF) => (jTs off m.hd m.stk m.heap.length Ps.length m.stk m.heap N W segRoots roots jets C Mm Wt Rt Hd Tm Po Iw tbM tbC tbPo tbI tpT tpH tpR tpP tpS (SM c4) (SC c4) (S9 c4) (SPo c4) (SI c4) (ST c4) (SH c4) (SR c4) (SP c4) (SS c4) ζ qv (wm c2) (wc c2) (ww c2) (wpo c2) (wi c2) (wt c2) (wh c2) (wr c2) (wp c2) (wsg c2)).map Prod.fst
    let qdZ := fun (c4 c2 : Nat) (ζ : EF) (t : Nat → Tup) (α β : EF) (ms : List F) =>
      (jTs off m.hd m.stk m.heap.length Ps.length m.stk m.heap N W segRoots roots jets C Mm Wt Rt Hd Tm Po Iw tbM tbC tbPo tbI tpT tpH tpR tpP tpS (SM c4) (SC c4) (S9 c4) (SPo c4) (SI c4) (ST c4) (SH c4) (SR c4) (SP c4) (SS c4) ζ qv (wm c2) (wc c2) (ww c2) (wpo c2) (wi c2) (wt c2) (wh c2) (wr c2) (wp c2) (wsg c2)).map (fun p => p.2 t α β ms)
    let SsT := fun c4 => (tqZ c4 0 EF.zero).map (·.S)
    let SsC := fun c4 => (tabsInfo ncw (tqZ c4 0 EF.zero)).map (·.S)
    let mk1 := [0, 2, 4, 6, 8, 10, 12, 14, 16, 18]
    let mk2 := [1, 3, 5, 7, 9, 11, 13, 15, 17, 19]
    let main1 := fun (t : Nat → Tup) (r : Nat) => mainF2 q0 ks cols (tqZ 0 0 EF.zero) ncw mk1 t (r % NR0)
    let main2 := fun (c1 : Nat) (t : Nat → Tup) (r : Nat) =>
      mainP2 q0 ks cols (tqZ 0 0 EF.zero) ncw mk2 t (efOf (c1 / Q4)) (efOf (c1 % Q4)) (r % NR0)
    let main3 := fun (c1 c2 : Nat) (t : Nat → Tup) (r : Nat) =>
      (tabsPolys (tqZ 0 c2 EF.zero) (qdZ 0 c2 EF.zero t (efOf (c1 / Q4)) (efOf (c1 % Q4))
          (msF q0 ks (tqZ 0 c2 EF.zero) ncw (r % NR0))) (crF q0 ks (tqZ 0 c2 EF.zero) ncw (r % NR0)),
       tabsCws ncw (tqZ 0 c2 EF.zero) (ccF q0 ks (tqZ 0 c2 EF.zero) ncw (r % NR0)))
    let vS := fun (α β : EF) (t : Nat → Tup) => viewT β (fun k => prefixOf α (off β) (jetBus k)) jetSg
      jetPar 8 (xrefN (ptm (prefixOf α (off β)) β)) t
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
      | some (pv, _) => some (ovQ pv, cwQ 20 pv)
      | none => none
    let rvF := fun (c4 c2 c3 : Nat) (α β : EF) (r : Nat) (t : Nat → Tup) =>
      realVN off tabs tv pb (pcsZ c4 c2 (efOf c3)) α β r t
    let svF := fun (c4 c2 c3 : Nat) (α β : EF) (r : Nat) (t : Nat → Tup) =>
      simVN off pb jetBus jetSg jetPar 8 ptm (psimZ c4 c2 (efOf c3)) α β r t
    let ozF : TViewN (PcsPV (V × Wv)) (EF × EF) → Option (List (List (List EF)) × List (List (List (List EF))) × List (List (List EF))) := fun v => match v with
      | some (pv, _) => some (pv.1.1.map (fun g => g.1.map Prod.snd), pv.1.2.map (List.map (List.map Prod.snd)),
        pv.2.1.map (List.map Prod.snd))
      | none => none
    let op3 := fun (c4 : Nat) (d : List (List (List (List F))) × List (List (List F))) =>
      (opQ (SsT c4) d.1, opCw (SsC c4) d.2)
    let sd3 := fun (c4 : Nat) (o : List (List (List (List F))) × List (List (List F))) =>
      (sdQ (SsT c4) o.1, sdCw (SsC c4) o.2)
    let sm := fun (g : Nat × Nat × Nat × (Nat → Tup) → Nat) =>
      sumTo (NSl ^ L * KA ^ nQ * KQ) (fun σ1 => sumTo (NS2 * NS3) (fun σ => sumTo NR (fun r => sumN 7 (fun t => g (σ1, σ, r, t)))))
    let smR := fun (g : Nat × Nat × Nat × (Nat → Tup) → Nat) =>
      sumTo (NSl ^ L * KA ^ nQ) (fun σ1 => sumTo (NS2 * NS3) (fun σ => sumTo NR (fun r => sumN 7 (fun t => g (σ1, σ, r, t)))))
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
          (K2 * (Q4 * ((NSl ^ L * KA ^ nQ * KQ) * (NS2 * NS3 * (Q4 * (NR * (Q4 ^ 7 * M)) + Q4 * (Q4 * (Q4 ^ 7 * 0)))) +
            Q4 * Q4 * (NS2 * NS3 * (NR * (Q4 ^ 7 * (2 * (L * (L * (NSl ^ (L - 1) * sQ))) * (KA ^ nQ * KQ))))))) +
            (Q4 * (P * P) * (K2 * Q4) + Q4 * Q4 * (K2 * (P * P))) * ((NSl ^ L * KA ^ nQ * KQ) * (NS2 * NS3 * (NR * (Q4 ^ 7 * 1)))))))) +
            B4 * (Q4 * Q4 * (K2 * Q4) * sm4 (fun _ => 1))) +
      K4 * (Q4 * Q4 * (K2 * Q4) * (K4 ^ N4 * ((Q4 * Q4) ^ KQ * (K2 ^ (KQ * n2) * (Q4 ^ (KQ * (n2 * n3)) *
        (KQ * (L * (KA ^ nQ * (NSl ^ (L - 1) * (sQ * (kQ + L))))) * (NS2 * NS3 * (NR * (Q4 ^ 7 * 1))))))))) := by
  intro opS Com1 Pf1 Cmi Pfi m segRoots N Rn C Pg Wt Po Iw Mm Rt Hd Tm NR0 pcsZ psimZ NR tabs tv pb ptm M q0 qZ Ss ks cols tqZ qdZ SsT SsC mk1 mk2 main1 main2 main3 vS sop1 sop2 sop3 ov1 ov2 ov3 rvF svF ozF op3 sd3 sm smR m1 m2 m3 rvo s1 s2 s3 svo sm4 sm4R r1 r2 r3 Mq
  subst hKL
  have hc1 : ComHidesA (NSl ^ L * KA ^ nQ * KA ^ L) (2 * (L * (L * (NSl ^ (L - 1) * sQ))) * (KA ^ nQ * KA ^ L))
      (comMI KA NSl L L pos) := fun d d' E =>
    pfMIP_hidesA (k := 0) (O := Unit) (P := Unit) hKA pos (collB pos L NSl) (fun _ _ h => collB_dist h)
      (fun dd => collB_count hN pos hs dd) hlt (fun _ => false) (fun _ => ())
      (fun _ _ _ _ _ h => absurd h Bool.false_ne_true) (fun _ _ => ()) (fun _ _ _ => 0) d d' rfl (fun c _ => E c)
  have hp1 := fun c4 => pfMIP_hidesA (NSl := NSl) (k := kQ) hKA pos (collB pos L NSl) (fun _ _ h => collB_dist h)
    (fun dd => collB_count hN pos hs dd) hlt (isOf c4) (opS c4) (hposO c4) g nxt
  have hr1 : ∀ d σ, comMI KA NSl L L pos d σ < KA ^ L := fun d σ => by
    have h := rgetL_lt hKA (posAll pos L NSl d (σ / KA ^ L % NSl ^ L)) (σ / KA ^ L / NSl ^ L)
    rwa [posAll_length] at h
  have fo := (compJ_fs_open4A off hR hLm hLp hLi hprov hprov24 hrl hr hroots hA hlen hK hHP hHW hNW htM htC htPo htI htT htH htR htP htS SM SC S9 SPo SI ST SH SR SP SS qv wm wc ww wpo wi wt wh wr wp wsg hlwm hlwc hlww hlwpo hlwi hlwt hlwh hlwr hlwp hlwsg hK2 hK4 φ hφ hSM hSC hS9 hSPo hSI hST hSH hSR hSP hSS hszM hszC hsz9 hszPo hszI hszT hszH hszR hszP hszS αd hB4 fri hncw NR2 Rb Ro Cmi Pfi hc1 hp1 hr1 d1 Com2 Pf2 hc2 hp2 hr2 d2 Com3 Pf3 hc3 hp3 hr3 d3 E)
  exact Nat.le_trans (rom4_transferMC (K3 := Q4) (m := 7) (NR := NR) (NSl := NSl) (L := L) (KA := KA) (s := sQ) (k := kQ) (n := nQ)
    (NS2 := NS2) (NS3 := NS3) (K2 := K2) (K4 := K4) (N4 := N4) (n2 := n2) (n3 := n3) hKA hN rfl φ rvF ozF pos hlt g hs nxt opS isOf ov1 main1
    Com2 Pf2 ov2 main2 Com3 Pf3 ov3 main3 E) (Nat.add_le_add_right fo _)

end Circuit
