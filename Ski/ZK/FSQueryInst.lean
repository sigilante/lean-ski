import Ski.ZK.FSQuery

/-!
# The hidden-term and composed proofs with the query points hashed

`sud_fs_open4`'s construction for the other two circuits (`wit_fs_open4`,
`comp_fs_open4`).  Scope as in `Ski/ZK/FSQuery.lean`.
-/

namespace Circuit

open ZKF B Air Compose CompM Stmt Mach Wit

set_option maxRecDepth 100000 in
theorem wit_data_q (off : EF → String → EF) (hd0 stk0 ctr0 : Nat) (heap : List Cell) (W : Nat) (C Mm Wt : Table) (tp : Nat)
    (S10 S9 SP S10' S9' SP' : List F) (ζ ζ' : EF) (qv : EF → EF → List EF → F → List F → List F → List EF)
    (wm wc ww wp : List (EF → EF → List F)) (t : Nat → Tup) (α β : EF) (ms : List F)
    (h : Aborts (prefixOf α (off β)) β (wTabs hd0 stk0 ctr0 heap W C Mm Wt t) = false) :
    (wTs off hd0 stk0 ctr0 heap W C Mm Wt tp S10 S9 SP ζ qv wm wc ww wp).map (fun p => p.2 t α β ms) =
      (wTs off hd0 stk0 ctr0 heap W C Mm Wt tp S10' S9' SP' ζ' qv wm wc ww wp).map (fun p => p.2 t α β ms) := by
  have hg : ∀ tss rs, mpolysMulti ((wGroups tp S10 S9 SP ζ qv).map QGroup.ext) tss rs =
      mpolysMulti ((wGroups tp S10' S9' SP' ζ' qv).map QGroup.ext) tss rs := fun tss rs =>
    mpolysMulti_congr _ _ _ _ rfl
  simp only [wTs, bbData, List.map_cons, List.map_nil, h, if_true, hg]

set_option maxRecDepth 100000 in
/-- **The hidden-term PCS's data shape reads neither the query points, nor `ζ`,
    nor the weights beyond their lengths.** -/
theorem wit_same_d (off : EF → String → EF) (hd0 stk0 ctr0 : Nat) (heap : List Cell) (W : Nat) (C Mm Wt : Table) (tp : Nat)
    (S10 S9 SP S10' S9' SP' : List F) (ζ ζ' : EF) (qv : EF → EF → List EF → F → List F → List F → List EF)
    (wm wc ww wp wm' wc' ww' wp' : List (EF → EF → List F))
    (hwm : wm.length = wm'.length) (hwc : wc.length = wc'.length) (hww : ww.length = ww'.length) (hwp : wp.length = wp'.length) :
    SameData (wGroups tp S10 S9 SP ζ qv) (wGroups tp S10' S9' SP' ζ' qv)
      ((wTs off hd0 stk0 ctr0 heap W C Mm Wt tp S10 S9 SP ζ qv wm wc ww wp).map Prod.fst)
      ((wTs off hd0 stk0 ctr0 heap W C Mm Wt tp S10' S9' SP' ζ' qv wm' wc' ww' wp').map Prod.fst) where
  trn := rfl
  dom := rfl
  shape := by
    simp only [wTs, bbTab, airQTabG, tShape, List.map_cons, List.map_nil, List.length_map]
    rw [hwm, hwc, hww, hwp]

set_option maxRecDepth 100000 in
/-- **The hidden-term proof over four Fiat–Shamir rounds, the query points
    hashed**: `wit_fs_open3` with the query points a fourth challenge `c4`,
    drawn from a fourth table at a function `φ` of the commitments'
    transcript and the openings at `ζ`, which do not read the query points
    (`pcsFri_ood`, `pcsFri_oodT`, `pcsFri_oodC`); `φ` may carry a proof-of-work nonce ground
    against a table of its own, independent of the query table (`fs_pow`).
    The points are decoded by
    `S10 S9 SP` (`fs_open4`, `fs_open4R`).  The opening proofs (`Pf`, the
    Merkle paths at the drawn indices) and FRI's openings and randomness
    (`fri`, `Rb`, `Ro`) read `c4`; the committed data do not
    (`wit_same_d`, `wit_data_q`).  Assumed at every `c4`: the decoding
    admissible (off the trace domains, few enough points), and each
    commitment hiding given its openings and opening proof there.  Both
    ways, both counts unguarded, the non-generic `β` and `ζ` in the bound.
    Assumed besides `wit_fs_open3`'s: the fourth table's input is the
    commitments' transcript and every opening at `ζ` (the trace groups',
    the quotient chunks' and the codewords'), without FRI's layer
    commitments or its final polynomial.  The FRI challenge is hashed
    too, decoded from `c4` by `αd`; the draws where it fails the verifier's
    test, at most `B4` of the `K4`, enter the bound as their whole count;
    Plonky3 samples it before FRI's layers, from the openings at `ζ`
    (decoded uniformly, `P²` in every `Q4`: `genB_count_mod`).
    FRI's folding challenges are read from `c4` through `Rb`, as one draw
    with the query points, not each hashed after its layer. -/
theorem wit_fs_open4 {V Wv P1 P2 P3 : Type} (off : EF → String → EF) {Vt x : Term} {W : Nat} {ws : List Cell} (hwf : WF ws)
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
    (Com1 : List (List (List F)) → Nat → Nat) (Pf1 : Nat → List (List (List F)) → Nat → P1) (hc1 : ComHides NS1 Com1)
    (hp1 : ∀ c4, ComPfHides NS1 Com1 (Pf1 c4) (opF ((wGroups tP (S10 c4) (S9 c4) (SP c4) EF.zero qv).map (·.base.S)) [0, 2, 4, 6]))
    (hr1 : ∀ d σ, Com1 d σ < n1) (d1 : List (List (List F)))
    (Com2 : List (List (List F)) → Nat → Nat) (Pf2 : Nat → List (List (List F)) → Nat → P2) (hc2 : ComHides NS2 Com2)
    (hp2 : ∀ c4, ComPfHides NS2 Com2 (Pf2 c4) (opF ((wGroups tP (S10 c4) (S9 c4) (SP c4) EF.zero qv).map (·.base.S)) [1, 3, 5, 7]))
    (hr2 : ∀ d σ, Com2 d σ < n2) (d2 : List (List (List F)))
    (Com3 : List (List (List (List F))) × List (List (List F)) → Nat → Nat)
    (Pf3 : Nat → List (List (List (List F))) × List (List (List F)) → Nat → P3) (hc3 : ComHides NS3 Com3)
    (hp3 : ∀ c4, ComPfHides NS3 Com3 (Pf3 c4) (fun d => (opQ (wSsT (S10 c4) (S9 c4) (SP c4)) d.1, opCw (wSsC tP (S10 c4) (S9 c4) (SP c4)) d.2)))
    (hr3 : ∀ d σ, Com3 d σ < n3) (d3 : List (List (List (List F))) × List (List (List F)))
    (E : Nat → Nat → Nat → Nat → Nat → Nat → Nat → Option P1 × Option (P2 × P3) × TViewN (PcsPV (V × Wv)) EF → Bool) :
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
    (K4 * (Q4 * Q4 * (K2 * Q4) * sumTo (K4 ^ N4) (fun H4 => sm4 (fun y =>
        indB (E y.1 y.2.1 y.2.2.1 H4 (m1 y.2.2.2) (m2 (r1 y) y.2.2.2) (m3 (r1 y) (r2 y) y.2.2.2)
          (rvo (rget K4 (Mq y) H4) (r1 y) (r2 y) (r3 y) y.2.2.2))))) ≤
      sumTo (K4 ^ N4) (fun H4 => sumTo K4 (fun c4 =>
        sumTo ((Q4 * Q4) ^ n1) (fun H1 => sumTo (K2 ^ (n1 * n2)) (fun H2 => sumTo (Q4 ^ (n1 * (n2 * n3))) (fun H3 =>
        sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo Q4 (fun c3 => sm (fun x =>
          indB (E (rset (Q4 * Q4) (s1 c4 c1 c2 c3 x) H1 c1) (rset K2 (s2 c4 c1 c2 c3 x) H2 c2)
            (rset Q4 (s3 c4 c1 c2 c3 x) H3 c3) (rset K4 (φ (s3 c4 c1 c2 c3 x) (ozF (svF c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2))) H4 c4)
            (s1 c4 c1 c2 c3 x) (s2 c4 c1 c2 c3 x) (s3 c4 c1 c2 c3 x) (svo c4 c1 c2 c3 x))))))))))) +
        K4 ^ N4 * (K4 * ((Q4 * Q4) ^ n1 * (K2 ^ (n1 * n2) * (Q4 ^ (n1 * (n2 * n3)) *
          (K2 * (Q4 * (NS1 * (NS2 * NS3 * (Q4 * (NR * (Q4 ^ 2 * M)) + Q4 * (Q4 * (Q4 ^ 2 * 0)))))) +
            (Q4 * (P * P) * (K2 * Q4) + Q4 * Q4 * (K2 * (P * P))) * (NS1 * (NS2 * NS3 * (NR * (Q4 ^ 2 * 1)))))))) +
            B4 * (Q4 * Q4 * (K2 * Q4) * sm4 (fun _ => 1)))) ∧
    (sumTo (K4 ^ N4) (fun H4 => sumTo K4 (fun c4 =>
        sumTo ((Q4 * Q4) ^ n1) (fun H1 => sumTo (K2 ^ (n1 * n2)) (fun H2 => sumTo (Q4 ^ (n1 * (n2 * n3))) (fun H3 =>
        sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo Q4 (fun c3 => sm (fun x =>
          indB (E (rset (Q4 * Q4) (s1 c4 c1 c2 c3 x) H1 c1) (rset K2 (s2 c4 c1 c2 c3 x) H2 c2)
            (rset Q4 (s3 c4 c1 c2 c3 x) H3 c3) (rset K4 (φ (s3 c4 c1 c2 c3 x) (ozF (svF c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2))) H4 c4)
            (s1 c4 c1 c2 c3 x) (s2 c4 c1 c2 c3 x) (s3 c4 c1 c2 c3 x) (svo c4 c1 c2 c3 x))))))))))) ≤
        K4 * (Q4 * Q4 * (K2 * Q4) * sumTo (K4 ^ N4) (fun H4 => sm4 (fun y =>
        indB (E y.1 y.2.1 y.2.2.1 H4 (m1 y.2.2.2) (m2 (r1 y) y.2.2.2) (m3 (r1 y) (r2 y) y.2.2.2)
          (rvo (rget K4 (Mq y) H4) (r1 y) (r2 y) (r3 y) y.2.2.2))))) +
        K4 ^ N4 * (K4 * ((Q4 * Q4) ^ n1 * (K2 ^ (n1 * n2) * (Q4 ^ (n1 * (n2 * n3)) *
          (K2 * (Q4 * (NS1 * (NS2 * NS3 * (Q4 * (NR * (Q4 ^ 2 * M)) + Q4 * (Q4 * (Q4 ^ 2 * 0)))))) +
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
  exact ⟨fs_open4 hK2 Q4_pos hK4 φ hφ rvF svF (fun c2 c3 => genB (efOf c3)) hgz (fun c4 => genB (αd c4)) hB4
    (fun c4 c2 c3 α β r t => realVN_cases _ _ _ _ _ α β r t) (fun c4 c2 c3 α β r t => simVN_some _ _ _ _ _ _ _ _ α β r t)
    ozF hoz (fun c4 c2 c3 hg4 hg => (hb c4 c2 c3 hg4 hg).1) (fun c4 c2 c3 hg4 hg => (hb c4 c2 c3 hg4 hg).2)
    Com1 Pf1 (fun c4 => opF (Ss c4) mk1) (fun c4 => sdF (Ss c4) mk1) d1 hc1 hp1 hr1 ov1 (fun _ => rfl) main1 hsd1
    Com2 Pf2 (fun c4 => opF (Ss c4) mk2) (fun c4 => sdF (Ss c4) mk2) d2 hc2 hp2 hr2 ov2 (fun _ => rfl) main2 hsd2
    Com3 Pf3 op3 sd3 d3 hc3 hp3' hr3 ov3 (fun _ => rfl) main3 hsd3 hvo1 hvo2 hvo3 sop1 sop2 sop3 hsvo1 hsvo2 hsvo3 E,
    fs_open4R hK2 Q4_pos hK4 φ hφ rvF svF (fun c2 c3 => genB (efOf c3)) hgz (fun c4 => genB (αd c4)) hB4
    (fun c4 c2 c3 α β r t => realVN_cases _ _ _ _ _ α β r t) (fun c4 c2 c3 α β r t => simVN_some _ _ _ _ _ _ _ _ α β r t)
    ozF hoz (fun c4 c2 c3 hg4 hg => (hb c4 c2 c3 hg4 hg).1) (fun c4 c2 c3 hg4 hg => (hb c4 c2 c3 hg4 hg).2)
    Com1 Pf1 (fun c4 => opF (Ss c4) mk1) (fun c4 => sdF (Ss c4) mk1) d1 hc1 hp1 hr1 ov1 (fun _ => rfl) main1 hsd1
    Com2 Pf2 (fun c4 => opF (Ss c4) mk2) (fun c4 => sdF (Ss c4) mk2) d2 hc2 hp2 hr2 ov2 (fun _ => rfl) main2 hsd2
    Com3 Pf3 op3 sd3 d3 hc3 hp3' hr3 ov3 (fun _ => rfl) main3 hsd3 hvo1 hvo2 hvo3 sop1 sop2 sop3 hsvo1 hsvo2 hsvo3 E⟩


set_option maxRecDepth 100000 in
theorem comp_data_q (off : EF → String → EF) (hd0 stk0 ctr0 n nilA : Nat) (heap : List Cell) (N W : Nat) (roots : List Nat)
    (C Mm Wt : Table) (tbM tbC tpP tpS : Nat) (SM SC S9 SP SS SM' SC' S9' SP' SS' : List F) (ζ ζ' : EF) (qv : EF → EF → List EF → F → List F → List F → List EF)
    (wm wc ww wp wsg : List (EF → EF → List F)) (t : Nat → Tup) (α β : EF) (ms : List F)
    (h : Aborts (prefixOf α (off β)) β (cTabs hd0 stk0 ctr0 n nilA heap N W roots C Mm Wt t) = false) :
    (cTs off hd0 stk0 ctr0 n nilA heap N W roots C Mm Wt tbM tbC tpP tpS SM SC S9 SP SS ζ qv wm wc ww wp wsg).map (fun p => p.2 t α β ms) =
      (cTs off hd0 stk0 ctr0 n nilA heap N W roots C Mm Wt tbM tbC tpP tpS SM' SC' S9' SP' SS' ζ' qv wm wc ww wp wsg).map (fun p => p.2 t α β ms) := by
  have hg : ∀ tss rs, mpolysMulti ((cGroups tbM tbC tpP tpS SM SC S9 SP SS ζ qv).map QGroup.ext) tss rs =
      mpolysMulti ((cGroups tbM tbC tpP tpS SM' SC' S9' SP' SS' ζ' qv).map QGroup.ext) tss rs := fun tss rs =>
    mpolysMulti_congr _ _ _ _ rfl
  simp only [cTs, bbData, List.map_cons, List.map_nil, h, if_true, hg]

set_option maxRecDepth 100000 in
/-- **The composed PCS's data shape reads neither the query points, nor `ζ`,
    nor the weights beyond their lengths.** -/
theorem comp_same_d (off : EF → String → EF) (hd0 stk0 ctr0 n nilA : Nat) (heap : List Cell) (N W : Nat) (roots : List Nat)
    (C Mm Wt : Table) (tbM tbC tpP tpS : Nat) (SM SC S9 SP SS SM' SC' S9' SP' SS' : List F) (ζ ζ' : EF) (qv : EF → EF → List EF → F → List F → List F → List EF)
    (wm wc ww wp wsg wm' wc' ww' wp' wsg' : List (EF → EF → List F))
    (hwm : wm.length = wm'.length) (hwc : wc.length = wc'.length) (hww : ww.length = ww'.length) (hwp : wp.length = wp'.length) (hwsg : wsg.length = wsg'.length) :
    SameData (cGroups tbM tbC tpP tpS SM SC S9 SP SS ζ qv) (cGroups tbM tbC tpP tpS SM' SC' S9' SP' SS' ζ' qv)
      ((cTs off hd0 stk0 ctr0 n nilA heap N W roots C Mm Wt tbM tbC tpP tpS SM SC S9 SP SS ζ qv wm wc ww wp wsg).map Prod.fst)
      ((cTs off hd0 stk0 ctr0 n nilA heap N W roots C Mm Wt tbM tbC tpP tpS SM' SC' S9' SP' SS' ζ' qv wm' wc' ww' wp' wsg').map Prod.fst) where
  trn := rfl
  dom := rfl
  shape := by
    simp only [cTs, bbTab, airQTabG, tShape, List.map_cons, List.map_nil, List.length_map]
    rw [hwm, hwc, hww, hwp, hwsg]

set_option maxRecDepth 100000 in
/-- **The composed proof over four Fiat–Shamir rounds, the query points
    hashed**: `comp_fs_open3` with the query points a fourth challenge `c4`,
    drawn from a fourth table at a function `φ` of the commitments'
    transcript and the openings at `ζ`, which do not read the query points
    (`pcsFri_ood`, `pcsFri_oodT`, `pcsFri_oodC`); `φ` may carry a proof-of-work nonce ground
    against a table of its own, independent of the query table (`fs_pow`).
    The points are decoded by
    `SM SC S9 SP SS` (`fs_open4`, `fs_open4R`).  The opening proofs (`Pf`, the
    Merkle paths at the drawn indices) and FRI's openings and randomness
    (`fri`, `Rb`, `Ro`) read `c4`; the committed data do not
    (`comp_same_d`, `comp_data_q`).  Assumed at every `c4`: the decoding
    admissible (off the trace domains, few enough points), and each
    commitment hiding given its openings and opening proof there.  Both
    ways, both counts unguarded, the non-generic `β` and `ζ` in the bound.
    Assumed besides `comp_fs_open3`'s: the fourth table's input is the
    commitments' transcript and every opening at `ζ` (the trace groups',
    the quotient chunks' and the codewords'), without FRI's layer
    commitments or its final polynomial.  The FRI challenge is hashed
    too, decoded from `c4` by `αd`; the draws where it fails the verifier's
    test, at most `B4` of the `K4`, enter the bound as their whole count;
    Plonky3 samples it before FRI's layers, from the openings at `ζ`
    (decoded uniformly, `P²` in every `Q4`: `genB_count_mod`).
    FRI's folding challenges are read from `c4` through `Rb`, as one draw
    with the query points, not each hashed after its layer. -/
theorem comp_fs_open4 {V Wv P1 P2 P3 : Type} (off : EF → String → EF) {R Lm : Nat} (hR : R ≤ 20) {shp : BT} {Ps : List Term}
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
    (Com1 : List (List (List F)) → Nat → Nat) (Pf1 : Nat → List (List (List F)) → Nat → P1) (hc1 : ComHides NS1 Com1)
    (hp1 : ∀ c4, ComPfHides NS1 Com1 (Pf1 c4) (opF ((cGroups tbM tbC tpP tpS (SM c4) (SC c4) (S9 c4) (SP c4) (SS c4) EF.zero qv).map (·.base.S)) [0, 2, 4, 6, 8]))
    (hr1 : ∀ d σ, Com1 d σ < n1) (d1 : List (List (List F)))
    (Com2 : List (List (List F)) → Nat → Nat) (Pf2 : Nat → List (List (List F)) → Nat → P2) (hc2 : ComHides NS2 Com2)
    (hp2 : ∀ c4, ComPfHides NS2 Com2 (Pf2 c4) (opF ((cGroups tbM tbC tpP tpS (SM c4) (SC c4) (S9 c4) (SP c4) (SS c4) EF.zero qv).map (·.base.S)) [1, 3, 5, 7, 9]))
    (hr2 : ∀ d σ, Com2 d σ < n2) (d2 : List (List (List F)))
    (Com3 : List (List (List (List F))) × List (List (List F)) → Nat → Nat)
    (Pf3 : Nat → List (List (List (List F))) × List (List (List F)) → Nat → P3) (hc3 : ComHides NS3 Com3)
    (hp3 : ∀ c4, ComPfHides NS3 Com3 (Pf3 c4) (fun d => (opQ (cSsT (SM c4) (SC c4) (S9 c4) (SP c4) (SS c4)) d.1, opCw (cSsC tbM tbC tpP tpS (SM c4) (SC c4) (S9 c4) (SP c4) (SS c4)) d.2)))
    (hr3 : ∀ d σ, Com3 d σ < n3) (d3 : List (List (List (List F))) × List (List (List F)))
    (E : Nat → Nat → Nat → Nat → Nat → Nat → Nat → Option P1 × Option (P2 × P3) × TViewN (PcsPV (V × Wv)) (EF × EF) → Bool) :
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
    (K4 * (Q4 * Q4 * (K2 * Q4) * sumTo (K4 ^ N4) (fun H4 => sm4 (fun y =>
        indB (E y.1 y.2.1 y.2.2.1 H4 (m1 y.2.2.2) (m2 (r1 y) y.2.2.2) (m3 (r1 y) (r2 y) y.2.2.2)
          (rvo (rget K4 (Mq y) H4) (r1 y) (r2 y) (r3 y) y.2.2.2))))) ≤
      sumTo (K4 ^ N4) (fun H4 => sumTo K4 (fun c4 =>
        sumTo ((Q4 * Q4) ^ n1) (fun H1 => sumTo (K2 ^ (n1 * n2)) (fun H2 => sumTo (Q4 ^ (n1 * (n2 * n3))) (fun H3 =>
        sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo Q4 (fun c3 => sm (fun x =>
          indB (E (rset (Q4 * Q4) (s1 c4 c1 c2 c3 x) H1 c1) (rset K2 (s2 c4 c1 c2 c3 x) H2 c2)
            (rset Q4 (s3 c4 c1 c2 c3 x) H3 c3) (rset K4 (φ (s3 c4 c1 c2 c3 x) (ozF (svF c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2))) H4 c4)
            (s1 c4 c1 c2 c3 x) (s2 c4 c1 c2 c3 x) (s3 c4 c1 c2 c3 x) (svo c4 c1 c2 c3 x))))))))))) +
        K4 ^ N4 * (K4 * ((Q4 * Q4) ^ n1 * (K2 ^ (n1 * n2) * (Q4 ^ (n1 * (n2 * n3)) *
          (K2 * (Q4 * (NS1 * (NS2 * NS3 * (Q4 * (NR * (Q4 ^ 2 * M)) + Q4 * (Q4 * (Q4 ^ 2 * 0)))))) +
            (Q4 * (P * P) * (K2 * Q4) + Q4 * Q4 * (K2 * (P * P))) * (NS1 * (NS2 * NS3 * (NR * (Q4 ^ 2 * 1)))))))) +
            B4 * (Q4 * Q4 * (K2 * Q4) * sm4 (fun _ => 1)))) ∧
    (sumTo (K4 ^ N4) (fun H4 => sumTo K4 (fun c4 =>
        sumTo ((Q4 * Q4) ^ n1) (fun H1 => sumTo (K2 ^ (n1 * n2)) (fun H2 => sumTo (Q4 ^ (n1 * (n2 * n3))) (fun H3 =>
        sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo Q4 (fun c3 => sm (fun x =>
          indB (E (rset (Q4 * Q4) (s1 c4 c1 c2 c3 x) H1 c1) (rset K2 (s2 c4 c1 c2 c3 x) H2 c2)
            (rset Q4 (s3 c4 c1 c2 c3 x) H3 c3) (rset K4 (φ (s3 c4 c1 c2 c3 x) (ozF (svF c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2))) H4 c4)
            (s1 c4 c1 c2 c3 x) (s2 c4 c1 c2 c3 x) (s3 c4 c1 c2 c3 x) (svo c4 c1 c2 c3 x))))))))))) ≤
        K4 * (Q4 * Q4 * (K2 * Q4) * sumTo (K4 ^ N4) (fun H4 => sm4 (fun y =>
        indB (E y.1 y.2.1 y.2.2.1 H4 (m1 y.2.2.2) (m2 (r1 y) y.2.2.2) (m3 (r1 y) (r2 y) y.2.2.2)
          (rvo (rget K4 (Mq y) H4) (r1 y) (r2 y) (r3 y) y.2.2.2))))) +
        K4 ^ N4 * (K4 * ((Q4 * Q4) ^ n1 * (K2 ^ (n1 * n2) * (Q4 ^ (n1 * (n2 * n3)) *
          (K2 * (Q4 * (NS1 * (NS2 * NS3 * (Q4 * (NR * (Q4 ^ 2 * M)) + Q4 * (Q4 * (Q4 ^ 2 * 0)))))) +
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
  exact ⟨fs_open4 hK2 Q4_pos hK4 φ hφ rvF svF (fun c2 c3 => genB (efOf c3)) hgz (fun c4 => genB (αd c4)) hB4
    (fun c4 c2 c3 α β r t => realVN_cases _ _ _ _ _ α β r t) (fun c4 c2 c3 α β r t => simVN_some _ _ _ _ _ _ _ _ α β r t)
    ozF hoz (fun c4 c2 c3 hg4 hg => (hb c4 c2 c3 hg4 hg).1) (fun c4 c2 c3 hg4 hg => (hb c4 c2 c3 hg4 hg).2)
    Com1 Pf1 (fun c4 => opF (Ss c4) mk1) (fun c4 => sdF (Ss c4) mk1) d1 hc1 hp1 hr1 ov1 (fun _ => rfl) main1 hsd1
    Com2 Pf2 (fun c4 => opF (Ss c4) mk2) (fun c4 => sdF (Ss c4) mk2) d2 hc2 hp2 hr2 ov2 (fun _ => rfl) main2 hsd2
    Com3 Pf3 op3 sd3 d3 hc3 hp3' hr3 ov3 (fun _ => rfl) main3 hsd3 hvo1 hvo2 hvo3 sop1 sop2 sop3 hsvo1 hsvo2 hsvo3 E,
    fs_open4R hK2 Q4_pos hK4 φ hφ rvF svF (fun c2 c3 => genB (efOf c3)) hgz (fun c4 => genB (αd c4)) hB4
    (fun c4 c2 c3 α β r t => realVN_cases _ _ _ _ _ α β r t) (fun c4 c2 c3 α β r t => simVN_some _ _ _ _ _ _ _ _ α β r t)
    ozF hoz (fun c4 c2 c3 hg4 hg => (hb c4 c2 c3 hg4 hg).1) (fun c4 c2 c3 hg4 hg => (hb c4 c2 c3 hg4 hg).2)
    Com1 Pf1 (fun c4 => opF (Ss c4) mk1) (fun c4 => sdF (Ss c4) mk1) d1 hc1 hp1 hr1 ov1 (fun _ => rfl) main1 hsd1
    Com2 Pf2 (fun c4 => opF (Ss c4) mk2) (fun c4 => sdF (Ss c4) mk2) d2 hc2 hp2 hr2 ov2 (fun _ => rfl) main2 hsd2
    Com3 Pf3 op3 sd3 d3 hc3 hp3' hr3 ov3 (fun _ => rfl) main3 hsd3 hvo1 hvo2 hvo3 sop1 sop2 sop3 hsvo1 hsvo2 hsvo3 E⟩


end Circuit
