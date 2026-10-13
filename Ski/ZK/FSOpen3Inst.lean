import Ski.ZK.FSOpen3
import Ski.ZK.FSOpen2Inst2

/-!
# The hidden-term and composed proofs over three Fiat–Shamir rounds, every commitment opened

`sud_fs_open3`'s construction for the other two circuits (`wit_fs_open3`,
`comp_fs_open3`).  Scope as in `Ski/ZK/FSOpen3.lean`.
-/

namespace Circuit

open ZKF B Air Compose CompM Stmt Mach Wit

set_option maxRecDepth 100000 in
/-- **The hidden-term PCS's shape reads neither `ζ` nor the weights**, only
    their lengths. -/
theorem wit_same_w (off : EF → String → EF) (hd0 stk0 ctr0 : Nat) (heap : List Cell) (W : Nat) (C Mm Wt : Table) (tp : Nat)
    (S10 S9 SP : List F) (ζ ζ' : EF) (qv : EF → EF → List EF → F → List F → List F → List EF)
    (wm wc ww wp wm' wc' ww' wp' : List (EF → EF → List F)) (ncw : Nat)
    (hwm : wm.length = wm'.length) (hwc : wc.length = wc'.length) (hww : ww.length = ww'.length) (hwp : wp.length = wp'.length) :
    SameShape (wGroups tp S10 S9 SP ζ qv) (wGroups tp S10 S9 SP ζ' qv) (wKs hd0 stk0 ctr0 heap W)
      ((wTs off hd0 stk0 ctr0 heap W C Mm Wt tp S10 S9 SP ζ qv wm wc ww wp).map Prod.fst)
      ((wTs off hd0 stk0 ctr0 heap W C Mm Wt tp S10 S9 SP ζ' qv wm' wc' ww' wp').map Prod.fst) ncw where
  trn := rfl
  dom := rfl
  S := rfl
  shape := by
    simp only [wTs, bbTab, airQTabG, tShape, List.map_cons, List.map_nil, List.length_map]
    rw [hwm, hwc, hww, hwp]
  tS := by simp only [wTs, bbTab, airQTabG, List.map_cons, List.map_nil]
  iS := by simp only [wTs, bbTab, airQTabG, tabsInfo, tInfo, List.map_cons, List.map_nil, List.map_append,
    List.map_replicate]

set_option maxRecDepth 100000 in
/-- **The hidden-term proof over three Fiat–Shamir rounds, every commitment
    opened**, in the programmable random-oracle model: the LogUp
    challenges hashed from the main matrices' commitment, the
    constraint-folding challenge (which picks the quotient's weights) from
    the transcript with the permutation matrices' commitment, `ζ` from the
    transcript with the quotient chunks' commitment; each commitment
    opened beside the view; the simulator commits and opens interpolants
    through its own view's openings and programs all three tables
    (`fs_open3`).  Assumed: each commitment hides alone and given its
    openings at the real query points, perfectly, and is a primitive apart
    from the oracle; generic `β` and `ζ`; the weights a family of fixed
    lengths; the FRI challenge `αb` and the query points fixed
    parameters, unhashed; one proof per oracle. -/
theorem wit_fs_open3 {V Wv P1 P2 P3 : Type} (off : EF → String → EF) {Vt x : Term} {W : Nat} {ws : List Cell} (hwf : WF ws)
    (hwl : ws.length = W) (hW8 : W ≤ 2 ^ 8) {A : List Cell} {k : Nat} {row : Nat → Air.Row}
    (hA : AcceptsFrom A (wMachine ws (Vt ⬝ x)) k row)
    (hK : rd A (row (k - 1)).ctr (row (k - 1)).hd = some .K ∧ rd A (row (k - 1)).ctr (row (k - 1)).stk = some .nil)
    (hlen : A.length = 2 ^ 10) (hk : k ≤ 2 ^ 10)
    {tP : Nat} (htp : tP = progTpW (wMachine (List.replicate W .S) (Vt ⬝ x)).heap W)
    {S10 S9 SP : List F} (qv : EF → EF → List EF → F → List F → List F → List EF)
    (wm wc ww wp : Nat → List (EF → EF → List F)) {Lwm Lwc Lww Lwp : Nat} (hlwm : ∀ c, (wm c).length = Lwm)
    (hlwc : ∀ c, (wc c).length = Lwc) (hlww : ∀ c, (ww c).length = Lww) (hlwp : ∀ c, (wp c).length = Lwp)
    {K2 : Nat} (hK2 : 0 < K2)
    (hS10 : ∀ x ∈ S10, x ∉ cosetL 1 (bbGen 10) (2 ^ 10)) (hS9 : ∀ x ∈ S9, x ∉ cosetL 1 (bbGen 9) (2 ^ 9))
    (hSP : ∀ x ∈ SP, x ∉ cosetL 1 (bbGen (tP + 1)) (2 ^ (tP + 1)))
    (hsz10 : 2 * S10.length + 8 ≤ 2 ^ 10) (hsz9 : 2 * S9.length + 8 ≤ 2 ^ 9)
    (hszP : 2 * SP.length + 8 ≤ 2 ^ (tP + 1)) {ncw : Nat} {αb : EF} (fri : EF → EF → List (EF → EF) → V) (hncw : 4 ≤ ncw) (hgα : Generic αb)
    (NR2 : Nat) (Rb : EF → EF → Nat → List (EF → EF)) (Ro : EF → EF → Nat → Wv)
    {NS1 NS2 NS3 n1 n2 n3 : Nat}
    (Com1 : List (List (List F)) → Nat → Nat) (Pf1 : List (List (List F)) → Nat → P1) (hc1 : ComHides NS1 Com1)
    (hp1 : ComPfHides NS1 Com1 Pf1 (opF ((wGroups tP S10 S9 SP EF.zero qv).map (·.base.S)) [0, 2, 4, 6]))
    (hr1 : ∀ d σ, Com1 d σ < n1) (d1 : List (List (List F)))
    (Com2 : List (List (List F)) → Nat → Nat) (Pf2 : List (List (List F)) → Nat → P2) (hc2 : ComHides NS2 Com2)
    (hp2 : ComPfHides NS2 Com2 Pf2 (opF ((wGroups tP S10 S9 SP EF.zero qv).map (·.base.S)) [1, 3, 5, 7]))
    (hr2 : ∀ d σ, Com2 d σ < n2) (d2 : List (List (List F)))
    (Com3 : List (List (List (List F))) × List (List (List F)) → Nat → Nat)
    (Pf3 : List (List (List (List F))) × List (List (List F)) → Nat → P3) (hc3 : ComHides NS3 Com3)
    (hp3 : ComPfHides NS3 Com3 Pf3 (fun d => (opQ (wSsT S10 S9 SP) d.1, opCw (wSsC tP S10 S9 SP) d.2)))
    (hr3 : ∀ d σ, Com3 d σ < n3) (d3 : List (List (List (List F))) × List (List (List F)))
    (E : Nat → Nat → Nat → Nat → Nat → Nat → Option P1 × Option (P2 × P3) × TViewN (PcsPV (V × Wv)) EF → Bool) :
    let blank := wMachine (List.replicate W .S) (Vt ⬝ x)
    let C := cpuTableW A row k (2 ^ 10)
    let Pg := progTableW blank.heap W
    let Wt := witTableG 0 A 0 W
    let Mm := memTableC A (cpuAirW blank.hd blank.stk blank.heap.length) (progAirW blank.heap W) (witAirW W) C Pg Wt
    let NR0 := wNR off blank.hd blank.stk blank.heap.length blank.heap W C Mm Wt tP S10 S9 SP EF.zero qv (wm 0) (wc 0) (ww 0) (wp 0) ncw
    let pcsZ := fun (c2 : Nat) (ζ : EF) t α β r => wPcs off blank.hd blank.stk blank.heap.length blank.heap W C Mm Wt tP S10 S9 SP ζ qv (wm c2) (wc c2) (ww c2) (wp c2) ncw αb
      (friX fri Rb Ro (r / NR0)) t α β (r % NR0)
    let psimZ := fun (c2 : Nat) (ζ : EF) α β v r => wPsim off blank.hd blank.stk blank.heap.length blank.heap W C Mm Wt tP S10 S9 SP ζ qv (wm c2) (wc c2) (ww c2) (wp c2) ncw αb
      (friX fri Rb Ro (r / NR0)) α β v (r % NR0)
    let NR := NR0 * NR2
    let tabs := fun t : Nat → Tup => witTables blank.hd blank.stk blank.heap.length blank.heap W
      ((C.setBlind BLA (t 1)).setBlind BLB (t 0)) (Mm.setBlind 5 (t 0)) (progTableW blank.heap W)
      (Wt.setBlind WT_BLIND (t 1))
    let tv := fun pre β t => witViewN pre β blank.hd blank.stk blank.heap.length W C Mm Wt t
    let ptm := fun pre β => terminal pre β (progAirW blank.heap W) (progTableW blank.heap W)
    let M := (allEntries (witTables blank.hd blank.stk blank.heap.length blank.heap W C Mm (progTableW blank.heap W)
      Wt)).length
    let q0 := wGroups tP S10 S9 SP EF.zero qv
    let Ss0 := q0.map (·.base.S)
    let ks := wKs blank.hd blank.stk blank.heap.length blank.heap W
    let cols := wCols off blank.hd blank.stk blank.heap.length blank.heap W C Mm Wt
    let tqZ := fun (c2 : Nat) (ζ : EF) => (wTs off blank.hd blank.stk blank.heap.length blank.heap W C Mm Wt tP S10 S9 SP ζ qv (wm c2) (wc c2) (ww c2) (wp c2)).map Prod.fst
    let qdZ := fun (c2 : Nat) (ζ : EF) (t : Nat → Tup) (α β : EF) (ms : List F) =>
      (wTs off blank.hd blank.stk blank.heap.length blank.heap W C Mm Wt tP S10 S9 SP ζ qv (wm c2) (wc c2) (ww c2) (wp c2)).map (fun p => p.2 t α β ms)
    let SsT0 := (tqZ 0 EF.zero).map (·.S)
    let SsC0 := (tabsInfo ncw (tqZ 0 EF.zero)).map (·.S)
    let mk1 := [0, 2, 4, 6]
    let mk2 := [1, 3, 5, 7]
    let main1 := fun (t : Nat → Tup) (r : Nat) => mainF2 q0 ks cols (tqZ 0 EF.zero) ncw mk1 t (r % NR0)
    let main2 := fun (c1 : Nat) (t : Nat → Tup) (r : Nat) =>
      mainP2 q0 ks cols (tqZ 0 EF.zero) ncw mk2 t (efOf (c1 / Q4)) (efOf (c1 % Q4)) (r % NR0)
    let main3 := fun (c1 c2 : Nat) (t : Nat → Tup) (r : Nat) =>
      (tabsPolys (tqZ c2 EF.zero) (qdZ c2 EF.zero t (efOf (c1 / Q4)) (efOf (c1 % Q4))
          (msF q0 ks (tqZ c2 EF.zero) ncw (r % NR0))) (crF q0 ks (tqZ c2 EF.zero) ncw (r % NR0)),
       tabsCws ncw (tqZ c2 EF.zero) (ccF q0 ks (tqZ c2 EF.zero) ncw (r % NR0)))
    let vS := fun (α β : EF) (t : Nat → Tup) => viewT β (fun k => prefixOf α (off β) (chainBus k)) (fun _ => false)
      chainPar 3 (xrefN (ptm (prefixOf α (off β)) β)) t
    let qZ := fun (ζ : EF) => wGroups tP S10 S9 SP ζ qv
    let sop1 := fun (c2 c3 r : Nat) (_ : Nat → Tup) =>
      opF Ss0 mk1 (mainZ2 (qZ (efOf c3)) ks (tqZ c2 (efOf c3)) ncw mk1 (r % NR0))
    let sop2 := fun (c2 c3 _ r : Nat) (_ : Nat → Tup) =>
      opF Ss0 mk2 (mainZ2 (qZ (efOf c3)) ks (tqZ c2 (efOf c3)) ncw mk2 (r % NR0))
    let sop3 := fun (c2 c3 c1 r : Nat) (t : Nat → Tup) =>
      (opQ SsT0 (tabsPolys (tqZ c2 (efOf c3)) (canonT (tqZ c2 (efOf c3)) (efOf (c1 / Q4)) (efOf (c1 % Q4))
         (vS (efOf (c1 / Q4)) (efOf (c1 % Q4)) t)
         (openMulti ((qZ (efOf c3)).map QGroup.ext) ((((qZ (efOf c3)).map QGroup.ext).zip ks).map
           (fun p => List.replicate p.2 (List.replicate p.1.n (0 : F)))) (msF (qZ (efOf c3)) ks (tqZ c2 (efOf c3)) ncw (r % NR0))))
         (crF (qZ (efOf c3)) ks (tqZ c2 (efOf c3)) ncw (r % NR0))),
       opCw SsC0 (tabsCws ncw (tqZ c2 (efOf c3)) (ccF (qZ (efOf c3)) ks (tqZ c2 (efOf c3)) ncw (r % NR0))))
    let ov1 : TViewN (PcsPV (V × Wv)) EF → Option (List (List (List F))) := fun v => match v with
      | some (pv, _) => some (ovF2 Ss0 mk1 pv)
      | none => none
    let ov2 : TViewN (PcsPV (V × Wv)) EF → Option (List (List (List F))) := fun v => match v with
      | some (pv, _) => some (ovF2 Ss0 mk2 pv)
      | none => none
    let ov3 : TViewN (PcsPV (V × Wv)) EF → Option (List (List (List (List F))) × List (List (List F))) := fun v =>
      match v with
      | some (pv, _) => some (ovQ pv, cwQ 8 pv)
      | none => none
    let rvF := fun (c2 c3 : Nat) (α β : EF) (r : Nat) (t : Nat → Tup) => realVN off tabs tv ptm (pcsZ c2 (efOf c3)) α β r t
    let svF := fun (c2 c3 : Nat) (α β : EF) (r : Nat) (t : Nat → Tup) =>
      simVN off ptm chainBus (fun _ => false) chainPar 3 ptm (psimZ c2 (efOf c3)) α β r t
    let op3 := fun (d : List (List (List (List F))) × List (List (List F))) => (opQ SsT0 d.1, opCw SsC0 d.2)
    let sd3 := fun (o : List (List (List (List F))) × List (List (List F))) => (sdQ SsT0 o.1, sdCw SsC0 o.2)
    let sm := fun (g : Nat × Nat × Nat × (Nat → Tup) → Nat) =>
      sumTo NS1 (fun σ1 => sumTo (NS2 * NS3) (fun σ => sumTo NR (fun r => sumN 2 (fun t => g (σ1, σ, r, t)))))
    let m1 := fun (x : Nat × Nat × Nat × (Nat → Tup)) => Com1 (main1 x.2.2.2 x.2.2.1) x.1
    let m2 := fun (c1 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      m1 x + n1 * Com2 (main2 c1 x.2.2.2 x.2.2.1) (x.2.1 % NS2)
    let m3 := fun (c1 c2 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      m1 x + n1 * comPair NS2 n2 Com2 Com3 (main2 c1 x.2.2.2 x.2.2.1, main3 c1 c2 x.2.2.2 x.2.2.1) x.2.1
    let rvo := fun (c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      ((ov1 (rvF c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)).map (fun _ => Pf1 (main1 x.2.2.2 x.2.2.1) x.1),
       (ovPair ov2 ov3 (rvF c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)).map
         (fun _ => pfPair NS2 Pf2 Pf3 (main2 c1 x.2.2.2 x.2.2.1, main3 c1 c2 x.2.2.2 x.2.2.1) x.2.1),
       rvF c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)
    let s1 := fun (c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) => Com1 ((sdF Ss0 mk1) (sop1 c2 c3 x.2.2.1 x.2.2.2)) x.1
    let s2 := fun (c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      s1 c1 c2 c3 x + n1 * Com2 ((sdF Ss0 mk2) (sop2 c2 c3 c1 x.2.2.1 x.2.2.2)) (x.2.1 % NS2)
    let s3 := fun (c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      s1 c1 c2 c3 x + n1 * comPair NS2 n2 Com2 Com3
        ((sdF Ss0 mk2) (sop2 c2 c3 c1 x.2.2.1 x.2.2.2), sd3 (sop3 c2 c3 c1 x.2.2.1 x.2.2.2)) x.2.1
    let svo := fun (c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      (some (Pf1 ((sdF Ss0 mk1) (sop1 c2 c3 x.2.2.1 x.2.2.2)) x.1),
       some (pfPair NS2 Pf2 Pf3 ((sdF Ss0 mk2) (sop2 c2 c3 c1 x.2.2.1 x.2.2.2), sd3 (sop3 c2 c3 c1 x.2.2.1 x.2.2.2)) x.2.1),
       svF c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)
    let gd := fun (c1 c2 c3 : Nat) => genB (efOf (c1 % Q4)) && genB (efOf c3)
    (Q4 * Q4) * (K2 * (Q4 * sumTo ((Q4 * Q4) ^ n1) (fun H1 => sumTo (K2 ^ (n1 * n2)) (fun H2 =>
      sumTo (Q4 ^ (n1 * (n2 * n3))) (fun H3 => sm (fun x =>
      indB (gd (rget (Q4 * Q4) (m1 x) H1) (rget K2 (m2 (rget (Q4 * Q4) (m1 x) H1) x) H2)
          (rget Q4 (m3 (rget (Q4 * Q4) (m1 x) H1) (rget K2 (m2 (rget (Q4 * Q4) (m1 x) H1) x) H2) x) H3) &&
        E H1 H2 H3 (m1 x) (m2 (rget (Q4 * Q4) (m1 x) H1) x)
          (m3 (rget (Q4 * Q4) (m1 x) H1) (rget K2 (m2 (rget (Q4 * Q4) (m1 x) H1) x) H2) x)
          (rvo (rget (Q4 * Q4) (m1 x) H1) (rget K2 (m2 (rget (Q4 * Q4) (m1 x) H1) x) H2)
            (rget Q4 (m3 (rget (Q4 * Q4) (m1 x) H1) (rget K2 (m2 (rget (Q4 * Q4) (m1 x) H1) x) H2) x) H3) x)))))))) ≤
    sumTo ((Q4 * Q4) ^ n1) (fun H1 => sumTo (K2 ^ (n1 * n2)) (fun H2 => sumTo (Q4 ^ (n1 * (n2 * n3))) (fun H3 =>
      sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo Q4 (fun c3 => sm (fun x =>
        indB (gd c1 c2 c3 && E (rset (Q4 * Q4) (s1 c1 c2 c3 x) H1 c1) (rset K2 (s2 c1 c2 c3 x) H2 c2)
          (rset Q4 (s3 c1 c2 c3 x) H3 c3) (s1 c1 c2 c3 x) (s2 c1 c2 c3 x) (s3 c1 c2 c3 x) (svo c1 c2 c3 x))))))))) +
      (Q4 * Q4) ^ n1 * (K2 ^ (n1 * n2) * (Q4 ^ (n1 * (n2 * n3)) *
        (K2 * (Q4 * (NS1 * (NS2 * NS3 * ((Q4 * (NR * (Q4 ^ 2 * M)) + Q4 * (Q4 * (Q4 ^ 2 * 0)))))))))) := by
  intro blank C Pg Wt Mm NR0 pcsZ psimZ NR tabs tv ptm M q0 Ss0 ks cols tqZ qdZ SsT0 SsC0 mk1 mk2 main1 main2 main3 vS qZ sop1 sop2 sop3 ov1 ov2 ov3 rvF svF op3 sd3
  obtain ⟨hbal, hun⟩ := wit_honest_zk hwf hwl hW8 hA hlen hk
  obtain ⟨sc, sms, sw, hWh⟩ := wit_run_sats hwf hwl hW8 hA hK hlen hk
  obtain ⟨_, hP23, hPg⟩ := wit_prog_height hwl hA hlen
  rw [← htp] at hP23 hPg
  have hSw := fun (c2 c3 : Nat) => wit_same_w off blank.hd blank.stk blank.heap.length blank.heap W C Mm Wt tP S10 S9 SP (efOf c3) EF.zero qv (wm c2) (wc c2) (ww c2) (wp c2) (wm 0) (wc 0) (ww 0) (wp 0) ncw (by rw [hlwm, hlwm]) (by rw [hlwc, hlwc]) (by rw [hlww, hlww]) (by rw [hlwp, hlwp])
  have hSz := fun (c2 c3 : Nat) => wit_same_w off blank.hd blank.stk blank.heap.length blank.heap W C Mm Wt tP S10 S9 SP (efOf c3) EF.zero qv (wm c2) (wc c2) (ww c2) (wp c2) (wm c2) (wc c2) (ww c2) (wp c2) ncw rfl rfl rfl rfl
  have hS0 := fun (c2 : Nat) => wit_same_w off blank.hd blank.stk blank.heap.length blank.heap W C Mm Wt tP S10 S9 SP EF.zero EF.zero qv (wm c2) (wc c2) (ww c2) (wp c2) (wm 0) (wc 0) (ww 0) (wp 0) ncw (by rw [hlwm, hlwm]) (by rw [hlwc, hlwc]) (by rw [hlww, hlww]) (by rw [hlwp, hlwp])
  have hb : ∀ c2 c3, genB (efOf c3) = true →
      (∀ E' : TViewN (PcsPV (V × Wv)) EF → Bool,
        tsumN NR 2 (fun α β r t => indB (genB β && E' (rvF c2 c3 α β r t))) ≤
          tsumN NR 2 (fun α β r t => indB (genB β && E' (svF c2 c3 α β r t))) + Q4 * (NR * (Q4 ^ 2 * M)) +
            Q4 * (Q4 * (Q4 ^ 2 * 0))) ∧
      (∀ E' : TViewN (PcsPV (V × Wv)) EF → Bool,
        tsumN NR 2 (fun α β r t => indB (genB β && E' (svF c2 c3 α β r t))) ≤
          tsumN NR 2 (fun α β r t => indB (genB β && E' (rvF c2 c3 α β r t))) + Q4 * (NR * (Q4 ^ 2 * M)) +
            Q4 * (Q4 * (Q4 ^ 2 * 0))) := fun c2 c3 hg => by
    have hgz := (genB_iff _).1 hg
    have hpcs := wit_pcsX (heap := blank.heap) (ζ := efOf c3) off sc sms sw (rfl : C.h = 2 ^ 10) hlen hWh (by omega) hPg qv
      (wm c2) (wc c2) (ww c2) (wp c2) hS10 hS9 hSP hsz10 hsz9 hszP (generic_ofF_ne hgz) (mz_generic hgz) fri (mz_generic hgα) (generic_apow_ne hgα) hncw NR2 Rb Ro
    have hNR : wNR off blank.hd blank.stk blank.heap.length blank.heap W C Mm Wt tP S10 S9 SP (efOf c3) qv (wm c2) (wc c2) (ww c2) (wp c2) ncw = wNR off blank.hd blank.stk blank.heap.length blank.heap W C Mm Wt tP S10 S9 SP EF.zero qv (wm 0) (wc 0) (ww 0) (wp 0) ncw := by
      unfold wNR; rw [(hSw c2 c3).n1, (hSw c2 c3).n2]
    rw [hNR] at hpcs
    exact ⟨fun E' => (wit_transcriptG off NR 0 (pcsZ c2 (efOf c3)) (psimZ c2 (efOf c3)) hbal hun hpcs E').1,
      fun E' => (wit_transcriptG off NR 0 (pcsZ c2 (efOf c3)) (psimZ c2 (efOf c3)) hbal hun hpcs E').2⟩
  have hlen8 : ∀ (ζ : EF) t α β, (cols t α β).map List.length = (cols t EF.zero EF.zero).map List.length :=
    fun ζ t α β => by
      rw [(wCols_shaped off blank.hd blank.stk blank.heap.length (rfl : C.h = 2 ^ 10) hlen hWh hPg
          S10 S9 SP ζ qv t α β).2,
        (wCols_shaped off blank.hd blank.stk blank.heap.length (rfl : C.h = 2 ^ 10) hlen hWh hPg
          S10 S9 SP ζ qv t EF.zero EF.zero).2]
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
  have hvo1 : ∀ c2 c3 c r t, rvF c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t = none ∨
      ov1 (rvF c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (opF Ss0 mk1 (main1 t r)) := by
    intro c2 c3 c r t
    show realVN off tabs tv ptm (pcsZ c2 (efOf c3)) _ _ r t = none ∨
      ov1 (realVN off tabs tv ptm (pcsZ c2 (efOf c3)) _ _ r t) = _
    unfold realVN
    split
    · exact .inl rfl
    · have e := pcsFri_ov2 off (fun pre β t => witViewN pre β blank.hd blank.stk blank.heap.length W C Mm Wt t) (wGroups tP S10 S9 SP (efOf c3) qv) ks cols ((wTs off blank.hd blank.stk blank.heap.length blank.heap W C Mm Wt tP S10 S9 SP (efOf c3) qv (wm c2) (wc c2) (ww c2) (wp c2)).map Prod.fst) (fun t α β ms => (wTs off blank.hd blank.stk blank.heap.length blank.heap W C Mm Wt tP S10 S9 SP (efOf c3) qv (wm c2) (wc c2) (ww c2) (wp c2)).map fun p => p.2 t α β ms) ncw αb
        (friX fri Rb Ro (r / NR0)) mk1 hmk1 (hlen8 (efOf c3)) rfl t (efOf (c / Q4)) (efOf (c % Q4)) (r % NR0)
      rw [(hSw c2 c3).dataF2 cols mk1 t (r % NR0), (hSw c2 c3).S] at e
      exact .inr (congrArg some e)
  have hvo2 : ∀ c2 c3 c r t, rvF c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t = none ∨
      ov2 (rvF c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (opF Ss0 mk2 (main2 c t r)) := by
    intro c2 c3 c r t
    show realVN off tabs tv ptm (pcsZ c2 (efOf c3)) _ _ r t = none ∨
      ov2 (realVN off tabs tv ptm (pcsZ c2 (efOf c3)) _ _ r t) = _
    unfold realVN
    split
    · exact .inl rfl
    · have e := pcsFri_ovP off (fun pre β t => witViewN pre β blank.hd blank.stk blank.heap.length W C Mm Wt t) (wGroups tP S10 S9 SP (efOf c3) qv) ks cols ((wTs off blank.hd blank.stk blank.heap.length blank.heap W C Mm Wt tP S10 S9 SP (efOf c3) qv (wm c2) (wc c2) (ww c2) (wp c2)).map Prod.fst) (fun t α β ms => (wTs off blank.hd blank.stk blank.heap.length blank.heap W C Mm Wt tP S10 S9 SP (efOf c3) qv (wm c2) (wc c2) (ww c2) (wp c2)).map fun p => p.2 t α β ms) ncw αb
        (friX fri Rb Ro (r / NR0)) mk2 hmk2 rfl t (efOf (c / Q4)) (efOf (c % Q4)) (r % NR0)
      rw [(hSw c2 c3).dataP2 cols mk2 t _ _ (r % NR0), (hSw c2 c3).S] at e
      exact .inr (congrArg some e)
  have hvo3 : ∀ c2 c3 c r t, rvF c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t = none ∨
      ov3 (rvF c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (op3 (main3 c c2 t r)) := by
    intro c2 c3 c r t
    show realVN off tabs tv ptm (pcsZ c2 (efOf c3)) _ _ r t = none ∨
      ov3 (realVN off tabs tv ptm (pcsZ c2 (efOf c3)) _ _ r t) = _
    unfold realVN
    split
    · exact .inl rfl
    · rename_i hab
      have hab' : Aborts (prefixOf (efOf (c / Q4)) (off (efOf (c % Q4)))) (efOf (c % Q4)) (tabs t) = false := by
        cases h : Aborts (prefixOf (efOf (c / Q4)) (off (efOf (c % Q4)))) (efOf (c % Q4)) (tabs t)
        · rfl
        · exact absurd h hab
      have e0 := pcsFri_ovR2 off (fun pre β t => witViewN pre β blank.hd blank.stk blank.heap.length W C Mm Wt t) (wGroups tP S10 S9 SP (efOf c3) qv) ks cols ((wTs off blank.hd blank.stk blank.heap.length blank.heap W C Mm Wt tP S10 S9 SP (efOf c3) qv (wm c2) (wc c2) (ww c2) (wp c2)).map Prod.fst) (fun t α β ms => (wTs off blank.hd blank.stk blank.heap.length blank.heap W C Mm Wt tP S10 S9 SP (efOf c3) qv (wm c2) (wc c2) (ww c2) (wp c2)).map fun p => p.2 t α β ms) ncw αb
        (friX fri Rb Ro (r / NR0)) mk2 hmk2 rfl t (efOf (c / Q4)) (efOf (c % Q4)) (r % NR0)
      have e := congrArg Prod.snd e0
      rw [(hSz c2 c3).tS, (hSz c2 c3).iS, tabsPolys_congr _ _ _ _ (hSz c2 c3).shape,
        tabsCws_congr ncw _ _ _ (hSz c2 c3).shape, (hSz c2 c3).cr (r % NR0), (hSz c2 c3).cc (r % NR0),
        (hSz c2 c3).ms (r % NR0), (hS0 c2).tS, (hS0 c2).iS,
        wit_data_zeta off blank.hd blank.stk blank.heap.length blank.heap W C Mm Wt tP S10 S9 SP (efOf c3) EF.zero
          qv (wm c2) (wc c2) (ww c2) (wp c2) t _ _ _ hab'] at e
      exact .inr (congrArg some e)
  have hsvo1 : ∀ c2 c3 c r t, ov1 (svF c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (sop1 c2 c3 r t) :=
    fun c2 c3 c r t => congrArg some (psimFri_ov2 (qZ (efOf c3)) ks (tqZ c2 (efOf c3)) ncw αb _ mk1
      (fun k hk => (hmk1 k hk).1) rfl _ _ _ (r % NR0))
  have hsvo2 : ∀ c2 c3 c r t, ov2 (svF c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (sop2 c2 c3 c r t) :=
    fun c2 c3 c r t => congrArg some (psimFri_ov2 (qZ (efOf c3)) ks (tqZ c2 (efOf c3)) ncw αb _ mk2
      (fun k hk => (hmk2 k hk).1) rfl _ _ _ (r % NR0))
  have hsvo3 : ∀ c2 c3 c r t, ov3 (svF c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (sop3 c2 c3 c r t) := by
    intro c2 c3 c r t
    have e0 := psimFri_ovR2 (wGroups tP S10 S9 SP (efOf c3) qv) ks ((wTs off blank.hd blank.stk blank.heap.length blank.heap W C Mm Wt tP S10 S9 SP (efOf c3) qv (wm c2) (wc c2) (ww c2) (wp c2)).map Prod.fst) ncw αb (friX fri Rb Ro (r / NR0)) mk2
      (fun k hk => (hmk2 k hk).1) rfl (efOf (c / Q4)) (efOf (c % Q4)) (vS (efOf (c / Q4)) (efOf (c % Q4)) t) (r % NR0)
    have e := congrArg Prod.snd e0
    rw [(hSw c2 c3).tS, (hSw c2 c3).iS] at e
    exact congrArg some e
  have hsd1 : ∀ t r, opF Ss0 mk1 (sdF Ss0 mk1 (opF Ss0 mk1 (main1 t r))) = opF Ss0 mk1 (main1 t r) :=
    fun t r => opF_sdF _ _ _
  have hsd2 : ∀ c t r, opF Ss0 mk2 (sdF Ss0 mk2 (opF Ss0 mk2 (main2 c t r))) = opF Ss0 mk2 (main2 c t r) :=
    fun c t r => opF_sdF _ _ _
  have hsd3 : ∀ c c' t r, op3 (sd3 (op3 (main3 c c' t r))) = op3 (main3 c c' t r) := fun c c' t r =>
    congrArg Prod.snd (op2_sd2 Ss0 [] SsT0 SsC0 (fun _ => []) (main3 c c' t r).1 (main3 c c' t r).2)
  have hp3' : ComPfHides NS3 Com3 Pf3 op3 := by
    have e1 : SsT0 = wSsT S10 S9 SP := wit_SsT off blank.hd blank.stk blank.heap.length blank.heap W C Mm Wt tP S10 S9 SP EF.zero qv (wm 0) (wc 0) (ww 0) (wp 0)
    have e2 : SsC0 = wSsC tP S10 S9 SP := wit_SsC off blank.hd blank.stk blank.heap.length blank.heap W C Mm Wt tP S10 S9 SP EF.zero qv (wm 0) (wc 0) (ww 0) (wp 0) ncw
    show ComPfHides NS3 Com3 Pf3 (fun d => (opQ SsT0 d.1, opCw SsC0 d.2))
    rw [e1, e2]; exact hp3
  exact fs_open3 hK2 Q4_pos rvF svF (fun c2 c3 => genB (efOf c3))
    (fun c2 c3 α β r t => realVN_cases _ _ _ _ _ α β r t) (fun c2 c3 α β r t => simVN_some _ _ _ _ _ _ _ _ α β r t)
    (fun c2 c3 hg => (hb c2 c3 hg).1) (fun c2 c3 hg => (hb c2 c3 hg).2)
    Com1 Pf1 (opF Ss0 mk1) (sdF Ss0 mk1) d1 hc1 hp1 hr1 ov1 rfl main1 hsd1
    Com2 Pf2 (opF Ss0 mk2) (sdF Ss0 mk2) d2 hc2 hp2 hr2 ov2 rfl main2 hsd2
    Com3 Pf3 op3 sd3 d3 hc3 hp3' hr3 ov3 rfl main3 hsd3 hvo1 hvo2 hvo3 sop1 sop2 sop3 hsvo1 hsvo2 hsvo3 E

set_option maxRecDepth 100000 in
/-- **The composed PCS's shape reads neither `ζ` nor the weights**, only
    their lengths. -/
theorem comp_same_w (off : EF → String → EF) (hd0 stk0 ctr0 n nilA : Nat) (heap : List Cell) (N W : Nat) (roots : List Nat)
    (C Mm Wt : Table) (tbM tbC tpP tpS : Nat) (SM SC S9 SP SS : List F) (ζ ζ' : EF) (qv : EF → EF → List EF → F → List F → List F → List EF)
    (wm wc ww wp wsg wm' wc' ww' wp' wsg' : List (EF → EF → List F)) (ncw : Nat)
    (hwm : wm.length = wm'.length) (hwc : wc.length = wc'.length) (hww : ww.length = ww'.length) (hwp : wp.length = wp'.length) (hwsg : wsg.length = wsg'.length) :
    SameShape (cGroups tbM tbC tpP tpS SM SC S9 SP SS ζ qv) (cGroups tbM tbC tpP tpS SM SC S9 SP SS ζ' qv)
      (cKs hd0 stk0 ctr0 n nilA heap N W roots)
      ((cTs off hd0 stk0 ctr0 n nilA heap N W roots C Mm Wt tbM tbC tpP tpS SM SC S9 SP SS ζ qv wm wc ww wp wsg).map Prod.fst)
      ((cTs off hd0 stk0 ctr0 n nilA heap N W roots C Mm Wt tbM tbC tpP tpS SM SC S9 SP SS ζ' qv wm' wc' ww' wp' wsg').map Prod.fst) ncw where
  trn := rfl
  dom := rfl
  S := rfl
  shape := by
    simp only [cTs, bbTab, airQTabG, tShape, List.map_cons, List.map_nil, List.length_map]
    rw [hwm, hwc, hww, hwp, hwsg]
  tS := by simp only [cTs, bbTab, airQTabG, List.map_cons, List.map_nil]
  iS := by simp only [cTs, bbTab, airQTabG, tabsInfo, tInfo, List.map_cons, List.map_nil, List.map_append,
    List.map_replicate]

set_option maxRecDepth 100000 in
/-- **The composed proof over three Fiat–Shamir rounds, every commitment
    opened**, in the programmable random-oracle model: the LogUp
    challenges hashed from the main matrices' commitment, the
    constraint-folding challenge (which picks the quotient's weights) from
    the transcript with the permutation matrices' commitment, `ζ` from the
    transcript with the quotient chunks' commitment; each commitment
    opened beside the view; the simulator commits and opens interpolants
    through its own view's openings and programs all three tables
    (`fs_open3`).  Assumed: each commitment hides alone and given its
    openings at the real query points, perfectly, and is a primitive apart
    from the oracle; generic `β` and `ζ`; the weights a family of fixed
    lengths; the FRI challenge `αb` and the query points fixed
    parameters, unhashed; one proof per oracle. -/
theorem comp_fs_open3 {V Wv P1 P2 P3 : Type} (off : EF → String → EF) {R Lm : Nat} (hR : R ≤ 20) {shp : BT} {Ps : List Term}
    {W : Nat} {ρ : Nat → Bool} {region : List Cell} (hrl : region.length = W)
    (hr : ∀ i c, region[i]? = some c → cellOK (BT.nleaves shp + 3 + i) c = true)
    {A : List Cell} {e : Nat → Nat} {row : Nat → Air.Row}
    (hA : AcceptsC A (cMachine ρ shp region Ps) (cHeap ρ shp region Ps).2
      (cHeap ρ shp region Ps).1.length Ps.length e row)
    (hlen : A.length = 2 ^ Lm) (hLm : Lm ≤ 20) (hK : e (Ps.length - 1) < 2 ^ R)
    (hNW : BT.nleaves shp + W ≤ 2 ^ 8)
    {tbM tbC tpP tpS : Nat} (htM : tbM + 1 = Lm) (htC : tbC + 1 = R)
    (htP : tpP = progTpC (blankM shp W Ps).heap (BT.nleaves shp) W) (htS : tpS = segTp (blankRoots shp W Ps))
    {SM SC S9 SP SS : List F} (qv : EF → EF → List EF → F → List F → List F → List EF)
    (wm wc ww wp wsg : Nat → List (EF → EF → List F)) {Lwm Lwc Lww Lwp Lwsg : Nat} (hlwm : ∀ c, (wm c).length = Lwm)
    (hlwc : ∀ c, (wc c).length = Lwc) (hlww : ∀ c, (ww c).length = Lww) (hlwp : ∀ c, (wp c).length = Lwp)
    (hlwsg : ∀ c, (wsg c).length = Lwsg)
    {K2 : Nat} (hK2 : 0 < K2)
    (hSM : ∀ x ∈ SM, x ∉ cosetL 1 (bbGen (tbM + 1)) (2 ^ (tbM + 1)))
    (hSC : ∀ x ∈ SC, x ∉ cosetL 1 (bbGen (tbC + 1)) (2 ^ (tbC + 1)))
    (hS9 : ∀ x ∈ S9, x ∉ cosetL 1 (bbGen 9) (2 ^ 9))
    (hSP : ∀ x ∈ SP, x ∉ cosetL 1 (bbGen (tpP + 1)) (2 ^ (tpP + 1)))
    (hSS : ∀ x ∈ SS, x ∉ cosetL 1 (bbGen (tpS + 1)) (2 ^ (tpS + 1)))
    (hszM : 2 * SM.length + 8 ≤ 2 ^ (tbM + 1)) (hszC : 2 * SC.length + 8 ≤ 2 ^ (tbC + 1))
    (hsz9 : 2 * S9.length + 8 ≤ 2 ^ 9) (hszP : 2 * SP.length + 8 ≤ 2 ^ (tpP + 1))
    (hszS : 2 * SS.length + 8 ≤ 2 ^ (tpS + 1)) {ncw : Nat} {αb : EF} (fri : EF → EF → List (EF → EF) → V) (hncw : 4 ≤ ncw) (hgα : Generic αb)
    (NR2 : Nat) (Rb : EF → EF → Nat → List (EF → EF)) (Ro : EF → EF → Nat → Wv)
    {NS1 NS2 NS3 n1 n2 n3 : Nat}
    (Com1 : List (List (List F)) → Nat → Nat) (Pf1 : List (List (List F)) → Nat → P1) (hc1 : ComHides NS1 Com1)
    (hp1 : ComPfHides NS1 Com1 Pf1 (opF ((cGroups tbM tbC tpP tpS SM SC S9 SP SS EF.zero qv).map (·.base.S)) [0, 2, 4, 6, 8]))
    (hr1 : ∀ d σ, Com1 d σ < n1) (d1 : List (List (List F)))
    (Com2 : List (List (List F)) → Nat → Nat) (Pf2 : List (List (List F)) → Nat → P2) (hc2 : ComHides NS2 Com2)
    (hp2 : ComPfHides NS2 Com2 Pf2 (opF ((cGroups tbM tbC tpP tpS SM SC S9 SP SS EF.zero qv).map (·.base.S)) [1, 3, 5, 7, 9]))
    (hr2 : ∀ d σ, Com2 d σ < n2) (d2 : List (List (List F)))
    (Com3 : List (List (List (List F))) × List (List (List F)) → Nat → Nat)
    (Pf3 : List (List (List (List F))) × List (List (List F)) → Nat → P3) (hc3 : ComHides NS3 Com3)
    (hp3 : ComPfHides NS3 Com3 Pf3 (fun d => (opQ (cSsT SM SC S9 SP SS) d.1, opCw (cSsC tbM tbC tpP tpS SM SC S9 SP SS) d.2)))
    (hr3 : ∀ d σ, Com3 d σ < n3) (d3 : List (List (List (List F))) × List (List (List F)))
    (E : Nat → Nat → Nat → Nat → Nat → Nat → Option P1 × Option (P2 × P3) × TViewN (PcsPV (V × Wv)) (EF × EF) → Bool) :
    let m := blankM shp W Ps
    let roots := blankRoots shp W Ps
    let N := BT.nleaves shp
    let C := cpuTableC A row e Ps.length roots (2 ^ R)
    let Pg := progTableC m.heap N W
    let Wt := witTable A N W
    let Mm := memTableC A (cpuAirC m.hd m.stk m.heap.length roots.length m.stk) (progAirC m.heap N W)
      (witAir N W) C Pg Wt
    let NR0 := cNR off m.hd m.stk m.heap.length roots.length m.stk m.heap N W roots C Mm Wt tbM tbC tpP tpS SM SC S9 SP SS EF.zero qv (wm 0) (wc 0) (ww 0) (wp 0) (wsg 0) ncw
    let pcsZ := fun (c2 : Nat) (ζ : EF) t α β r => cPcs off m.hd m.stk m.heap.length roots.length m.stk m.heap N W roots C Mm Wt tbM tbC tpP tpS SM SC S9 SP SS ζ qv (wm c2) (wc c2) (ww c2) (wp c2) (wsg c2) ncw αb
      (friX fri Rb Ro (r / NR0)) t α β (r % NR0)
    let psimZ := fun (c2 : Nat) (ζ : EF) α β v r => cPsim off m.hd m.stk m.heap.length roots.length m.stk m.heap N W roots C Mm Wt tbM tbC tpP tpS SM SC S9 SP SS ζ qv (wm c2) (wc c2) (ww c2) (wp c2) (wsg c2) ncw αb
      (friX fri Rb Ro (r / NR0)) α β v (r % NR0)
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
    let q0 := cGroups tbM tbC tpP tpS SM SC S9 SP SS EF.zero qv
    let Ss0 := q0.map (·.base.S)
    let ks := cKs m.hd m.stk m.heap.length roots.length m.stk m.heap N W roots
    let cols := cCols off m.hd m.stk m.heap.length roots.length m.stk m.heap N W roots C Mm Wt
    let tqZ := fun (c2 : Nat) (ζ : EF) => (cTs off m.hd m.stk m.heap.length roots.length m.stk m.heap N W roots C Mm Wt tbM tbC tpP tpS SM SC S9 SP SS ζ qv (wm c2) (wc c2) (ww c2) (wp c2) (wsg c2)).map Prod.fst
    let qdZ := fun (c2 : Nat) (ζ : EF) (t : Nat → Tup) (α β : EF) (ms : List F) =>
      (cTs off m.hd m.stk m.heap.length roots.length m.stk m.heap N W roots C Mm Wt tbM tbC tpP tpS SM SC S9 SP SS ζ qv (wm c2) (wc c2) (ww c2) (wp c2) (wsg c2)).map (fun p => p.2 t α β ms)
    let SsT0 := (tqZ 0 EF.zero).map (·.S)
    let SsC0 := (tabsInfo ncw (tqZ 0 EF.zero)).map (·.S)
    let mk1 := [0, 2, 4, 6, 8]
    let mk2 := [1, 3, 5, 7, 9]
    let main1 := fun (t : Nat → Tup) (r : Nat) => mainF2 q0 ks cols (tqZ 0 EF.zero) ncw mk1 t (r % NR0)
    let main2 := fun (c1 : Nat) (t : Nat → Tup) (r : Nat) =>
      mainP2 q0 ks cols (tqZ 0 EF.zero) ncw mk2 t (efOf (c1 / Q4)) (efOf (c1 % Q4)) (r % NR0)
    let main3 := fun (c1 c2 : Nat) (t : Nat → Tup) (r : Nat) =>
      (tabsPolys (tqZ c2 EF.zero) (qdZ c2 EF.zero t (efOf (c1 / Q4)) (efOf (c1 % Q4))
          (msF q0 ks (tqZ c2 EF.zero) ncw (r % NR0))) (crF q0 ks (tqZ c2 EF.zero) ncw (r % NR0)),
       tabsCws ncw (tqZ c2 EF.zero) (ccF q0 ks (tqZ c2 EF.zero) ncw (r % NR0)))
    let vS := fun (α β : EF) (t : Nat → Tup) => viewT β (fun k => prefixOf α (off β) (chainBus k)) (fun _ => false)
      chainPar 3 (xrefN (ptm (prefixOf α (off β)) β)) t
    let qZ := fun (ζ : EF) => cGroups tbM tbC tpP tpS SM SC S9 SP SS ζ qv
    let sop1 := fun (c2 c3 r : Nat) (_ : Nat → Tup) =>
      opF Ss0 mk1 (mainZ2 (qZ (efOf c3)) ks (tqZ c2 (efOf c3)) ncw mk1 (r % NR0))
    let sop2 := fun (c2 c3 _ r : Nat) (_ : Nat → Tup) =>
      opF Ss0 mk2 (mainZ2 (qZ (efOf c3)) ks (tqZ c2 (efOf c3)) ncw mk2 (r % NR0))
    let sop3 := fun (c2 c3 c1 r : Nat) (t : Nat → Tup) =>
      (opQ SsT0 (tabsPolys (tqZ c2 (efOf c3)) (canonT (tqZ c2 (efOf c3)) (efOf (c1 / Q4)) (efOf (c1 % Q4))
         (vS (efOf (c1 / Q4)) (efOf (c1 % Q4)) t)
         (openMulti ((qZ (efOf c3)).map QGroup.ext) ((((qZ (efOf c3)).map QGroup.ext).zip ks).map
           (fun p => List.replicate p.2 (List.replicate p.1.n (0 : F)))) (msF (qZ (efOf c3)) ks (tqZ c2 (efOf c3)) ncw (r % NR0))))
         (crF (qZ (efOf c3)) ks (tqZ c2 (efOf c3)) ncw (r % NR0))),
       opCw SsC0 (tabsCws ncw (tqZ c2 (efOf c3)) (ccF (qZ (efOf c3)) ks (tqZ c2 (efOf c3)) ncw (r % NR0))))
    let ov1 : TViewN (PcsPV (V × Wv)) (EF × EF) → Option (List (List (List F))) := fun v => match v with
      | some (pv, _) => some (ovF2 Ss0 mk1 pv)
      | none => none
    let ov2 : TViewN (PcsPV (V × Wv)) (EF × EF) → Option (List (List (List F))) := fun v => match v with
      | some (pv, _) => some (ovF2 Ss0 mk2 pv)
      | none => none
    let ov3 : TViewN (PcsPV (V × Wv)) (EF × EF) → Option (List (List (List (List F))) × List (List (List F))) := fun v =>
      match v with
      | some (pv, _) => some (ovQ pv, cwQ 10 pv)
      | none => none
    let rvF := fun (c2 c3 : Nat) (α β : EF) (r : Nat) (t : Nat → Tup) => realVN off tabs tv pb (pcsZ c2 (efOf c3)) α β r t
    let svF := fun (c2 c3 : Nat) (α β : EF) (r : Nat) (t : Nat → Tup) =>
      simVN off pb chainBus (fun _ => false) chainPar 3 ptm (psimZ c2 (efOf c3)) α β r t
    let op3 := fun (d : List (List (List (List F))) × List (List (List F))) => (opQ SsT0 d.1, opCw SsC0 d.2)
    let sd3 := fun (o : List (List (List (List F))) × List (List (List F))) => (sdQ SsT0 o.1, sdCw SsC0 o.2)
    let sm := fun (g : Nat × Nat × Nat × (Nat → Tup) → Nat) =>
      sumTo NS1 (fun σ1 => sumTo (NS2 * NS3) (fun σ => sumTo NR (fun r => sumN 2 (fun t => g (σ1, σ, r, t)))))
    let m1 := fun (x : Nat × Nat × Nat × (Nat → Tup)) => Com1 (main1 x.2.2.2 x.2.2.1) x.1
    let m2 := fun (c1 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      m1 x + n1 * Com2 (main2 c1 x.2.2.2 x.2.2.1) (x.2.1 % NS2)
    let m3 := fun (c1 c2 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      m1 x + n1 * comPair NS2 n2 Com2 Com3 (main2 c1 x.2.2.2 x.2.2.1, main3 c1 c2 x.2.2.2 x.2.2.1) x.2.1
    let rvo := fun (c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      ((ov1 (rvF c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)).map (fun _ => Pf1 (main1 x.2.2.2 x.2.2.1) x.1),
       (ovPair ov2 ov3 (rvF c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)).map
         (fun _ => pfPair NS2 Pf2 Pf3 (main2 c1 x.2.2.2 x.2.2.1, main3 c1 c2 x.2.2.2 x.2.2.1) x.2.1),
       rvF c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)
    let s1 := fun (c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) => Com1 ((sdF Ss0 mk1) (sop1 c2 c3 x.2.2.1 x.2.2.2)) x.1
    let s2 := fun (c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      s1 c1 c2 c3 x + n1 * Com2 ((sdF Ss0 mk2) (sop2 c2 c3 c1 x.2.2.1 x.2.2.2)) (x.2.1 % NS2)
    let s3 := fun (c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      s1 c1 c2 c3 x + n1 * comPair NS2 n2 Com2 Com3
        ((sdF Ss0 mk2) (sop2 c2 c3 c1 x.2.2.1 x.2.2.2), sd3 (sop3 c2 c3 c1 x.2.2.1 x.2.2.2)) x.2.1
    let svo := fun (c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      (some (Pf1 ((sdF Ss0 mk1) (sop1 c2 c3 x.2.2.1 x.2.2.2)) x.1),
       some (pfPair NS2 Pf2 Pf3 ((sdF Ss0 mk2) (sop2 c2 c3 c1 x.2.2.1 x.2.2.2), sd3 (sop3 c2 c3 c1 x.2.2.1 x.2.2.2)) x.2.1),
       svF c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)
    let gd := fun (c1 c2 c3 : Nat) => genB (efOf (c1 % Q4)) && genB (efOf c3)
    (Q4 * Q4) * (K2 * (Q4 * sumTo ((Q4 * Q4) ^ n1) (fun H1 => sumTo (K2 ^ (n1 * n2)) (fun H2 =>
      sumTo (Q4 ^ (n1 * (n2 * n3))) (fun H3 => sm (fun x =>
      indB (gd (rget (Q4 * Q4) (m1 x) H1) (rget K2 (m2 (rget (Q4 * Q4) (m1 x) H1) x) H2)
          (rget Q4 (m3 (rget (Q4 * Q4) (m1 x) H1) (rget K2 (m2 (rget (Q4 * Q4) (m1 x) H1) x) H2) x) H3) &&
        E H1 H2 H3 (m1 x) (m2 (rget (Q4 * Q4) (m1 x) H1) x)
          (m3 (rget (Q4 * Q4) (m1 x) H1) (rget K2 (m2 (rget (Q4 * Q4) (m1 x) H1) x) H2) x)
          (rvo (rget (Q4 * Q4) (m1 x) H1) (rget K2 (m2 (rget (Q4 * Q4) (m1 x) H1) x) H2)
            (rget Q4 (m3 (rget (Q4 * Q4) (m1 x) H1) (rget K2 (m2 (rget (Q4 * Q4) (m1 x) H1) x) H2) x) H3) x)))))))) ≤
    sumTo ((Q4 * Q4) ^ n1) (fun H1 => sumTo (K2 ^ (n1 * n2)) (fun H2 => sumTo (Q4 ^ (n1 * (n2 * n3))) (fun H3 =>
      sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo Q4 (fun c3 => sm (fun x =>
        indB (gd c1 c2 c3 && E (rset (Q4 * Q4) (s1 c1 c2 c3 x) H1 c1) (rset K2 (s2 c1 c2 c3 x) H2 c2)
          (rset Q4 (s3 c1 c2 c3 x) H3 c3) (s1 c1 c2 c3 x) (s2 c1 c2 c3 x) (s3 c1 c2 c3 x) (svo c1 c2 c3 x))))))))) +
      (Q4 * Q4) ^ n1 * (K2 ^ (n1 * n2) * (Q4 ^ (n1 * (n2 * n3)) *
        (K2 * (Q4 * (NS1 * (NS2 * NS3 * ((Q4 * (NR * (Q4 ^ 2 * M)) + Q4 * (Q4 * (Q4 ^ 2 * 0)))))))))) := by
  intro m roots N C Pg Wt Mm NR0 pcsZ psimZ NR tabs tv pb ptm M q0 Ss0 ks cols tqZ qdZ SsT0 SsC0 mk1 mk2 main1 main2 main3 vS qZ sop1 sop2 sop3 ov1 ov2 ov3 rvF svF op3 sd3
  obtain ⟨hbal, hun⟩ := comp_honest_zk hR hrl hr hA hlen hLm hK hNW
  obtain ⟨sc, sms, sw, hWh, _⟩ := comp_run_sats hR hrl hr hA hlen hLm hK hNW
  obtain ⟨p1, p2, s1, s2⟩ := comp_pub_heights hR hrl hA hlen hLm hK
  rw [← htP] at p1 p2
  rw [← htS] at s1 s2
  have hM : Mm.h = 2 ^ (tbM + 1) := by rw [htM]; exact hlen
  have hC : C.h = 2 ^ (tbC + 1) := by rw [htC]; rfl
  have hSw := fun (c2 c3 : Nat) => comp_same_w off m.hd m.stk m.heap.length roots.length m.stk m.heap N W roots C Mm Wt tbM tbC tpP tpS SM SC S9 SP SS (efOf c3) EF.zero qv (wm c2) (wc c2) (ww c2) (wp c2) (wsg c2) (wm 0) (wc 0) (ww 0) (wp 0) (wsg 0) ncw (by rw [hlwm, hlwm]) (by rw [hlwc, hlwc]) (by rw [hlww, hlww]) (by rw [hlwp, hlwp]) (by rw [hlwsg, hlwsg])
  have hSz := fun (c2 c3 : Nat) => comp_same_w off m.hd m.stk m.heap.length roots.length m.stk m.heap N W roots C Mm Wt tbM tbC tpP tpS SM SC S9 SP SS (efOf c3) EF.zero qv (wm c2) (wc c2) (ww c2) (wp c2) (wsg c2) (wm c2) (wc c2) (ww c2) (wp c2) (wsg c2) ncw rfl rfl rfl rfl rfl
  have hS0 := fun (c2 : Nat) => comp_same_w off m.hd m.stk m.heap.length roots.length m.stk m.heap N W roots C Mm Wt tbM tbC tpP tpS SM SC S9 SP SS EF.zero EF.zero qv (wm c2) (wc c2) (ww c2) (wp c2) (wsg c2) (wm 0) (wc 0) (ww 0) (wp 0) (wsg 0) ncw (by rw [hlwm, hlwm]) (by rw [hlwc, hlwc]) (by rw [hlww, hlww]) (by rw [hlwp, hlwp]) (by rw [hlwsg, hlwsg])
  have hb : ∀ c2 c3, genB (efOf c3) = true →
      (∀ E' : TViewN (PcsPV (V × Wv)) (EF × EF) → Bool,
        tsumN NR 2 (fun α β r t => indB (genB β && E' (rvF c2 c3 α β r t))) ≤
          tsumN NR 2 (fun α β r t => indB (genB β && E' (svF c2 c3 α β r t))) + Q4 * (NR * (Q4 ^ 2 * M)) +
            Q4 * (Q4 * (Q4 ^ 2 * 0))) ∧
      (∀ E' : TViewN (PcsPV (V × Wv)) (EF × EF) → Bool,
        tsumN NR 2 (fun α β r t => indB (genB β && E' (svF c2 c3 α β r t))) ≤
          tsumN NR 2 (fun α β r t => indB (genB β && E' (rvF c2 c3 α β r t))) + Q4 * (NR * (Q4 ^ 2 * M)) +
            Q4 * (Q4 * (Q4 ^ 2 * 0))) := fun c2 c3 hg => by
    have hgz := (genB_iff _).1 hg
    have hpcs := comp_pcsX (heap := m.heap) (ζ := efOf c3) (roots := roots) off sc sms sw (by omega) (by omega) (by omega) (by omega)
      hM hC hWh p2 s2 qv (wm c2) (wc c2) (ww c2) (wp c2) (wsg c2) hSM hSC hS9 hSP hSS hszM hszC hsz9 hszP hszS (generic_ofF_ne hgz) (mz_generic hgz) fri (mz_generic hgα) (generic_apow_ne hgα) hncw NR2 Rb Ro
    have hNR : cNR off m.hd m.stk m.heap.length roots.length m.stk m.heap N W roots C Mm Wt tbM tbC tpP tpS SM SC S9 SP SS (efOf c3) qv (wm c2) (wc c2) (ww c2) (wp c2) (wsg c2) ncw = cNR off m.hd m.stk m.heap.length roots.length m.stk m.heap N W roots C Mm Wt tbM tbC tpP tpS SM SC S9 SP SS EF.zero qv (wm 0) (wc 0) (ww 0) (wp 0) (wsg 0) ncw := by
      unfold cNR; rw [(hSw c2 c3).n1, (hSw c2 c3).n2]
    rw [hNR] at hpcs
    exact ⟨fun E' => (comp_transcriptG off NR 0 (pcsZ c2 (efOf c3)) (psimZ c2 (efOf c3)) hbal hun hpcs E').1,
      fun E' => (comp_transcriptG off NR 0 (pcsZ c2 (efOf c3)) (psimZ c2 (efOf c3)) hbal hun hpcs E').2⟩
  have hlen8 : ∀ (ζ : EF) t α β, (cols t α β).map List.length = (cols t EF.zero EF.zero).map List.length :=
    fun ζ t α β => by
      rw [(cCols_shaped off m.hd m.stk m.heap.length roots.length m.stk hM hC hWh p2 s2
          SM SC S9 SP SS ζ qv t α β).2,
        (cCols_shaped off m.hd m.stk m.heap.length roots.length m.stk hM hC hWh p2 s2
          SM SC S9 SP SS ζ qv t EF.zero EF.zero).2]
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
  have hvo1 : ∀ c2 c3 c r t, rvF c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t = none ∨
      ov1 (rvF c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (opF Ss0 mk1 (main1 t r)) := by
    intro c2 c3 c r t
    show realVN off tabs tv pb (pcsZ c2 (efOf c3)) _ _ r t = none ∨
      ov1 (realVN off tabs tv pb (pcsZ c2 (efOf c3)) _ _ r t) = _
    unfold realVN
    split
    · exact .inl rfl
    · have e := pcsFri_ov2 off (fun pre β t => compViewN pre β m.hd m.stk m.heap.length roots.length m.stk N W C Mm Wt t) (cGroups tbM tbC tpP tpS SM SC S9 SP SS (efOf c3) qv) ks cols ((cTs off m.hd m.stk m.heap.length roots.length m.stk m.heap N W roots C Mm Wt tbM tbC tpP tpS SM SC S9 SP SS (efOf c3) qv (wm c2) (wc c2) (ww c2) (wp c2) (wsg c2)).map Prod.fst) (fun t α β ms => (cTs off m.hd m.stk m.heap.length roots.length m.stk m.heap N W roots C Mm Wt tbM tbC tpP tpS SM SC S9 SP SS (efOf c3) qv (wm c2) (wc c2) (ww c2) (wp c2) (wsg c2)).map fun p => p.2 t α β ms) ncw αb
        (friX fri Rb Ro (r / NR0)) mk1 hmk1 (hlen8 (efOf c3)) rfl t (efOf (c / Q4)) (efOf (c % Q4)) (r % NR0)
      rw [(hSw c2 c3).dataF2 cols mk1 t (r % NR0), (hSw c2 c3).S] at e
      exact .inr (congrArg some e)
  have hvo2 : ∀ c2 c3 c r t, rvF c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t = none ∨
      ov2 (rvF c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (opF Ss0 mk2 (main2 c t r)) := by
    intro c2 c3 c r t
    show realVN off tabs tv pb (pcsZ c2 (efOf c3)) _ _ r t = none ∨
      ov2 (realVN off tabs tv pb (pcsZ c2 (efOf c3)) _ _ r t) = _
    unfold realVN
    split
    · exact .inl rfl
    · have e := pcsFri_ovP off (fun pre β t => compViewN pre β m.hd m.stk m.heap.length roots.length m.stk N W C Mm Wt t) (cGroups tbM tbC tpP tpS SM SC S9 SP SS (efOf c3) qv) ks cols ((cTs off m.hd m.stk m.heap.length roots.length m.stk m.heap N W roots C Mm Wt tbM tbC tpP tpS SM SC S9 SP SS (efOf c3) qv (wm c2) (wc c2) (ww c2) (wp c2) (wsg c2)).map Prod.fst) (fun t α β ms => (cTs off m.hd m.stk m.heap.length roots.length m.stk m.heap N W roots C Mm Wt tbM tbC tpP tpS SM SC S9 SP SS (efOf c3) qv (wm c2) (wc c2) (ww c2) (wp c2) (wsg c2)).map fun p => p.2 t α β ms) ncw αb
        (friX fri Rb Ro (r / NR0)) mk2 hmk2 rfl t (efOf (c / Q4)) (efOf (c % Q4)) (r % NR0)
      rw [(hSw c2 c3).dataP2 cols mk2 t _ _ (r % NR0), (hSw c2 c3).S] at e
      exact .inr (congrArg some e)
  have hvo3 : ∀ c2 c3 c r t, rvF c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t = none ∨
      ov3 (rvF c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (op3 (main3 c c2 t r)) := by
    intro c2 c3 c r t
    show realVN off tabs tv pb (pcsZ c2 (efOf c3)) _ _ r t = none ∨
      ov3 (realVN off tabs tv pb (pcsZ c2 (efOf c3)) _ _ r t) = _
    unfold realVN
    split
    · exact .inl rfl
    · rename_i hab
      have hab' : Aborts (prefixOf (efOf (c / Q4)) (off (efOf (c % Q4)))) (efOf (c % Q4)) (tabs t) = false := by
        cases h : Aborts (prefixOf (efOf (c / Q4)) (off (efOf (c % Q4)))) (efOf (c % Q4)) (tabs t)
        · rfl
        · exact absurd h hab
      have e0 := pcsFri_ovR2 off (fun pre β t => compViewN pre β m.hd m.stk m.heap.length roots.length m.stk N W C Mm Wt t) (cGroups tbM tbC tpP tpS SM SC S9 SP SS (efOf c3) qv) ks cols ((cTs off m.hd m.stk m.heap.length roots.length m.stk m.heap N W roots C Mm Wt tbM tbC tpP tpS SM SC S9 SP SS (efOf c3) qv (wm c2) (wc c2) (ww c2) (wp c2) (wsg c2)).map Prod.fst) (fun t α β ms => (cTs off m.hd m.stk m.heap.length roots.length m.stk m.heap N W roots C Mm Wt tbM tbC tpP tpS SM SC S9 SP SS (efOf c3) qv (wm c2) (wc c2) (ww c2) (wp c2) (wsg c2)).map fun p => p.2 t α β ms) ncw αb
        (friX fri Rb Ro (r / NR0)) mk2 hmk2 rfl t (efOf (c / Q4)) (efOf (c % Q4)) (r % NR0)
      have e := congrArg Prod.snd e0
      rw [(hSz c2 c3).tS, (hSz c2 c3).iS, tabsPolys_congr _ _ _ _ (hSz c2 c3).shape,
        tabsCws_congr ncw _ _ _ (hSz c2 c3).shape, (hSz c2 c3).cr (r % NR0), (hSz c2 c3).cc (r % NR0),
        (hSz c2 c3).ms (r % NR0), (hS0 c2).tS, (hS0 c2).iS,
        comp_data_zeta off m.hd m.stk m.heap.length roots.length m.stk m.heap N W roots C Mm Wt tbM tbC tpP tpS SM SC S9 SP SS (efOf c3) EF.zero
          qv (wm c2) (wc c2) (ww c2) (wp c2) (wsg c2) t _ _ _ hab'] at e
      exact .inr (congrArg some e)
  have hsvo1 : ∀ c2 c3 c r t, ov1 (svF c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (sop1 c2 c3 r t) :=
    fun c2 c3 c r t => congrArg some (psimFri_ov2 (qZ (efOf c3)) ks (tqZ c2 (efOf c3)) ncw αb _ mk1
      (fun k hk => (hmk1 k hk).1) rfl _ _ _ (r % NR0))
  have hsvo2 : ∀ c2 c3 c r t, ov2 (svF c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (sop2 c2 c3 c r t) :=
    fun c2 c3 c r t => congrArg some (psimFri_ov2 (qZ (efOf c3)) ks (tqZ c2 (efOf c3)) ncw αb _ mk2
      (fun k hk => (hmk2 k hk).1) rfl _ _ _ (r % NR0))
  have hsvo3 : ∀ c2 c3 c r t, ov3 (svF c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (sop3 c2 c3 c r t) := by
    intro c2 c3 c r t
    have e0 := psimFri_ovR2 (cGroups tbM tbC tpP tpS SM SC S9 SP SS (efOf c3) qv) ks ((cTs off m.hd m.stk m.heap.length roots.length m.stk m.heap N W roots C Mm Wt tbM tbC tpP tpS SM SC S9 SP SS (efOf c3) qv (wm c2) (wc c2) (ww c2) (wp c2) (wsg c2)).map Prod.fst) ncw αb (friX fri Rb Ro (r / NR0)) mk2
      (fun k hk => (hmk2 k hk).1) rfl (efOf (c / Q4)) (efOf (c % Q4)) (vS (efOf (c / Q4)) (efOf (c % Q4)) t) (r % NR0)
    have e := congrArg Prod.snd e0
    rw [(hSw c2 c3).tS, (hSw c2 c3).iS] at e
    exact congrArg some e
  have hsd1 : ∀ t r, opF Ss0 mk1 (sdF Ss0 mk1 (opF Ss0 mk1 (main1 t r))) = opF Ss0 mk1 (main1 t r) :=
    fun t r => opF_sdF _ _ _
  have hsd2 : ∀ c t r, opF Ss0 mk2 (sdF Ss0 mk2 (opF Ss0 mk2 (main2 c t r))) = opF Ss0 mk2 (main2 c t r) :=
    fun c t r => opF_sdF _ _ _
  have hsd3 : ∀ c c' t r, op3 (sd3 (op3 (main3 c c' t r))) = op3 (main3 c c' t r) := fun c c' t r =>
    congrArg Prod.snd (op2_sd2 Ss0 [] SsT0 SsC0 (fun _ => []) (main3 c c' t r).1 (main3 c c' t r).2)
  have hp3' : ComPfHides NS3 Com3 Pf3 op3 := by
    have e1 : SsT0 = cSsT SM SC S9 SP SS := comp_SsT off m.hd m.stk m.heap.length roots.length m.stk m.heap N W roots C Mm Wt tbM tbC tpP tpS SM SC S9 SP SS EF.zero qv (wm 0) (wc 0) (ww 0) (wp 0) (wsg 0)
    have e2 : SsC0 = cSsC tbM tbC tpP tpS SM SC S9 SP SS := comp_SsC off m.hd m.stk m.heap.length roots.length m.stk m.heap N W roots C Mm Wt tbM tbC tpP tpS SM SC S9 SP SS EF.zero qv (wm 0) (wc 0) (ww 0) (wp 0) (wsg 0) ncw
    show ComPfHides NS3 Com3 Pf3 (fun d => (opQ SsT0 d.1, opCw SsC0 d.2))
    rw [e1, e2]; exact hp3
  exact fs_open3 hK2 Q4_pos rvF svF (fun c2 c3 => genB (efOf c3))
    (fun c2 c3 α β r t => realVN_cases _ _ _ _ _ α β r t) (fun c2 c3 α β r t => simVN_some _ _ _ _ _ _ _ _ α β r t)
    (fun c2 c3 hg => (hb c2 c3 hg).1) (fun c2 c3 hg => (hb c2 c3 hg).2)
    Com1 Pf1 (opF Ss0 mk1) (sdF Ss0 mk1) d1 hc1 hp1 hr1 ov1 rfl main1 hsd1
    Com2 Pf2 (opF Ss0 mk2) (sdF Ss0 mk2) d2 hc2 hp2 hr2 ov2 rfl main2 hsd2
    Com3 Pf3 op3 sd3 d3 hc3 hp3' hr3 ov3 rfl main3 hsd3 hvo1 hvo2 hvo3 sop1 sop2 sop3 hsvo1 hsvo2 hsvo3 E

end Circuit
