import Ski.ZK.FSRound2

/-!
# The hidden-term and composed proofs over two Fiat–Shamir rounds

`sud_fs2`'s construction for the other two circuits (`wit_fs2`,
`comp_fs2`), their randomness counts independent of `ζ` (`wNR_zeta`,
`cNR_zeta`).  Scope as in `Ski/ZK/FSRound2.lean`.
-/

namespace Circuit

open ZKF B Air Compose CompM Stmt Mach Wit

set_option maxRecDepth 100000 in
theorem wNR_zeta (off : EF → String → EF) (hd0 stk0 ctr0 : Nat) (heap : List Cell) (W : Nat) (C Mm Wt : Table) (tp : Nat)
    (S10 S9 SP : List F) (ζ ζ' : EF) (qv : EF → EF → List EF → F → List F → List F → List EF)
    (wm wc ww wp : List (EF → EF → List F)) (ncw : Nat) :
    wNR off hd0 stk0 ctr0 heap W C Mm Wt tp S10 S9 SP ζ qv wm wc ww wp ncw =
      wNR off hd0 stk0 ctr0 heap W C Mm Wt tp S10 S9 SP ζ' qv wm wc ww wp ncw := by
  have ht : ((wTs off hd0 stk0 ctr0 heap W C Mm Wt tp S10 S9 SP ζ qv wm wc ww wp).map Prod.fst).map
        (fun T => (T.tg.length, T.cs.length, T.h)) =
      ((wTs off hd0 stk0 ctr0 heap W C Mm Wt tp S10 S9 SP ζ' qv wm wc ww wp).map Prod.fst).map
        (fun T => (T.tg.length, T.cs.length, T.h)) := by
    simp only [wTs, bbTab, airQTabG, List.map_cons, List.map_nil, List.length_map]
  have hn : ((wGroups tp S10 S9 SP ζ qv).map QGroup.ext).map MGroup.n =
      ((wGroups tp S10 S9 SP ζ' qv).map QGroup.ext).map MGroup.n := rfl
  have hd : ((wGroups tp S10 S9 SP ζ qv).map QGroup.ext).map MGroup.dom =
      ((wGroups tp S10 S9 SP ζ' qv).map QGroup.ext).map MGroup.dom := rfl
  unfold wNR friN1 friN2
  rw [mtotal_congr _ _ _ hn, tabsCr_congr _ _ ht, traceCw_congr ncw _ _ hd, tabsCw_congr ncw _ _ ht]

set_option maxRecDepth 100000 in
/-- **The hidden-term proof under Fiat–Shamir over two rounds**, as
    `sud_fs2`: the LogUp challenges hashed from the first commitment, `ζ`
    from the second, both unopened in the view, summed over generic `ζ`. -/
theorem wit_fs2 {V Wv D1 D2 : Type} (off : EF → String → EF) {Vt x : Term} {W : Nat} {ws : List Cell} (hwf : WF ws)
    (hwl : ws.length = W) (hW8 : W ≤ 2 ^ 8) {A : List Cell} {k : Nat} {row : Nat → Air.Row}
    (hA : AcceptsFrom A (wMachine ws (Vt ⬝ x)) k row)
    (hK : rd A (row (k - 1)).ctr (row (k - 1)).hd = some .K ∧ rd A (row (k - 1)).ctr (row (k - 1)).stk = some .nil)
    (hlen : A.length = 2 ^ 10) (hk : k ≤ 2 ^ 10)
    {tP : Nat} (htp : tP = progTpW (wMachine (List.replicate W .S) (Vt ⬝ x)).heap W)
    {S10 S9 SP : List F} (qv : EF → EF → List EF → F → List F → List F → List EF)
    (wm wc ww wp : List (EF → EF → List F))
    (hS10 : ∀ x ∈ S10, x ∉ cosetL 1 (bbGen 10) (2 ^ 10)) (hS9 : ∀ x ∈ S9, x ∉ cosetL 1 (bbGen 9) (2 ^ 9))
    (hSP : ∀ x ∈ SP, x ∉ cosetL 1 (bbGen (tP + 1)) (2 ^ (tP + 1)))
    (hsz10 : 2 * S10.length + 8 ≤ 2 ^ 10) (hsz9 : 2 * S9.length + 8 ≤ 2 ^ 9)
    (hszP : 2 * SP.length + 8 ≤ 2 ^ (tP + 1)) {ncw : Nat} {αb : EF} (fri : EF → EF → List (EF → EF) → V) (hncw : 4 ≤ ncw) (hgα : Generic αb)
    (NR2 : Nat) (Rb : EF → EF → Nat → List (EF → EF)) (Ro : EF → EF → Nat → Wv)
    {NS1 NS2 n1 n2 : Nat} (Com1 : D1 → Nat → Nat) (hc1 : ComHides NS1 Com1) (hr1 : ∀ d σ, Com1 d σ < n1)
    (Com2 : D2 → Nat → Nat) (hc2 : ComHides NS2 Com2) (hr2 : ∀ d σ, Com2 d σ < n2)
    (main1 : (Nat → Tup) → Nat → D1) (main2 : Nat → (Nat → Tup) → Nat → D2) (d1 : D1) (d2 : D2)
    (E : Nat → Nat → Nat → Nat → TViewN (PcsPV (V × Wv)) EF → Bool) :
    let blank := wMachine (List.replicate W .S) (Vt ⬝ x)
    let C := cpuTableW A row k (2 ^ 10)
    let Pg := progTableW blank.heap W
    let Wt := witTableG 0 A 0 W
    let Mm := memTableC A (cpuAirW blank.hd blank.stk blank.heap.length) (progAirW blank.heap W) (witAirW W) C Pg Wt
    let NR0 := wNR off blank.hd blank.stk blank.heap.length blank.heap W C Mm Wt tP S10 S9 SP EF.zero qv wm wc ww wp ncw
    let pcsZ := fun (ζ : EF) t α β r => wPcs off blank.hd blank.stk blank.heap.length blank.heap W C Mm Wt tP S10 S9 SP ζ qv wm wc ww wp ncw αb
      (friX fri Rb Ro (r / NR0)) t α β (r % NR0)
    let psimZ := fun (ζ : EF) α β v r => wPsim off blank.hd blank.stk blank.heap.length blank.heap W C Mm Wt tP S10 S9 SP ζ qv wm wc ww wp ncw αb
      (friX fri Rb Ro (r / NR0)) α β v (r % NR0)
    let NR := NR0 * NR2
    let tabs := fun t : Nat → Tup => witTables blank.hd blank.stk blank.heap.length blank.heap W
      ((C.setBlind BLA (t 1)).setBlind BLB (t 0)) (Mm.setBlind 5 (t 0)) (progTableW blank.heap W)
      (Wt.setBlind WT_BLIND (t 1))
    let tv := fun pre β t => witViewN pre β blank.hd blank.stk blank.heap.length W C Mm Wt t
    let ptm := fun pre β => terminal pre β (progAirW blank.heap W) (progTableW blank.heap W)
    let M := (allEntries (witTables blank.hd blank.stk blank.heap.length blank.heap W C Mm (progTableW blank.heap W)
      Wt)).length
    let sm := fun (g : Nat × Nat × Nat × (Nat → Tup) → Nat) =>
      sumTo NS1 (fun σ1 => sumTo NS2 (fun σ2 => sumTo NR (fun r => sumN 2 (fun t => g (σ1, σ2, r, t)))))
    let m1 := fun (x : Nat × Nat × Nat × (Nat → Tup)) => Com1 (main1 x.2.2.2 x.2.2.1) x.1
    let m2 := fun (c1 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) => Com2 (main2 c1 x.2.2.2 x.2.2.1) x.2.1
    let rv := fun (c1 c2 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      realVN off tabs tv ptm (pcsZ (efOf c2)) (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2
    let sv := fun (c1 c2 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      simVN off ptm chainBus (fun _ => false) chainPar 3 ptm (psimZ (efOf c2)) (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2
    let gd := fun (c1 c2 : Nat) => genB (efOf (c1 % Q4)) && genB (efOf c2)
    let err := Q4 * (NR * (Q4 ^ 2 * M)) + Q4 * (Q4 * (Q4 ^ 2 * 0))
    (Q4 * Q4) * (Q4 * sumTo ((Q4 * Q4) ^ n1) (fun H1 => sumTo (Q4 ^ n2) (fun H2 => sm (fun x =>
      indB (gd (rget (Q4 * Q4) (m1 x) H1) (rget Q4 (m2 (rget (Q4 * Q4) (m1 x) H1) x) H2) &&
        E H1 H2 (m1 x) (m2 (rget (Q4 * Q4) (m1 x) H1) x)
          (rv (rget (Q4 * Q4) (m1 x) H1) (rget Q4 (m2 (rget (Q4 * Q4) (m1 x) H1) x) H2) x)))))) ≤
    sumTo ((Q4 * Q4) ^ n1) (fun H1 => sumTo (Q4 ^ n2) (fun H2 => sumTo (Q4 * Q4) (fun c1 => sumTo Q4 (fun c2 =>
      sm (fun x => indB (gd c1 c2 && E (rset (Q4 * Q4) (Com1 d1 x.1) H1 c1) (rset Q4 (Com2 d2 x.2.1) H2 c2)
        (Com1 d1 x.1) (Com2 d2 x.2.1) (sv c1 c2 x))))))) +
      (Q4 * Q4) ^ n1 * (Q4 ^ n2 * (Q4 * (NS1 * (NS2 * err)))) := by
  intro blank C Pg Wt Mm NR0 pcsZ psimZ NR tabs tv ptm M sm m1 m2 rv sv gd err
  obtain ⟨hbal, hun⟩ := wit_honest_zk hwf hwl hW8 hA hlen hk
  obtain ⟨sc, sms, sw, hWh⟩ := wit_run_sats hwf hwl hW8 hA hK hlen hk
  obtain ⟨_, hP23, hPg⟩ := wit_prog_height hwl hA hlen
  rw [← htp] at hP23 hPg
  have hb : ∀ c2, genB (efOf c2) = true →
      (∀ E' : TViewN (PcsPV (V × Wv)) EF → Bool,
        tsumN NR 2 (fun α β r t => indB (genB β && E' (realVN off tabs tv ptm (pcsZ (efOf c2)) α β r t))) ≤
          tsumN NR 2 (fun α β r t => indB (genB β && E' (simVN off ptm chainBus (fun _ => false) chainPar 3 ptm (psimZ (efOf c2)) α β r t))) + Q4 * (NR * (Q4 ^ 2 * M)) +
            Q4 * (Q4 * (Q4 ^ 2 * 0))) ∧
      (∀ E' : TViewN (PcsPV (V × Wv)) EF → Bool,
        tsumN NR 2 (fun α β r t => indB (genB β && E' (simVN off ptm chainBus (fun _ => false) chainPar 3 ptm (psimZ (efOf c2)) α β r t))) ≤
          tsumN NR 2 (fun α β r t => indB (genB β && E' (realVN off tabs tv ptm (pcsZ (efOf c2)) α β r t))) + Q4 * (NR * (Q4 ^ 2 * M)) +
            Q4 * (Q4 * (Q4 ^ 2 * 0))) := fun c2 hg => by
    have hgz := (genB_iff _).1 hg
    have hpcs := wit_pcsX (heap := blank.heap) (ζ := efOf c2) off sc sms sw (rfl : C.h = 2 ^ 10) hlen hWh (by omega) hPg qv
      wm wc ww wp hS10 hS9 hSP hsz10 hsz9 hszP (generic_ofF_ne hgz) (mz_generic hgz) fri (mz_generic hgα) (generic_apow_ne hgα) hncw NR2 Rb Ro
    rw [wNR_zeta off blank.hd blank.stk blank.heap.length blank.heap W C Mm Wt tP S10 S9 SP (efOf c2) EF.zero qv wm wc ww wp ncw] at hpcs
    exact ⟨fun E' => (wit_transcriptG off NR 0 (pcsZ (efOf c2)) (psimZ (efOf c2)) hbal hun hpcs E').1,
      fun E' => (wit_transcriptG off NR 0 (pcsZ (efOf c2)) (psimZ (efOf c2)) hbal hun hpcs E').2⟩
  have hsm : ∀ (N : Nat) (f : Nat → Nat × Nat × Nat × (Nat → Tup) → Nat),
      sm (fun x => sumTo N (fun i => f i x)) = sumTo N (fun i => sm (f i)) := fun N f => by
    show sumTo NS1 (fun σ1 => sumTo NS2 (fun σ2 => sumTo NR (fun r => sumN 2 (fun t =>
      sumTo N (fun i => f i (σ1, σ2, r, t)))))) = _
    rw [sumTo_congr _ (fun σ1 _ => sm_exch (NS := NS2) (NR := NR) (m := 2) (N := N)
      (fun i σ2 r t => f i (σ1, σ2, r, t)))]
    exact sumTo_exch _ N NS1
  exact fs_zk2 (K1 := Q4 * Q4) (K2 := Q4) (n1 := n1) (n2 := n2) (Nat.mul_pos Q4_pos Q4_pos) Q4_pos sm hsm m1 m2
    (fun x => hr1 _ _) (fun _ x => hr2 _ _) (fun _ _ x => Com1 d1 x.1) (fun _ _ x => Com2 d2 x.2.1) rv sv gd
    (fun F => pc_two (fun c2 α β r t => realVN off tabs tv ptm (pcsZ (efOf c2)) α β r t)
      (fun c2 α β r t => simVN off ptm chainBus (fun _ => false) chainPar 3 ptm (psimZ (efOf c2)) α β r t)
      (fun c2 => genB (efOf c2)) (fun c2 α β r t => realVN_cases _ _ _ _ _ α β r t)
      (fun c2 α β r t => simVN_some _ _ _ _ _ _ _ _ α β r t) (fun c2 hg => (hb c2 hg).1) (fun c2 hg => (hb c2 hg).2)
      Com1 hc1 Com2 hc2 main1 main2 d1 d2 F) E
set_option maxRecDepth 100000 in
theorem cNR_zeta (off : EF → String → EF) (hd0 stk0 ctr0 n nilA : Nat) (heap : List Cell) (N W : Nat) (roots : List Nat)
    (C Mm Wt : Table) (tbM tbC tpP tpS : Nat) (SM SC S9 SP SS : List F) (ζ ζ' : EF)
    (qv : EF → EF → List EF → F → List F → List F → List EF) (wm wc ww wp wsg : List (EF → EF → List F)) (ncw : Nat) :
    cNR off hd0 stk0 ctr0 n nilA heap N W roots C Mm Wt tbM tbC tpP tpS SM SC S9 SP SS ζ qv wm wc ww wp wsg ncw =
      cNR off hd0 stk0 ctr0 n nilA heap N W roots C Mm Wt tbM tbC tpP tpS SM SC S9 SP SS ζ' qv wm wc ww wp wsg ncw := by
  have ht : ((cTs off hd0 stk0 ctr0 n nilA heap N W roots C Mm Wt tbM tbC tpP tpS SM SC S9 SP SS ζ qv wm wc ww wp wsg).map Prod.fst).map
        (fun T => (T.tg.length, T.cs.length, T.h)) =
      ((cTs off hd0 stk0 ctr0 n nilA heap N W roots C Mm Wt tbM tbC tpP tpS SM SC S9 SP SS ζ' qv wm wc ww wp wsg).map Prod.fst).map
        (fun T => (T.tg.length, T.cs.length, T.h)) := by
    simp only [cTs, bbTab, airQTabG, List.map_cons, List.map_nil, List.length_map]
  have hn : ((cGroups tbM tbC tpP tpS SM SC S9 SP SS ζ qv).map QGroup.ext).map MGroup.n =
      ((cGroups tbM tbC tpP tpS SM SC S9 SP SS ζ' qv).map QGroup.ext).map MGroup.n := rfl
  have hd : ((cGroups tbM tbC tpP tpS SM SC S9 SP SS ζ qv).map QGroup.ext).map MGroup.dom =
      ((cGroups tbM tbC tpP tpS SM SC S9 SP SS ζ' qv).map QGroup.ext).map MGroup.dom := rfl
  unfold cNR friN1 friN2
  rw [mtotal_congr _ _ _ hn, tabsCr_congr _ _ ht, traceCw_congr ncw _ _ hd, tabsCw_congr ncw _ _ ht]

set_option maxRecDepth 100000 in
/-- **The composed proof under Fiat–Shamir over two rounds**, as
    `sud_fs2`: the LogUp challenges hashed from the first commitment, `ζ`
    from the second, both unopened in the view, summed over generic `ζ`. -/
theorem comp_fs2 {V Wv D1 D2 : Type} (off : EF → String → EF) {R Lm : Nat} (hR : R ≤ 20) {shp : BT} {Ps : List Term}
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
    (wm wc ww wp wsg : List (EF → EF → List F))
    (hSM : ∀ x ∈ SM, x ∉ cosetL 1 (bbGen (tbM + 1)) (2 ^ (tbM + 1)))
    (hSC : ∀ x ∈ SC, x ∉ cosetL 1 (bbGen (tbC + 1)) (2 ^ (tbC + 1)))
    (hS9 : ∀ x ∈ S9, x ∉ cosetL 1 (bbGen 9) (2 ^ 9))
    (hSP : ∀ x ∈ SP, x ∉ cosetL 1 (bbGen (tpP + 1)) (2 ^ (tpP + 1)))
    (hSS : ∀ x ∈ SS, x ∉ cosetL 1 (bbGen (tpS + 1)) (2 ^ (tpS + 1)))
    (hszM : 2 * SM.length + 8 ≤ 2 ^ (tbM + 1)) (hszC : 2 * SC.length + 8 ≤ 2 ^ (tbC + 1))
    (hsz9 : 2 * S9.length + 8 ≤ 2 ^ 9) (hszP : 2 * SP.length + 8 ≤ 2 ^ (tpP + 1))
    (hszS : 2 * SS.length + 8 ≤ 2 ^ (tpS + 1)) {ncw : Nat} {αb : EF} (fri : EF → EF → List (EF → EF) → V) (hncw : 4 ≤ ncw) (hgα : Generic αb)
    (NR2 : Nat) (Rb : EF → EF → Nat → List (EF → EF)) (Ro : EF → EF → Nat → Wv)
    {NS1 NS2 n1 n2 : Nat} (Com1 : D1 → Nat → Nat) (hc1 : ComHides NS1 Com1) (hr1 : ∀ d σ, Com1 d σ < n1)
    (Com2 : D2 → Nat → Nat) (hc2 : ComHides NS2 Com2) (hr2 : ∀ d σ, Com2 d σ < n2)
    (main1 : (Nat → Tup) → Nat → D1) (main2 : Nat → (Nat → Tup) → Nat → D2) (d1 : D1) (d2 : D2)
    (E : Nat → Nat → Nat → Nat → TViewN (PcsPV (V × Wv)) (EF × EF) → Bool) :
    let m := blankM shp W Ps
    let roots := blankRoots shp W Ps
    let N := BT.nleaves shp
    let C := cpuTableC A row e Ps.length roots (2 ^ R)
    let Pg := progTableC m.heap N W
    let Wt := witTable A N W
    let Mm := memTableC A (cpuAirC m.hd m.stk m.heap.length roots.length m.stk) (progAirC m.heap N W)
      (witAir N W) C Pg Wt
    let NR0 := cNR off m.hd m.stk m.heap.length roots.length m.stk m.heap N W roots C Mm Wt tbM tbC tpP tpS
      SM SC S9 SP SS EF.zero qv wm wc ww wp wsg ncw
    let pcsZ := fun (ζ : EF) t α β r => cPcs off m.hd m.stk m.heap.length roots.length m.stk m.heap N W roots C Mm Wt tbM tbC tpP tpS
      SM SC S9 SP SS ζ qv wm wc ww wp wsg ncw αb
      (friX fri Rb Ro (r / NR0)) t α β (r % NR0)
    let psimZ := fun (ζ : EF) α β v r => cPsim off m.hd m.stk m.heap.length roots.length m.stk m.heap N W roots C Mm Wt tbM tbC tpP tpS
      SM SC S9 SP SS ζ qv wm wc ww wp wsg ncw αb
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
    let sm := fun (g : Nat × Nat × Nat × (Nat → Tup) → Nat) =>
      sumTo NS1 (fun σ1 => sumTo NS2 (fun σ2 => sumTo NR (fun r => sumN 2 (fun t => g (σ1, σ2, r, t)))))
    let m1 := fun (x : Nat × Nat × Nat × (Nat → Tup)) => Com1 (main1 x.2.2.2 x.2.2.1) x.1
    let m2 := fun (c1 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) => Com2 (main2 c1 x.2.2.2 x.2.2.1) x.2.1
    let rv := fun (c1 c2 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      realVN off tabs tv pb (pcsZ (efOf c2)) (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2
    let sv := fun (c1 c2 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      simVN off pb chainBus (fun _ => false) chainPar 3 ptm (psimZ (efOf c2)) (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2
    let gd := fun (c1 c2 : Nat) => genB (efOf (c1 % Q4)) && genB (efOf c2)
    let err := Q4 * (NR * (Q4 ^ 2 * M)) + Q4 * (Q4 * (Q4 ^ 2 * 0))
    (Q4 * Q4) * (Q4 * sumTo ((Q4 * Q4) ^ n1) (fun H1 => sumTo (Q4 ^ n2) (fun H2 => sm (fun x =>
      indB (gd (rget (Q4 * Q4) (m1 x) H1) (rget Q4 (m2 (rget (Q4 * Q4) (m1 x) H1) x) H2) &&
        E H1 H2 (m1 x) (m2 (rget (Q4 * Q4) (m1 x) H1) x)
          (rv (rget (Q4 * Q4) (m1 x) H1) (rget Q4 (m2 (rget (Q4 * Q4) (m1 x) H1) x) H2) x)))))) ≤
    sumTo ((Q4 * Q4) ^ n1) (fun H1 => sumTo (Q4 ^ n2) (fun H2 => sumTo (Q4 * Q4) (fun c1 => sumTo Q4 (fun c2 =>
      sm (fun x => indB (gd c1 c2 && E (rset (Q4 * Q4) (Com1 d1 x.1) H1 c1) (rset Q4 (Com2 d2 x.2.1) H2 c2)
        (Com1 d1 x.1) (Com2 d2 x.2.1) (sv c1 c2 x))))))) +
      (Q4 * Q4) ^ n1 * (Q4 ^ n2 * (Q4 * (NS1 * (NS2 * err)))) := by
  intro m roots N C Pg Wt Mm NR0 pcsZ psimZ NR tabs tv pb ptm M sm m1 m2 rv sv gd err
  obtain ⟨hbal, hun⟩ := comp_honest_zk hR hrl hr hA hlen hLm hK hNW
  obtain ⟨sc, sms, sw, hWh, _⟩ := comp_run_sats hR hrl hr hA hlen hLm hK hNW
  obtain ⟨p1, p2, s1, s2⟩ := comp_pub_heights hR hrl hA hlen hLm hK
  rw [← htP] at p1 p2
  rw [← htS] at s1 s2
  have hM : Mm.h = 2 ^ (tbM + 1) := by rw [htM]; exact hlen
  have hC : C.h = 2 ^ (tbC + 1) := by rw [htC]; rfl
  have hb : ∀ c2, genB (efOf c2) = true →
      (∀ E' : TViewN (PcsPV (V × Wv)) (EF × EF) → Bool,
        tsumN NR 2 (fun α β r t => indB (genB β && E' (realVN off tabs tv pb (pcsZ (efOf c2)) α β r t))) ≤
          tsumN NR 2 (fun α β r t => indB (genB β && E' (simVN off pb chainBus (fun _ => false) chainPar 3 ptm (psimZ (efOf c2)) α β r t))) + Q4 * (NR * (Q4 ^ 2 * M)) +
            Q4 * (Q4 * (Q4 ^ 2 * 0))) ∧
      (∀ E' : TViewN (PcsPV (V × Wv)) (EF × EF) → Bool,
        tsumN NR 2 (fun α β r t => indB (genB β && E' (simVN off pb chainBus (fun _ => false) chainPar 3 ptm (psimZ (efOf c2)) α β r t))) ≤
          tsumN NR 2 (fun α β r t => indB (genB β && E' (realVN off tabs tv pb (pcsZ (efOf c2)) α β r t))) + Q4 * (NR * (Q4 ^ 2 * M)) +
            Q4 * (Q4 * (Q4 ^ 2 * 0))) := fun c2 hg => by
    have hgz := (genB_iff _).1 hg
    have hpcs := comp_pcsX (heap := m.heap) (ζ := efOf c2) (roots := roots) off sc sms sw (by omega) (by omega) (by omega) (by omega)
      hM hC hWh p2 s2 qv wm wc ww wp wsg hSM hSC hS9 hSP hSS hszM hszC hsz9 hszP hszS (generic_ofF_ne hgz) (mz_generic hgz) fri (mz_generic hgα) (generic_apow_ne hgα) hncw NR2 Rb Ro
    rw [cNR_zeta off m.hd m.stk m.heap.length roots.length m.stk m.heap N W roots C Mm Wt tbM tbC tpP tpS
      SM SC S9 SP SS (efOf c2) EF.zero qv wm wc ww wp wsg ncw] at hpcs
    exact ⟨fun E' => (comp_transcriptG off NR 0 (pcsZ (efOf c2)) (psimZ (efOf c2)) hbal hun hpcs E').1,
      fun E' => (comp_transcriptG off NR 0 (pcsZ (efOf c2)) (psimZ (efOf c2)) hbal hun hpcs E').2⟩
  have hsm : ∀ (N : Nat) (f : Nat → Nat × Nat × Nat × (Nat → Tup) → Nat),
      sm (fun x => sumTo N (fun i => f i x)) = sumTo N (fun i => sm (f i)) := fun N f => by
    show sumTo NS1 (fun σ1 => sumTo NS2 (fun σ2 => sumTo NR (fun r => sumN 2 (fun t =>
      sumTo N (fun i => f i (σ1, σ2, r, t)))))) = _
    rw [sumTo_congr _ (fun σ1 _ => sm_exch (NS := NS2) (NR := NR) (m := 2) (N := N)
      (fun i σ2 r t => f i (σ1, σ2, r, t)))]
    exact sumTo_exch _ N NS1
  exact fs_zk2 (K1 := Q4 * Q4) (K2 := Q4) (n1 := n1) (n2 := n2) (Nat.mul_pos Q4_pos Q4_pos) Q4_pos sm hsm m1 m2
    (fun x => hr1 _ _) (fun _ x => hr2 _ _) (fun _ _ x => Com1 d1 x.1) (fun _ _ x => Com2 d2 x.2.1) rv sv gd
    (fun F => pc_two (fun c2 α β r t => realVN off tabs tv pb (pcsZ (efOf c2)) α β r t)
      (fun c2 α β r t => simVN off pb chainBus (fun _ => false) chainPar 3 ptm (psimZ (efOf c2)) α β r t)
      (fun c2 => genB (efOf c2)) (fun c2 α β r t => realVN_cases _ _ _ _ _ α β r t)
      (fun c2 α β r t => simVN_some _ _ _ _ _ _ _ _ α β r t) (fun c2 hg => (hb c2 hg).1) (fun c2 hg => (hb c2 hg).2)
      Com1 hc1 Com2 hc2 main1 main2 d1 d2 F) E
end Circuit
