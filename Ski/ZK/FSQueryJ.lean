import Ski.ZK.CompJHiding
import Ski.ZK.FSQueryInst

/-!
# The proof with jets over four Fiat–Shamir rounds, the query points hashed

`comp_fs_open4`'s construction for the circuit with jets
(`compJ_fs_open4`): its PCS is `compJ_pcs`'s, its run's facts
`compJ_run_facts`'s, its transcript `compJ_transcriptG`'s.  Scope and
assumptions as `comp_fs_open4`'s (`Ski/ZK/FSQueryInst.lean`).
-/

namespace Circuit

open ZKF B Air JetTable Compose CompM Stmt Mach Wit

-- ---------------------------------------------------------------------------
-- The PCS's shape: what it reads of the query points, `ζ` and the weights
-- ---------------------------------------------------------------------------

def jSsT (SM SC S9 SPo SI ST SH SR SP SS : List F) : List (List F) := [SM, SC, S9, SPo, SI, ST, SH, SR, SP, SS]

def jSsC (tbM tbC tbPo tbI tpT tpH tpR tpP tpS : Nat) (SM SC S9 SPo SI ST SH SR SP SS : List F) : List (List F) :=
  List.replicate ((bbCs tbM 1 (2 ^ (tbM + 1) - 1)).length + 1) SM ++
    (List.replicate ((bbCs tbC 1 (2 ^ (tbC + 1) - 1)).length + 1) SC ++
      (List.replicate ((bbCs 8 1 (2 ^ (8 + 1) - 1)).length + 1) S9 ++
        (List.replicate ((bbCs tbPo 1 (2 ^ (tbPo + 1) - 1)).length + 1) SPo ++
          (List.replicate ((bbCs tbI 1 (2 ^ (tbI + 1) - 1)).length + 1) SI ++
            (List.replicate ((bbCs tpT 1 (2 ^ (tpT + 1) - 1)).length + 1) ST ++
              (List.replicate ((bbCs tpH 1 (2 ^ (tpH + 1) - 1)).length + 1) SH ++
                (List.replicate ((bbCs tpR 1 (2 ^ (tpR + 1) - 1)).length + 1) SR ++
                  (List.replicate ((bbCs tpP 1 (2 ^ (tpP + 1) - 1)).length + 1) SP ++
                    (List.replicate ((bbCs tpS 1 (2 ^ (tpS + 1) - 1)).length + 1) SS ++ [])))))))))

section
variable (off : EF → String → EF) (hd0 stk0 ctr0 n nilA : Nat) (heap : List Cell) (N W : Nat)
  (segRoots : List Nat) (roots : List (Nat × Nat)) (jets : List Air.Jet) (C Mm Wt Rt Hd Tm Po Iw : Table)
  (tbM tbC tbPo tbI tpT tpH tpR tpP tpS : Nat)

set_option maxRecDepth 100000 in
theorem compJ_SsT (SM SC S9 SPo SI ST SH SR SP SS : List F) (ζ : EF)
    (qv : EF → EF → List EF → F → List F → List F → List EF)
    (wm wc ww wpo wi wt wh wr wp wsg : List (EF → EF → List F)) :
    ((jTs off hd0 stk0 ctr0 n nilA heap N W segRoots roots jets C Mm Wt Rt Hd Tm Po Iw tbM tbC tbPo tbI tpT tpH tpR
      tpP tpS SM SC S9 SPo SI ST SH SR SP SS ζ qv wm wc ww wpo wi wt wh wr wp wsg).map Prod.fst).map (·.S) =
      jSsT SM SC S9 SPo SI ST SH SR SP SS := by
  simp only [jTs, bbTab, airQTabG, List.map_cons, List.map_nil, jSsT]

set_option maxRecDepth 100000 in
theorem compJ_SsC (SM SC S9 SPo SI ST SH SR SP SS : List F) (ζ : EF)
    (qv : EF → EF → List EF → F → List F → List F → List EF)
    (wm wc ww wpo wi wt wh wr wp wsg : List (EF → EF → List F)) (ncw : Nat) :
    (tabsInfo ncw ((jTs off hd0 stk0 ctr0 n nilA heap N W segRoots roots jets C Mm Wt Rt Hd Tm Po Iw tbM tbC tbPo tbI
      tpT tpH tpR tpP tpS SM SC S9 SPo SI ST SH SR SP SS ζ qv wm wc ww wpo wi wt wh wr wp wsg).map Prod.fst)).map (·.S) =
      jSsC tbM tbC tbPo tbI tpT tpH tpR tpP tpS SM SC S9 SPo SI ST SH SR SP SS := by
  simp only [jTs, bbTab, airQTabG, tabsInfo, tInfo, List.map_cons, List.map_nil, List.map_append,
    List.map_replicate, jSsC]

set_option maxRecDepth 100000 in
/-- **The PCS with jets' shape reads neither `ζ` nor the weights**, only
    their lengths. -/
theorem compJ_same_w (SM SC S9 SPo SI ST SH SR SP SS : List F) (ζ ζ' : EF)
    (qv : EF → EF → List EF → F → List F → List F → List EF)
    (wm wc ww wpo wi wt wh wr wp wsg wm' wc' ww' wpo' wi' wt' wh' wr' wp' wsg' : List (EF → EF → List F)) (ncw : Nat)
    (hwm : wm.length = wm'.length) (hwc : wc.length = wc'.length) (hww : ww.length = ww'.length)
    (hwpo : wpo.length = wpo'.length) (hwi : wi.length = wi'.length) (hwt : wt.length = wt'.length)
    (hwh : wh.length = wh'.length) (hwr : wr.length = wr'.length) (hwp : wp.length = wp'.length)
    (hwsg : wsg.length = wsg'.length) :
    SameShape (jGroups tbM tbC tbPo tbI tpT tpH tpR tpP tpS SM SC S9 SPo SI ST SH SR SP SS ζ qv)
      (jGroups tbM tbC tbPo tbI tpT tpH tpR tpP tpS SM SC S9 SPo SI ST SH SR SP SS ζ' qv)
      (jKs hd0 stk0 ctr0 n nilA heap N W segRoots roots jets)
      ((jTs off hd0 stk0 ctr0 n nilA heap N W segRoots roots jets C Mm Wt Rt Hd Tm Po Iw tbM tbC tbPo tbI tpT tpH tpR
        tpP tpS SM SC S9 SPo SI ST SH SR SP SS ζ qv wm wc ww wpo wi wt wh wr wp wsg).map Prod.fst)
      ((jTs off hd0 stk0 ctr0 n nilA heap N W segRoots roots jets C Mm Wt Rt Hd Tm Po Iw tbM tbC tbPo tbI tpT tpH tpR
        tpP tpS SM SC S9 SPo SI ST SH SR SP SS ζ' qv wm' wc' ww' wpo' wi' wt' wh' wr' wp' wsg').map Prod.fst) ncw where
  trn := rfl
  dom := rfl
  S := rfl
  shape := by
    simp only [jTs, bbTab, airQTabG, tShape, List.map_cons, List.map_nil, List.length_map]
    rw [hwm, hwc, hww, hwpo, hwi, hwt, hwh, hwr, hwp, hwsg]
  tS := by simp only [jTs, bbTab, airQTabG, List.map_cons, List.map_nil]
  iS := by simp only [jTs, bbTab, airQTabG, tabsInfo, tInfo, List.map_cons, List.map_nil, List.map_append,
    List.map_replicate]

set_option maxRecDepth 100000 in
theorem compJ_data_q (SM SC S9 SPo SI ST SH SR SP SS SM' SC' S9' SPo' SI' ST' SH' SR' SP' SS' : List F) (ζ ζ' : EF)
    (qv : EF → EF → List EF → F → List F → List F → List EF)
    (wm wc ww wpo wi wt wh wr wp wsg : List (EF → EF → List F)) (t : Nat → Tup) (α β : EF) (ms : List F)
    (h : Aborts (prefixOf α (off β))
      β (jTabs hd0 stk0 ctr0 n nilA heap N W segRoots roots jets C Mm Wt Rt Hd Tm Po Iw t) = false) :
    (jTs off hd0 stk0 ctr0 n nilA heap N W segRoots roots jets C Mm Wt Rt Hd Tm Po Iw tbM tbC tbPo tbI tpT tpH tpR tpP
      tpS SM SC S9 SPo SI ST SH SR SP SS ζ qv wm wc ww wpo wi wt wh wr wp wsg).map (fun p => p.2 t α β ms) =
      (jTs off hd0 stk0 ctr0 n nilA heap N W segRoots roots jets C Mm Wt Rt Hd Tm Po Iw tbM tbC tbPo tbI tpT tpH tpR
        tpP tpS SM' SC' S9' SPo' SI' ST' SH' SR' SP' SS' ζ' qv wm wc ww wpo wi wt wh wr wp wsg).map
        (fun p => p.2 t α β ms) := by
  have hg : ∀ tss rs, mpolysMulti ((jGroups tbM tbC tbPo tbI tpT tpH tpR tpP tpS SM SC S9 SPo SI ST SH SR SP SS ζ
      qv).map QGroup.ext) tss rs =
      mpolysMulti ((jGroups tbM tbC tbPo tbI tpT tpH tpR tpP tpS SM' SC' S9' SPo' SI' ST' SH' SR' SP' SS' ζ'
        qv).map QGroup.ext) tss rs := fun tss rs =>
    mpolysMulti_congr _ _ _ _ rfl
  simp only [jTs, bbData, List.map_cons, List.map_nil, h, if_true, hg]

set_option maxRecDepth 100000 in
/-- **The PCS with jets' data shape reads neither the query points, nor
    `ζ`, nor the weights beyond their lengths.** -/
theorem compJ_same_d (SM SC S9 SPo SI ST SH SR SP SS SM' SC' S9' SPo' SI' ST' SH' SR' SP' SS' : List F) (ζ ζ' : EF)
    (qv : EF → EF → List EF → F → List F → List F → List EF)
    (wm wc ww wpo wi wt wh wr wp wsg wm' wc' ww' wpo' wi' wt' wh' wr' wp' wsg' : List (EF → EF → List F))
    (hwm : wm.length = wm'.length) (hwc : wc.length = wc'.length) (hww : ww.length = ww'.length)
    (hwpo : wpo.length = wpo'.length) (hwi : wi.length = wi'.length) (hwt : wt.length = wt'.length)
    (hwh : wh.length = wh'.length) (hwr : wr.length = wr'.length) (hwp : wp.length = wp'.length)
    (hwsg : wsg.length = wsg'.length) :
    SameData (jGroups tbM tbC tbPo tbI tpT tpH tpR tpP tpS SM SC S9 SPo SI ST SH SR SP SS ζ qv)
      (jGroups tbM tbC tbPo tbI tpT tpH tpR tpP tpS SM' SC' S9' SPo' SI' ST' SH' SR' SP' SS' ζ' qv)
      ((jTs off hd0 stk0 ctr0 n nilA heap N W segRoots roots jets C Mm Wt Rt Hd Tm Po Iw tbM tbC tbPo tbI tpT tpH tpR
        tpP tpS SM SC S9 SPo SI ST SH SR SP SS ζ qv wm wc ww wpo wi wt wh wr wp wsg).map Prod.fst)
      ((jTs off hd0 stk0 ctr0 n nilA heap N W segRoots roots jets C Mm Wt Rt Hd Tm Po Iw tbM tbC tbPo tbI tpT tpH tpR
        tpP tpS SM' SC' S9' SPo' SI' ST' SH' SR' SP' SS' ζ' qv wm' wc' ww' wpo' wi' wt' wh' wr' wp' wsg').map
        Prod.fst) where
  trn := rfl
  dom := rfl
  shape := by
    simp only [jTs, bbTab, airQTabG, tShape, List.map_cons, List.map_nil, List.length_map]
    rw [hwm, hwc, hww, hwpo, hwi, hwt, hwh, hwr, hwp, hwsg]

theorem compJCols_main (t : Nat → Tup) (α β α' β' : EF) :
    ∀ k ∈ [0, 2, 4, 6, 8, 10, 12, 14, 16, 18],
      (jCols off hd0 stk0 ctr0 n nilA heap N W segRoots roots jets C Mm Wt Rt Hd Tm Po Iw t α β).getD k [] =
        (jCols off hd0 stk0 ctr0 n nilA heap N W segRoots roots jets C Mm Wt Rt Hd Tm Po Iw t α' β').getD k [] := by
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [jCols, List.getD_cons_zero, List.getD_cons_succ]

end

set_option maxRecDepth 100000 in
/-- **The PCS with jets, FRI's randomness split off, hides exactly**:
    `compJ_pcs` at every split (`comp_pcsX`). -/
theorem compJ_pcsX {V Wv : Type} (off : EF → String → EF) {hd0 stk0 ctr0 n nilA : Nat} {heap : List Cell} {N W : Nat}
    {segRoots : List Nat} {roots : List (Nat × Nat)} {jets : List Air.Jet} {C Mm Wt Rt Hd Tm Po Iw : Table}
    (hsC : Sat (cpuAirCJ hd0 stk0 ctr0 n nilA) C) (hsM : Sat memAirC Mm) (hsW : Sat (witAir N W) Wt)
    (hsPo : Sat popAirCJ Po) (hsI : Sat instwAirCJ Iw) (hsT : Sat (tmplAirCJ jets) Tm)
    (hsH : Sat (hdrAirCJ jets) Hd) (hsR : Sat (rootsAirCJ roots) Rt)
    {tbM tbC tbPo tbI tpT tpH tpR tpP tpS : Nat} (hbM : tbM ≤ 24) (hbC : tbC ≤ 24) (hbPo : tbPo ≤ 24)
    (hbI : tbI ≤ 24) (hbT : tpT ≤ 24) (hbH : tpH ≤ 24) (hbR : tpR ≤ 24) (hbP : tpP ≤ 24) (hbS : tpS ≤ 24)
    (hM : Mm.h = 2 ^ (tbM + 1)) (hC : C.h = 2 ^ (tbC + 1)) (hW : Wt.h = 2 ^ 9)
    (hPo : Po.h = 2 ^ (tbPo + 1)) (hI : Iw.h = 2 ^ (tbI + 1)) (hT : Tm.h = 2 ^ (tpT + 1))
    (hH : Hd.h = 2 ^ (tpH + 1)) (hR : Rt.h = 2 ^ (tpR + 1))
    (hPg : (progTableC heap N W).h = 2 ^ (tpP + 1)) (hSg : (segsPub segRoots).h = 2 ^ (tpS + 1))
    {SM SC S9 SPo SI ST SH SR SP SS : List F} {ζ : EF} (qv : EF → EF → List EF → F → List F → List F → List EF)
    (wm wc ww wpo wi wt wh wr wp wsg : List (EF → EF → List F))
    (hSM : ∀ x ∈ SM, x ∉ cosetL 1 (bbGen (tbM + 1)) (2 ^ (tbM + 1)))
    (hSC : ∀ x ∈ SC, x ∉ cosetL 1 (bbGen (tbC + 1)) (2 ^ (tbC + 1)))
    (hS9 : ∀ x ∈ S9, x ∉ cosetL 1 (bbGen 9) (2 ^ 9))
    (hSPo : ∀ x ∈ SPo, x ∉ cosetL 1 (bbGen (tbPo + 1)) (2 ^ (tbPo + 1)))
    (hSI : ∀ x ∈ SI, x ∉ cosetL 1 (bbGen (tbI + 1)) (2 ^ (tbI + 1)))
    (hST : ∀ x ∈ ST, x ∉ cosetL 1 (bbGen (tpT + 1)) (2 ^ (tpT + 1)))
    (hSH : ∀ x ∈ SH, x ∉ cosetL 1 (bbGen (tpH + 1)) (2 ^ (tpH + 1)))
    (hSR : ∀ x ∈ SR, x ∉ cosetL 1 (bbGen (tpR + 1)) (2 ^ (tpR + 1)))
    (hSP : ∀ x ∈ SP, x ∉ cosetL 1 (bbGen (tpP + 1)) (2 ^ (tpP + 1)))
    (hSS : ∀ x ∈ SS, x ∉ cosetL 1 (bbGen (tpS + 1)) (2 ^ (tpS + 1)))
    (hszM : 2 * SM.length + 8 ≤ 2 ^ (tbM + 1)) (hszC : 2 * SC.length + 8 ≤ 2 ^ (tbC + 1))
    (hsz9 : 2 * S9.length + 8 ≤ 2 ^ 9) (hszPo : 2 * SPo.length + 8 ≤ 2 ^ (tbPo + 1))
    (hszI : 2 * SI.length + 8 ≤ 2 ^ (tbI + 1)) (hszT : 2 * ST.length + 8 ≤ 2 ^ (tpT + 1))
    (hszH : 2 * SH.length + 8 ≤ 2 ^ (tpH + 1)) (hszR : 2 * SR.length + 8 ≤ 2 ^ (tpR + 1))
    (hszP : 2 * SP.length + 8 ≤ 2 ^ (tpP + 1)) (hszS : 2 * SS.length + 8 ≤ 2 ^ (tpS + 1))
    (hζ : ∀ x : F, EF.ofF x ≠ ζ) (hdet : (mz ζ).det ≠ 0) {ncw : Nat} {αb : EF} (fri : EF → EF → List (EF → EF) → V)
    (hdb : (mz αb).det ≠ 0) (haw : ∀ w, apow αb w ≠ EF.zero) (hncw : 4 ≤ ncw)
    (NR2 : Nat) (Rb : EF → EF → Nat → List (EF → EF)) (Ro : EF → EF → Nat → Wv) :
    let NR := jNR off hd0 stk0 ctr0 n nilA heap N W segRoots roots jets C Mm Wt Rt Hd Tm Po Iw tbM tbC tbPo tbI tpT tpH
      tpR tpP tpS SM SC S9 SPo SI ST SH SR SP SS ζ qv wm wc ww wpo wi wt wh wr wp wsg ncw
    PCSCloseN off (NR * NR2)
      (fun pre β t => compJViewN pre β hd0 stk0 ctr0 n nilA N W roots jets C Mm Wt Rt Hd Tm Po Iw t)
      (fun t α β r => jPcs off hd0 stk0 ctr0 n nilA heap N W segRoots roots jets C Mm Wt Rt Hd Tm Po Iw tbM tbC tbPo
        tbI tpT tpH tpR tpP tpS SM SC S9 SPo SI ST SH SR SP SS ζ qv wm wc ww wpo wi wt wh wr wp wsg ncw αb
        (friX fri Rb Ro (r / NR)) t α β (r % NR))
      (fun α β v r => jPsim off hd0 stk0 ctr0 n nilA heap N W segRoots roots jets C Mm Wt Rt Hd Tm Po Iw tbM tbC tbPo
        tbI tpT tpH tpR tpP tpS SM SC S9 SPo SI ST SH SR SP SS ζ qv wm wc ww wpo wi wt wh wr wp wsg ncw αb
        (friX fri Rb Ro (r / NR)) α β v (r % NR)) 0 :=
  PCSCloseN.family (pcs := fun δ => jPcs off hd0 stk0 ctr0 n nilA heap N W segRoots roots jets C Mm Wt Rt Hd Tm Po Iw
      tbM tbC tbPo tbI tpT tpH tpR tpP tpS SM SC S9 SPo SI ST SH SR SP SS ζ qv wm wc ww wpo wi wt wh wr wp wsg ncw αb
      (friX fri Rb Ro δ))
    (psim := fun δ => jPsim off hd0 stk0 ctr0 n nilA heap N W segRoots roots jets C Mm Wt Rt Hd Tm Po Iw tbM tbC tbPo
      tbI tpT tpH tpR tpP tpS SM SC S9 SPo SI ST SH SR SP SS ζ qv wm wc ww wpo wi wt wh wr wp wsg ncw αb
      (friX fri Rb Ro δ))
    (fun δ => by apply compJ_pcs (fri := friX fri Rb Ro δ) <;> assumption)

set_option maxRecDepth 100000 in
/-- **The proof with jets over four Fiat–Shamir rounds, the query points
    hashed**: `comp_fs_open4` for the circuit with jets.  The run is an
    accepting run with jets (`compJ_complete_log`'s hypotheses), its
    provider tables fitting `2^24` rows, POP and INSTW within their
    budgets `2^Lp`, `2^Li`; the PCS is `compJ_pcs`'s, over twenty trace
    groups and ten quotient tables.  Assumed as in `comp_fs_open4`: at
    every `c4`, the decoding admissible (off the trace domains, few
    enough points) and each commitment hiding given its openings and
    opening proof there; the fourth table's input the commitments'
    transcript and every opening at `ζ`; the FRI challenge hashed from
    `c4`, the draws where it fails at most `B4` of the `K4`. -/
theorem compJ_fs_open4 {V Wv P1 P2 P3 : Type} (off : EF → String → EF) {R Lm Lp Li : Nat} (hR : R ≤ 20)
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
    {NS1 NS2 NS3 n1 n2 n3 : Nat}
    (Com1 : List (List (List F)) → Nat → Nat) (Pf1 : Nat → List (List (List F)) → Nat → P1) (hc1 : ComHides NS1 Com1)
    (hp1 : ∀ c4, ComPfHides NS1 Com1 (Pf1 c4) (opF ((jGroups tbM tbC tbPo tbI tpT tpH tpR tpP tpS (SM c4) (SC c4) (S9 c4) (SPo c4) (SI c4) (ST c4) (SH c4) (SR c4) (SP c4) (SS c4) EF.zero qv).map (·.base.S)) [0, 2, 4, 6, 8, 10, 12, 14, 16, 18]))
    (hr1 : ∀ d σ, Com1 d σ < n1) (d1 : List (List (List F)))
    (Com2 : List (List (List F)) → Nat → Nat) (Pf2 : Nat → List (List (List F)) → Nat → P2) (hc2 : ComHides NS2 Com2)
    (hp2 : ∀ c4, ComPfHides NS2 Com2 (Pf2 c4) (opF ((jGroups tbM tbC tbPo tbI tpT tpH tpR tpP tpS (SM c4) (SC c4) (S9 c4) (SPo c4) (SI c4) (ST c4) (SH c4) (SR c4) (SP c4) (SS c4) EF.zero qv).map (·.base.S)) [1, 3, 5, 7, 9, 11, 13, 15, 17, 19]))
    (hr2 : ∀ d σ, Com2 d σ < n2) (d2 : List (List (List F)))
    (Com3 : List (List (List (List F))) × List (List (List F)) → Nat → Nat)
    (Pf3 : Nat → List (List (List (List F))) × List (List (List F)) → Nat → P3) (hc3 : ComHides NS3 Com3)
    (hp3 : ∀ c4, ComPfHides NS3 Com3 (Pf3 c4) (fun d => (opQ (jSsT (SM c4) (SC c4) (S9 c4) (SPo c4) (SI c4) (ST c4) (SH c4) (SR c4) (SP c4) (SS c4)) d.1, opCw (jSsC tbM tbC tbPo tbI tpT tpH tpR tpP tpS (SM c4) (SC c4) (S9 c4) (SPo c4) (SI c4) (ST c4) (SH c4) (SR c4) (SP c4) (SS c4)) d.2)))
    (hr3 : ∀ d σ, Com3 d σ < n3) (d3 : List (List (List (List F))) × List (List (List F)))
    (E : Nat → Nat → Nat → Nat → Nat → Nat → Nat → Option P1 × Option (P2 × P3) × TViewN (PcsPV (V × Wv)) (EF × EF) → Bool) :
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
      sumTo NS1 (fun σ1 => sumTo (NS2 * NS3) (fun σ => sumTo NR (fun r => sumN 7 (fun t => g (σ1, σ, r, t)))))
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
          (K2 * (Q4 * (NS1 * (NS2 * NS3 * (Q4 * (NR * (Q4 ^ 7 * M)) + Q4 * (Q4 * (Q4 ^ 7 * 0)))))) +
            (Q4 * (P * P) * (K2 * Q4) + Q4 * Q4 * (K2 * (P * P))) * (NS1 * (NS2 * NS3 * (NR * (Q4 ^ 7 * 1)))))))) +
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
          (K2 * (Q4 * (NS1 * (NS2 * NS3 * (Q4 * (NR * (Q4 ^ 7 * M)) + Q4 * (Q4 * (Q4 ^ 7 * 0)))))) +
            (Q4 * (P * P) * (K2 * Q4) + Q4 * Q4 * (K2 * (P * P))) * (NS1 * (NS2 * NS3 * (NR * (Q4 ^ 7 * 1)))))))) +
            B4 * (Q4 * Q4 * (K2 * Q4) * sm4 (fun _ => 1)))) := by
  intro m segRoots N Rn C Pg Wt Po Iw Mm Rt Hd Tm NR0 pcsZ psimZ NR tabs tv pb ptm M q0 qZ Ss ks cols tqZ qdZ SsT SsC mk1 mk2 main1 main2 main3 vS sop1 sop2 sop3 ov1 ov2 ov3 rvF svF ozF op3 sd3
  obtain ⟨⟨hbal, hun⟩, ⟨sc, sms, sw, spo, si, st, sh, sr⟩,
    ⟨hC0, hM0, hWh, hPo0, hI0, t1, hTm, h1, hHd, r1, hRt, p1, p2, s1, s2⟩⟩ :=
    compJ_run_facts hR hLm hLp hLi hprov hprov24 hrl hr hroots hA hlen hK hHP hHW hNW
  rw [← htP] at p1 p2
  rw [← htS] at s1 s2
  rw [← htT] at t1 hTm
  rw [← htH] at h1 hHd
  rw [← htR] at r1 hRt
  have hM : Mm.h = 2 ^ (tbM + 1) := by rw [htM]; exact hM0
  have hC : C.h = 2 ^ (tbC + 1) := by rw [htC]; exact hC0
  have hPo : Po.h = 2 ^ (tbPo + 1) := by rw [htPo]; exact hPo0
  have hI : Iw.h = 2 ^ (tbI + 1) := by rw [htI]; exact hI0
  have hSw := fun (c4 c2 c3 : Nat) => compJ_same_w off m.hd m.stk m.heap.length Ps.length m.stk m.heap N W segRoots roots jets C Mm Wt Rt Hd Tm Po Iw tbM tbC tbPo tbI tpT tpH tpR tpP tpS (SM c4) (SC c4) (S9 c4) (SPo c4) (SI c4) (ST c4) (SH c4) (SR c4) (SP c4) (SS c4) (efOf c3) EF.zero qv (wm c2) (wc c2) (ww c2) (wpo c2) (wi c2) (wt c2) (wh c2) (wr c2) (wp c2) (wsg c2) (wm 0) (wc 0) (ww 0) (wpo 0) (wi 0) (wt 0) (wh 0) (wr 0) (wp 0) (wsg 0) ncw (by rw [hlwm, hlwm]) (by rw [hlwc, hlwc]) (by rw [hlww, hlww]) (by rw [hlwpo, hlwpo]) (by rw [hlwi, hlwi]) (by rw [hlwt, hlwt]) (by rw [hlwh, hlwh]) (by rw [hlwr, hlwr]) (by rw [hlwp, hlwp]) (by rw [hlwsg, hlwsg])
  have hSz := fun (c4 c2 c3 : Nat) => compJ_same_w off m.hd m.stk m.heap.length Ps.length m.stk m.heap N W segRoots roots jets C Mm Wt Rt Hd Tm Po Iw tbM tbC tbPo tbI tpT tpH tpR tpP tpS (SM c4) (SC c4) (S9 c4) (SPo c4) (SI c4) (ST c4) (SH c4) (SR c4) (SP c4) (SS c4) (efOf c3) EF.zero qv (wm c2) (wc c2) (ww c2) (wpo c2) (wi c2) (wt c2) (wh c2) (wr c2) (wp c2) (wsg c2) (wm c2) (wc c2) (ww c2) (wpo c2) (wi c2) (wt c2) (wh c2) (wr c2) (wp c2) (wsg c2) ncw rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
  have hS0 := fun (c4 c2 : Nat) => compJ_same_w off m.hd m.stk m.heap.length Ps.length m.stk m.heap N W segRoots roots jets C Mm Wt Rt Hd Tm Po Iw tbM tbC tbPo tbI tpT tpH tpR tpP tpS (SM c4) (SC c4) (S9 c4) (SPo c4) (SI c4) (ST c4) (SH c4) (SR c4) (SP c4) (SS c4) EF.zero EF.zero qv (wm c2) (wc c2) (ww c2) (wpo c2) (wi c2) (wt c2) (wh c2) (wr c2) (wp c2) (wsg c2) (wm 0) (wc 0) (ww 0) (wpo 0) (wi 0) (wt 0) (wh 0) (wr 0) (wp 0) (wsg 0) ncw (by rw [hlwm, hlwm]) (by rw [hlwc, hlwc]) (by rw [hlww, hlww]) (by rw [hlwpo, hlwpo]) (by rw [hlwi, hlwi]) (by rw [hlwt, hlwt]) (by rw [hlwh, hlwh]) (by rw [hlwr, hlwr]) (by rw [hlwp, hlwp]) (by rw [hlwsg, hlwsg])
  have hSd := fun (c4 c2 c3 : Nat) => compJ_same_d off m.hd m.stk m.heap.length Ps.length m.stk m.heap N W segRoots roots jets C Mm Wt Rt Hd Tm Po Iw tbM tbC tbPo tbI tpT tpH tpR tpP tpS (SM c4) (SC c4) (S9 c4) (SPo c4) (SI c4) (ST c4) (SH c4) (SR c4) (SP c4) (SS c4) (SM 0) (SC 0) (S9 0) (SPo 0) (SI 0) (ST 0) (SH 0) (SR 0) (SP 0) (SS 0) (efOf c3) EF.zero qv (wm c2) (wc c2) (ww c2) (wpo c2) (wi c2) (wt c2) (wh c2) (wr c2) (wp c2) (wsg c2) (wm 0) (wc 0) (ww 0) (wpo 0) (wi 0) (wt 0) (wh 0) (wr 0) (wp 0) (wsg 0) (by rw [hlwm, hlwm]) (by rw [hlwc, hlwc]) (by rw [hlww, hlww]) (by rw [hlwpo, hlwpo]) (by rw [hlwi, hlwi]) (by rw [hlwt, hlwt]) (by rw [hlwh, hlwh]) (by rw [hlwr, hlwr]) (by rw [hlwp, hlwp]) (by rw [hlwsg, hlwsg])
  have hSdz := fun (c4 c2 c3 : Nat) => compJ_same_d off m.hd m.stk m.heap.length Ps.length m.stk m.heap N W segRoots roots jets C Mm Wt Rt Hd Tm Po Iw tbM tbC tbPo tbI tpT tpH tpR tpP tpS (SM c4) (SC c4) (S9 c4) (SPo c4) (SI c4) (ST c4) (SH c4) (SR c4) (SP c4) (SS c4) (SM 0) (SC 0) (S9 0) (SPo 0) (SI 0) (ST 0) (SH 0) (SR 0) (SP 0) (SS 0) (efOf c3) EF.zero qv (wm c2) (wc c2) (ww c2) (wpo c2) (wi c2) (wt c2) (wh c2) (wr c2) (wp c2) (wsg c2) (wm c2) (wc c2) (ww c2) (wpo c2) (wi c2) (wt c2) (wh c2) (wr c2) (wp c2) (wsg c2) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
  have hb : ∀ c4 c2 c3, genB (αd c4) = true → genB (efOf c3) = true →
      (∀ E' : TViewN (PcsPV (V × Wv)) (EF × EF) → Bool,
        tsumN NR 7 (fun α β r t => indB (genB β && E' (rvF c4 c2 c3 α β r t))) ≤
          tsumN NR 7 (fun α β r t => indB (genB β && E' (svF c4 c2 c3 α β r t))) + Q4 * (NR * (Q4 ^ 7 * M)) +
            Q4 * (Q4 * (Q4 ^ 7 * 0))) ∧
      (∀ E' : TViewN (PcsPV (V × Wv)) (EF × EF) → Bool,
        tsumN NR 7 (fun α β r t => indB (genB β && E' (svF c4 c2 c3 α β r t))) ≤
          tsumN NR 7 (fun α β r t => indB (genB β && E' (rvF c4 c2 c3 α β r t))) + Q4 * (NR * (Q4 ^ 7 * M)) +
            Q4 * (Q4 * (Q4 ^ 7 * 0))) := fun c4 c2 c3 hg4 hg => by
    have hgz := (genB_iff _).1 hg
    have hgα := (genB_iff _).1 hg4
    have hpcs := compJ_pcsX (heap := m.heap) (ζ := efOf c3) (segRoots := segRoots) (roots := roots) (jets := jets) off sc sms sw spo si st sh sr (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      hM hC hWh hPo hI hTm hHd hRt p2 s2 qv (wm c2) (wc c2) (ww c2) (wpo c2) (wi c2) (wt c2) (wh c2) (wr c2) (wp c2) (wsg c2) (hSM c4) (hSC c4) (hS9 c4) (hSPo c4) (hSI c4) (hST c4) (hSH c4) (hSR c4) (hSP c4) (hSS c4) (hszM c4) (hszC c4) (hsz9 c4) (hszPo c4) (hszI c4) (hszT c4) (hszH c4) (hszR c4) (hszP c4) (hszS c4) (generic_ofF_ne hgz) (mz_generic hgz) (fri c4) (mz_generic hgα) (generic_apow_ne hgα) hncw NR2 (Rb c4) (Ro c4)
    have hNR : jNR off m.hd m.stk m.heap.length Ps.length m.stk m.heap N W segRoots roots jets C Mm Wt Rt Hd Tm Po Iw tbM tbC tbPo tbI tpT tpH tpR tpP tpS (SM c4) (SC c4) (S9 c4) (SPo c4) (SI c4) (ST c4) (SH c4) (SR c4) (SP c4) (SS c4) (efOf c3) qv (wm c2) (wc c2) (ww c2) (wpo c2) (wi c2) (wt c2) (wh c2) (wr c2) (wp c2) (wsg c2) ncw = jNR off m.hd m.stk m.heap.length Ps.length m.stk m.heap N W segRoots roots jets C Mm Wt Rt Hd Tm Po Iw tbM tbC tbPo tbI tpT tpH tpR tpP tpS (SM 0) (SC 0) (S9 0) (SPo 0) (SI 0) (ST 0) (SH 0) (SR 0) (SP 0) (SS 0) EF.zero qv (wm 0) (wc 0) (ww 0) (wpo 0) (wi 0) (wt 0) (wh 0) (wr 0) (wp 0) (wsg 0) ncw := by
      unfold jNR; rw [(hSd c4 c2 c3).n1, (hSd c4 c2 c3).n2]
    rw [hNR] at hpcs
    exact ⟨fun E' => (compJ_transcriptG off NR 0 (pcsZ c4 c2 (efOf c3)) (psimZ c4 c2 (efOf c3)) hbal hun hpcs E').1,
      fun E' => (compJ_transcriptG off NR 0 (pcsZ c4 c2 (efOf c3)) (psimZ c4 c2 (efOf c3)) hbal hun hpcs E').2⟩
  have hlen8 : ∀ (c4 : Nat) (ζ : EF) t α β, (cols t α β).map List.length = (cols t EF.zero EF.zero).map List.length :=
    fun c4 ζ t α β => by
      rw [(jCols_shaped off m.hd m.stk m.heap.length Ps.length m.stk hM hC hWh hPo hI hTm hHd hRt p2 s2
          (SM c4) (SC c4) (S9 c4) (SPo c4) (SI c4) (ST c4) (SH c4) (SR c4) (SP c4) (SS c4) ζ qv t α β).2,
        (jCols_shaped off m.hd m.stk m.heap.length Ps.length m.stk hM hC hWh hPo hI hTm hHd hRt p2 s2
          (SM c4) (SC c4) (S9 c4) (SPo c4) (SI c4) (ST c4) (SH c4) (SR c4) (SP c4) (SS c4) ζ qv t EF.zero EF.zero).2]
  have hmk1 : ∀ k ∈ mk1, k < 20 ∧ ∀ t α β, k < (cols t α β).length ∧
      (cols t α β).getD k [] = (cols t EF.zero EF.zero).getD k [] := by
    intro k hk
    have hk' := hk
    simp only [mk1, List.mem_cons, List.not_mem_nil, or_false] at hk'
    have hkn : k < 20 := by rcases hk' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact ⟨hkn, fun t α β => ⟨hkn, compJCols_main off m.hd m.stk m.heap.length Ps.length m.stk m.heap N W segRoots roots jets C Mm Wt Rt Hd Tm Po Iw t α β
      EF.zero EF.zero k hk⟩⟩
  have hmk2 : ∀ k ∈ mk2, k < 20 ∧ ∀ t α β, k < (cols t α β).length := by
    intro k hk
    simp only [mk2, List.mem_cons, List.not_mem_nil, or_false] at hk
    have hkn : k < 20 := by rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact ⟨hkn, fun _ _ _ => hkn⟩
  have hvo1 : ∀ c4 c2 c3 c r t, rvF c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t = none ∨
      ov1 c4 (rvF c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (opF (Ss c4) mk1 (main1 t r)) := by
    intro c4 c2 c3 c r t
    show realVN off tabs tv pb (pcsZ c4 c2 (efOf c3)) _ _ r t = none ∨
      ov1 c4 (realVN off tabs tv pb (pcsZ c4 c2 (efOf c3)) _ _ r t) = _
    unfold realVN
    split
    · exact .inl rfl
    · have e := pcsFri_ov2 off (fun pre β t => compJViewN pre β m.hd m.stk m.heap.length Ps.length m.stk N W roots jets C Mm Wt Rt Hd Tm Po Iw t) (jGroups tbM tbC tbPo tbI tpT tpH tpR tpP tpS (SM c4) (SC c4) (S9 c4) (SPo c4) (SI c4) (ST c4) (SH c4) (SR c4) (SP c4) (SS c4) (efOf c3) qv) ks cols ((jTs off m.hd m.stk m.heap.length Ps.length m.stk m.heap N W segRoots roots jets C Mm Wt Rt Hd Tm Po Iw tbM tbC tbPo tbI tpT tpH tpR tpP tpS (SM c4) (SC c4) (S9 c4) (SPo c4) (SI c4) (ST c4) (SH c4) (SR c4) (SP c4) (SS c4) (efOf c3) qv (wm c2) (wc c2) (ww c2) (wpo c2) (wi c2) (wt c2) (wh c2) (wr c2) (wp c2) (wsg c2)).map Prod.fst) (fun t α β ms => (jTs off m.hd m.stk m.heap.length Ps.length m.stk m.heap N W segRoots roots jets C Mm Wt Rt Hd Tm Po Iw tbM tbC tbPo tbI tpT tpH tpR tpP tpS (SM c4) (SC c4) (S9 c4) (SPo c4) (SI c4) (ST c4) (SH c4) (SR c4) (SP c4) (SS c4) (efOf c3) qv (wm c2) (wc c2) (ww c2) (wpo c2) (wi c2) (wt c2) (wh c2) (wr c2) (wp c2) (wsg c2)).map fun p => p.2 t α β ms) ncw (αd c4)
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
    · have e := pcsFri_ovP off (fun pre β t => compJViewN pre β m.hd m.stk m.heap.length Ps.length m.stk N W roots jets C Mm Wt Rt Hd Tm Po Iw t) (jGroups tbM tbC tbPo tbI tpT tpH tpR tpP tpS (SM c4) (SC c4) (S9 c4) (SPo c4) (SI c4) (ST c4) (SH c4) (SR c4) (SP c4) (SS c4) (efOf c3) qv) ks cols ((jTs off m.hd m.stk m.heap.length Ps.length m.stk m.heap N W segRoots roots jets C Mm Wt Rt Hd Tm Po Iw tbM tbC tbPo tbI tpT tpH tpR tpP tpS (SM c4) (SC c4) (S9 c4) (SPo c4) (SI c4) (ST c4) (SH c4) (SR c4) (SP c4) (SS c4) (efOf c3) qv (wm c2) (wc c2) (ww c2) (wpo c2) (wi c2) (wt c2) (wh c2) (wr c2) (wp c2) (wsg c2)).map Prod.fst) (fun t α β ms => (jTs off m.hd m.stk m.heap.length Ps.length m.stk m.heap N W segRoots roots jets C Mm Wt Rt Hd Tm Po Iw tbM tbC tbPo tbI tpT tpH tpR tpP tpS (SM c4) (SC c4) (S9 c4) (SPo c4) (SI c4) (ST c4) (SH c4) (SR c4) (SP c4) (SS c4) (efOf c3) qv (wm c2) (wc c2) (ww c2) (wpo c2) (wi c2) (wt c2) (wh c2) (wr c2) (wp c2) (wsg c2)).map fun p => p.2 t α β ms) ncw (αd c4)
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
      have e0 := pcsFri_ovR2 off (fun pre β t => compJViewN pre β m.hd m.stk m.heap.length Ps.length m.stk N W roots jets C Mm Wt Rt Hd Tm Po Iw t) (jGroups tbM tbC tbPo tbI tpT tpH tpR tpP tpS (SM c4) (SC c4) (S9 c4) (SPo c4) (SI c4) (ST c4) (SH c4) (SR c4) (SP c4) (SS c4) (efOf c3) qv) ks cols ((jTs off m.hd m.stk m.heap.length Ps.length m.stk m.heap N W segRoots roots jets C Mm Wt Rt Hd Tm Po Iw tbM tbC tbPo tbI tpT tpH tpR tpP tpS (SM c4) (SC c4) (S9 c4) (SPo c4) (SI c4) (ST c4) (SH c4) (SR c4) (SP c4) (SS c4) (efOf c3) qv (wm c2) (wc c2) (ww c2) (wpo c2) (wi c2) (wt c2) (wh c2) (wr c2) (wp c2) (wsg c2)).map Prod.fst) (fun t α β ms => (jTs off m.hd m.stk m.heap.length Ps.length m.stk m.heap N W segRoots roots jets C Mm Wt Rt Hd Tm Po Iw tbM tbC tbPo tbI tpT tpH tpR tpP tpS (SM c4) (SC c4) (S9 c4) (SPo c4) (SI c4) (ST c4) (SH c4) (SR c4) (SP c4) (SS c4) (efOf c3) qv (wm c2) (wc c2) (ww c2) (wpo c2) (wi c2) (wt c2) (wh c2) (wr c2) (wp c2) (wsg c2)).map fun p => p.2 t α β ms) ncw (αd c4)
        (friX (fri c4) (Rb c4) (Ro c4) (r / NR0)) mk2 hmk2 rfl t (efOf (c / Q4)) (efOf (c % Q4)) (r % NR0)
      have e := congrArg Prod.snd e0
      rw [(hSz c4 c2 c3).tS, (hSz c4 c2 c3).iS, tabsPolys_congr _ _ _ _ (hSdz c4 c2 c3).shape,
        tabsCws_congr ncw _ _ _ (hSdz c4 c2 c3).shape, (hSdz c4 c2 c3).cr (r % NR0), (hSdz c4 c2 c3).cc (r % NR0),
        (hSdz c4 c2 c3).ms (r % NR0), (hS0 c4 c2).tS, (hS0 c4 c2).iS,
        compJ_data_q off m.hd m.stk m.heap.length Ps.length m.stk m.heap N W segRoots roots jets C Mm Wt Rt Hd Tm Po Iw tbM tbC tbPo tbI tpT tpH tpR tpP tpS (SM c4) (SC c4) (S9 c4) (SPo c4) (SI c4) (ST c4) (SH c4) (SR c4) (SP c4) (SS c4) (SM 0) (SC 0) (S9 0) (SPo 0) (SI 0) (ST 0) (SH 0) (SR 0) (SP 0) (SS 0) (efOf c3) EF.zero
          qv (wm c2) (wc c2) (ww c2) (wpo c2) (wi c2) (wt c2) (wh c2) (wr c2) (wp c2) (wsg c2) t _ _ _ hab'] at e
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
    have e0 := psimFri_ovR2 (jGroups tbM tbC tbPo tbI tpT tpH tpR tpP tpS (SM c4) (SC c4) (S9 c4) (SPo c4) (SI c4) (ST c4) (SH c4) (SR c4) (SP c4) (SS c4) (efOf c3) qv) ks ((jTs off m.hd m.stk m.heap.length Ps.length m.stk m.heap N W segRoots roots jets C Mm Wt Rt Hd Tm Po Iw tbM tbC tbPo tbI tpT tpH tpR tpP tpS (SM c4) (SC c4) (S9 c4) (SPo c4) (SI c4) (ST c4) (SH c4) (SR c4) (SP c4) (SS c4) (efOf c3) qv (wm c2) (wc c2) (ww c2) (wpo c2) (wi c2) (wt c2) (wh c2) (wr c2) (wp c2) (wsg c2)).map Prod.fst) ncw (αd c4) (friX (fri c4) (Rb c4) (Ro c4) (r / NR0)) mk2
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
    have e1 : SsT c4 = jSsT (SM c4) (SC c4) (S9 c4) (SPo c4) (SI c4) (ST c4) (SH c4) (SR c4) (SP c4) (SS c4) := compJ_SsT off m.hd m.stk m.heap.length Ps.length m.stk m.heap N W segRoots roots jets C Mm Wt Rt Hd Tm Po Iw tbM tbC tbPo tbI tpT tpH tpR tpP tpS (SM c4) (SC c4) (S9 c4) (SPo c4) (SI c4) (ST c4) (SH c4) (SR c4) (SP c4) (SS c4) EF.zero qv (wm 0) (wc 0) (ww 0) (wpo 0) (wi 0) (wt 0) (wh 0) (wr 0) (wp 0) (wsg 0)
    have e2 : SsC c4 = jSsC tbM tbC tbPo tbI tpT tpH tpR tpP tpS (SM c4) (SC c4) (S9 c4) (SPo c4) (SI c4) (ST c4) (SH c4) (SR c4) (SP c4) (SS c4) := compJ_SsC off m.hd m.stk m.heap.length Ps.length m.stk m.heap N W segRoots roots jets C Mm Wt Rt Hd Tm Po Iw tbM tbC tbPo tbI tpT tpH tpR tpP tpS (SM c4) (SC c4) (S9 c4) (SPo c4) (SI c4) (ST c4) (SH c4) (SR c4) (SP c4) (SS c4) EF.zero qv (wm 0) (wc 0) (ww 0) (wpo 0) (wi 0) (wt 0) (wh 0) (wr 0) (wp 0) (wsg 0) ncw
    show ComPfHides NS3 Com3 (Pf3 c4) (fun d => (opQ (SsT c4) d.1, opCw (SsC c4) d.2))
    rw [e1, e2]; exact hp3 c4
  have hoz : ∀ c4 c2 c3 α β r t, ozF (rvF c4 c2 c3 α β r t) = ozF (rvF 0 c2 c3 α β r t) := by
    intro c4 c2 c3 α β r t
    simp only [rvF]
    unfold realVN
    cases hA : Aborts (prefixOf α (off β)) β (tabs t)
    · simp only [Bool.false_eq_true, ↓reduceIte, ozF, Option.some.injEq, Prod.mk.injEq]
      have hd := compJ_same_d off m.hd m.stk m.heap.length Ps.length m.stk m.heap N W segRoots roots jets C Mm Wt Rt Hd Tm Po Iw tbM tbC tbPo tbI tpT tpH tpR tpP tpS (SM c4) (SC c4) (S9 c4) (SPo c4) (SI c4) (ST c4) (SH c4) (SR c4) (SP c4) (SS c4) (SM 0) (SC 0) (S9 0) (SPo 0) (SI 0) (ST 0) (SH 0) (SR 0) (SP 0) (SS 0) (efOf c3) (efOf c3) qv (wm c2) (wc c2) (ww c2) (wpo c2) (wi c2) (wt c2) (wh c2) (wr c2) (wp c2) (wsg c2) (wm c2) (wc c2) (ww c2) (wpo c2) (wi c2) (wt c2) (wh c2) (wr c2) (wp c2) (wsg c2) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
      refine ⟨pcsFri_ood off (fun pre β t => compJViewN pre β m.hd m.stk m.heap.length Ps.length m.stk N W roots jets C Mm Wt Rt Hd Tm Po Iw t) (jGroups tbM tbC tbPo tbI tpT tpH tpR tpP tpS (SM c4) (SC c4) (S9 c4) (SPo c4) (SI c4) (ST c4) (SH c4) (SR c4) (SP c4) (SS c4) (efOf c3) qv) (jGroups tbM tbC tbPo tbI tpT tpH tpR tpP tpS (SM 0) (SC 0) (S9 0) (SPo 0) (SI 0) (ST 0) (SH 0) (SR 0) (SP 0) (SS 0) (efOf c3) qv) ks cols
        ((jTs off m.hd m.stk m.heap.length Ps.length m.stk m.heap N W segRoots roots jets C Mm Wt Rt Hd Tm Po Iw tbM tbC tbPo tbI tpT tpH tpR tpP tpS (SM c4) (SC c4) (S9 c4) (SPo c4) (SI c4) (ST c4) (SH c4) (SR c4) (SP c4) (SS c4) (efOf c3) qv (wm c2) (wc c2) (ww c2) (wpo c2) (wi c2) (wt c2) (wh c2) (wr c2) (wp c2) (wsg c2)).map Prod.fst) ((jTs off m.hd m.stk m.heap.length Ps.length m.stk m.heap N W segRoots roots jets C Mm Wt Rt Hd Tm Po Iw tbM tbC tbPo tbI tpT tpH tpR tpP tpS (SM 0) (SC 0) (S9 0) (SPo 0) (SI 0) (ST 0) (SH 0) (SR 0) (SP 0) (SS 0) (efOf c3) qv (wm c2) (wc c2) (ww c2) (wpo c2) (wi c2) (wt c2) (wh c2) (wr c2) (wp c2) (wsg c2)).map Prod.fst) _ _ ncw (αd c4) (αd 0) _ _
        hd rfl rfl t α β (r % NR0), pcsFri_oodT off (fun pre β t => compJViewN pre β m.hd m.stk m.heap.length Ps.length m.stk N W roots jets C Mm Wt Rt Hd Tm Po Iw t) (jGroups tbM tbC tbPo tbI tpT tpH tpR tpP tpS (SM c4) (SC c4) (S9 c4) (SPo c4) (SI c4) (ST c4) (SH c4) (SR c4) (SP c4) (SS c4) (efOf c3) qv) (jGroups tbM tbC tbPo tbI tpT tpH tpR tpP tpS (SM 0) (SC 0) (S9 0) (SPo 0) (SI 0) (ST 0) (SH 0) (SR 0) (SP 0) (SS 0) (efOf c3) qv) ks cols
        ((jTs off m.hd m.stk m.heap.length Ps.length m.stk m.heap N W segRoots roots jets C Mm Wt Rt Hd Tm Po Iw tbM tbC tbPo tbI tpT tpH tpR tpP tpS (SM c4) (SC c4) (S9 c4) (SPo c4) (SI c4) (ST c4) (SH c4) (SR c4) (SP c4) (SS c4) (efOf c3) qv (wm c2) (wc c2) (ww c2) (wpo c2) (wi c2) (wt c2) (wh c2) (wr c2) (wp c2) (wsg c2)).map Prod.fst) ((jTs off m.hd m.stk m.heap.length Ps.length m.stk m.heap N W segRoots roots jets C Mm Wt Rt Hd Tm Po Iw tbM tbC tbPo tbI tpT tpH tpR tpP tpS (SM 0) (SC 0) (S9 0) (SPo 0) (SI 0) (ST 0) (SH 0) (SR 0) (SP 0) (SS 0) (efOf c3) qv (wm c2) (wc c2) (ww c2) (wpo c2) (wi c2) (wt c2) (wh c2) (wr c2) (wp c2) (wsg c2)).map Prod.fst) _ _ ncw (αd c4) (αd 0) _ _
        hd (by simp only [jTs, bbTab, airQTabG, List.map_cons, List.map_nil]) t α β (r % NR0)
        (compJ_data_q off m.hd m.stk m.heap.length Ps.length m.stk m.heap N W segRoots roots jets C Mm Wt Rt Hd Tm Po Iw tbM tbC tbPo tbI tpT tpH tpR tpP tpS (SM c4) (SC c4) (S9 c4) (SPo c4) (SI c4) (ST c4) (SH c4) (SR c4) (SP c4) (SS c4) (SM 0) (SC 0) (S9 0) (SPo 0) (SI 0) (ST 0) (SH 0) (SR 0) (SP 0) (SS 0) (efOf c3) (efOf c3) qv (wm c2) (wc c2) (ww c2) (wpo c2) (wi c2) (wt c2) (wh c2) (wr c2) (wp c2) (wsg c2) t _ _ _ hA),
        pcsFri_oodC off (fun pre β t => compJViewN pre β m.hd m.stk m.heap.length Ps.length m.stk N W roots jets C Mm Wt Rt Hd Tm Po Iw t) (jGroups tbM tbC tbPo tbI tpT tpH tpR tpP tpS (SM c4) (SC c4) (S9 c4) (SPo c4) (SI c4) (ST c4) (SH c4) (SR c4) (SP c4) (SS c4) (efOf c3) qv) (jGroups tbM tbC tbPo tbI tpT tpH tpR tpP tpS (SM 0) (SC 0) (S9 0) (SPo 0) (SI 0) (ST 0) (SH 0) (SR 0) (SP 0) (SS 0) (efOf c3) qv) ks cols
        ((jTs off m.hd m.stk m.heap.length Ps.length m.stk m.heap N W segRoots roots jets C Mm Wt Rt Hd Tm Po Iw tbM tbC tbPo tbI tpT tpH tpR tpP tpS (SM c4) (SC c4) (S9 c4) (SPo c4) (SI c4) (ST c4) (SH c4) (SR c4) (SP c4) (SS c4) (efOf c3) qv (wm c2) (wc c2) (ww c2) (wpo c2) (wi c2) (wt c2) (wh c2) (wr c2) (wp c2) (wsg c2)).map Prod.fst) ((jTs off m.hd m.stk m.heap.length Ps.length m.stk m.heap N W segRoots roots jets C Mm Wt Rt Hd Tm Po Iw tbM tbC tbPo tbI tpT tpH tpR tpP tpS (SM 0) (SC 0) (S9 0) (SPo 0) (SI 0) (ST 0) (SH 0) (SR 0) (SP 0) (SS 0) (efOf c3) qv (wm c2) (wc c2) (ww c2) (wpo c2) (wi c2) (wt c2) (wh c2) (wr c2) (wp c2) (wsg c2)).map Prod.fst) _ _ ncw (αd c4) (αd 0) _ _
        hd rfl (by simp only [jTs, bbTab, airQTabG, List.map_cons, List.map_nil]) t α β (r % NR0)⟩
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
