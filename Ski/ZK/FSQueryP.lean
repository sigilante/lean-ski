import Ski.ZK.CompPHiding
import Ski.ZK.FSQueryInst

/-!
# The proof with the Poseidon2 jet over four Fiat–Shamir rounds

`comp_fs_open4`'s construction for the circuit with the Poseidon2 jet
(`compP_fs_open4`; its call-count hypothesis met by `p2pre`'s and the
hand-off's verifiers, `compP_calls_p2pre`, `compP_calls_p2commit`): its
PCS is `compP_pcs`'s, its run's facts `compP_run_facts`'s, its transcript
`compP_transcriptG`'s.  Scope and assumptions as `comp_fs_open4`'s
(`Ski/ZK/FSQueryInst.lean`).
-/

namespace Circuit

open ZKF B Air Compose CompM Stmt Mach Wit ComposedPText

def pSsT (SM SC S9 SI SO SQ SP SS SX : List F) : List (List F) := [SM, SC, S9, SI, SO, SQ, SP, SS, SX]

def pSsC (tbM tbC tbI tbO tbQ tpP tpS : Nat) (SM SC S9 SI SO SQ SP SS SX : List F) : List (List F) :=
  List.replicate ((bbCs tbM 1 (2 ^ (tbM + 1) - 1)).length + 1) SM ++ (List.replicate ((bbCs tbC 1 (2 ^ (tbC + 1) - 1)).length + 1) SC ++ (List.replicate ((bbCs 8 1 (2 ^ (8 + 1) - 1)).length + 1) S9 ++ (List.replicate ((bbCs tbI 1 (2 ^ (tbI + 1) - 1)).length + 1) SI ++ (List.replicate ((bbCs tbO 2 (2 ^ (tbO + 1) - 1)).length + 1) SO ++ (List.replicate ((bbCs tbQ 2 (2 ^ (tbQ + 1) - 1)).length + 1) SQ ++ (List.replicate ((bbCs tpP 1 (2 ^ (tpP + 1) - 1)).length + 1) SP ++ (List.replicate ((bbCs tpS 1 (2 ^ (tpS + 1) - 1)).length + 1) SS ++ (List.replicate ((bbCs 8 1 (2 ^ (8 + 1) - 1)).length + 1) SX ++ []))))))))

section
variable (off : EF → String → EF) (hd0 stk0 ctr0 n nilA J root : Nat) (heap : List Cell) (N W : Nat)
  (segRoots : List Nat) (calls : Nat) (C Mm Wt Pi Po Pp : Table) (tbM tbC tbI tbO tbQ tpP tpS : Nat)

set_option maxRecDepth 100000 in
theorem compP_SsT (SM SC S9 SI SO SQ SP SS SX : List F) (ζ : EF) (qv : EF → EF → List EF → F → List F → List F → List EF)
    (wm wc ww wi wo wq wp wsg wx : List (EF → EF → List F)) :
    ((pTs off hd0 stk0 ctr0 n nilA J root heap N W segRoots calls C Mm Wt Pi Po Pp tbM tbC tbI tbO tbQ tpP tpS SM SC S9 SI SO SQ SP SS SX ζ qv wm wc ww wi wo wq wp wsg wx).map Prod.fst).map (·.S) = pSsT SM SC S9 SI SO SQ SP SS SX := by
  simp only [pTs, bbTabL, airQTabG, List.map_cons, List.map_nil, pSsT]

set_option maxRecDepth 100000 in
theorem compP_SsC (SM SC S9 SI SO SQ SP SS SX : List F) (ζ : EF) (qv : EF → EF → List EF → F → List F → List F → List EF)
    (wm wc ww wi wo wq wp wsg wx : List (EF → EF → List F)) (ncw : Nat) :
    (tabsInfo ncw ((pTs off hd0 stk0 ctr0 n nilA J root heap N W segRoots calls C Mm Wt Pi Po Pp tbM tbC tbI tbO tbQ tpP tpS SM SC S9 SI SO SQ SP SS SX ζ qv wm wc ww wi wo wq wp wsg wx).map Prod.fst)).map (·.S) = pSsC tbM tbC tbI tbO tbQ tpP tpS SM SC S9 SI SO SQ SP SS SX := by
  simp only [pTs, bbTabL, airQTabG, tabsInfo, tInfo, List.map_cons, List.map_nil, List.map_append, List.map_replicate, pSsC]

set_option maxRecDepth 100000 in
/-- **The PCS with the Poseidon2 jet's shape reads neither `ζ` nor the
    weights**, only their lengths. -/
theorem compP_same_w (SM SC S9 SI SO SQ SP SS SX : List F) (ζ ζ' : EF) (qv : EF → EF → List EF → F → List F → List F → List EF)
    (wm wc ww wi wo wq wp wsg wx wm' wc' ww' wi' wo' wq' wp' wsg' wx' : List (EF → EF → List F)) (ncw : Nat)
    (hwm : wm.length = wm'.length) (hwc : wc.length = wc'.length) (hww : ww.length = ww'.length) (hwi : wi.length = wi'.length) (hwo : wo.length = wo'.length) (hwq : wq.length = wq'.length) (hwp : wp.length = wp'.length) (hwsg : wsg.length = wsg'.length) (hwx : wx.length = wx'.length) :
    SameShape (pGroups tbM tbC tbI tbO tbQ tpP tpS SM SC S9 SI SO SQ SP SS SX ζ qv) (pGroups tbM tbC tbI tbO tbQ tpP tpS SM SC S9 SI SO SQ SP SS SX ζ'  qv)
      (pKs hd0 stk0 ctr0 n nilA J root heap N W segRoots)
      ((pTs off hd0 stk0 ctr0 n nilA J root heap N W segRoots calls C Mm Wt Pi Po Pp tbM tbC tbI tbO tbQ tpP tpS SM SC S9 SI SO SQ SP SS SX ζ qv wm wc ww wi wo wq wp wsg wx).map Prod.fst)
      ((pTs off hd0 stk0 ctr0 n nilA J root heap N W segRoots calls C Mm Wt Pi Po Pp tbM tbC tbI tbO tbQ tpP tpS SM SC S9 SI SO SQ SP SS SX ζ' qv wm' wc' ww' wi' wo' wq' wp' wsg' wx').map Prod.fst) ncw where
  trn := rfl
  dom := rfl
  S := rfl
  shape := by
    simp only [pTs, bbTabL, airQTabG, tShape, List.map_cons, List.map_nil, List.length_map]
    rw [hwm, hwc, hww, hwi, hwo, hwq, hwp, hwsg, hwx]
  tS := by simp only [pTs, bbTabL, airQTabG, List.map_cons, List.map_nil]
  iS := by simp only [pTs, bbTabL, airQTabG, tabsInfo, tInfo, List.map_cons, List.map_nil, List.map_append,
    List.map_replicate]

set_option maxRecDepth 100000 in
theorem compP_data_q (SM SC S9 SI SO SQ SP SS SX SM' SC' S9' SI' SO' SQ' SP' SS' SX' : List F) (ζ ζ' : EF)
    (qv : EF → EF → List EF → F → List F → List F → List EF)
    (wm wc ww wi wo wq wp wsg wx : List (EF → EF → List F)) (t : Nat → Tup) (α β : EF) (ms : List F)
    (h : Aborts (prefixOf α (off β)) β (pTabs hd0 stk0 ctr0 n nilA J root heap N W segRoots calls C Mm Wt Pi Po Pp t) = false) :
    (pTs off hd0 stk0 ctr0 n nilA J root heap N W segRoots calls C Mm Wt Pi Po Pp tbM tbC tbI tbO tbQ tpP tpS SM SC S9 SI SO SQ SP SS SX ζ qv wm wc ww wi wo wq wp wsg wx).map (fun p => p.2 t α β ms) =
      (pTs off hd0 stk0 ctr0 n nilA J root heap N W segRoots calls C Mm Wt Pi Po Pp tbM tbC tbI tbO tbQ tpP tpS SM' SC' S9' SI' SO' SQ' SP' SS' SX' ζ' qv wm wc ww wi wo wq wp wsg wx).map (fun p => p.2 t α β ms) := by
  have hg : ∀ tss rs, mpolysMulti ((pGroups tbM tbC tbI tbO tbQ tpP tpS SM SC S9 SI SO SQ SP SS SX ζ qv).map QGroup.ext) tss rs =
      mpolysMulti ((pGroups tbM tbC tbI tbO tbQ tpP tpS SM' SC' S9' SI' SO' SQ' SP' SS' SX' ζ' qv).map QGroup.ext) tss rs := fun tss rs =>
    mpolysMulti_congr _ _ _ _ rfl
  simp only [pTs, bbDataL, List.map_cons, List.map_nil, h, if_true, hg]

set_option maxRecDepth 100000 in
theorem compP_same_d (SM SC S9 SI SO SQ SP SS SX SM' SC' S9' SI' SO' SQ' SP' SS' SX' : List F) (ζ ζ' : EF)
    (qv : EF → EF → List EF → F → List F → List F → List EF)
    (wm wc ww wi wo wq wp wsg wx wm' wc' ww' wi' wo' wq' wp' wsg' wx' : List (EF → EF → List F))
    (hwm : wm.length = wm'.length) (hwc : wc.length = wc'.length) (hww : ww.length = ww'.length) (hwi : wi.length = wi'.length) (hwo : wo.length = wo'.length) (hwq : wq.length = wq'.length) (hwp : wp.length = wp'.length) (hwsg : wsg.length = wsg'.length) (hwx : wx.length = wx'.length) :
    SameData (pGroups tbM tbC tbI tbO tbQ tpP tpS SM SC S9 SI SO SQ SP SS SX ζ qv) (pGroups tbM tbC tbI tbO tbQ tpP tpS SM' SC' S9' SI' SO' SQ' SP' SS' SX' ζ' qv)
      ((pTs off hd0 stk0 ctr0 n nilA J root heap N W segRoots calls C Mm Wt Pi Po Pp tbM tbC tbI tbO tbQ tpP tpS SM SC S9 SI SO SQ SP SS SX ζ qv wm wc ww wi wo wq wp wsg wx).map Prod.fst)
      ((pTs off hd0 stk0 ctr0 n nilA J root heap N W segRoots calls C Mm Wt Pi Po Pp tbM tbC tbI tbO tbQ tpP tpS SM' SC' S9' SI' SO' SQ' SP' SS' SX' ζ' qv wm' wc' ww' wi' wo' wq' wp' wsg' wx').map Prod.fst) where
  trn := rfl
  dom := rfl
  shape := by
    simp only [pTs, bbTabL, airQTabG, tShape, List.map_cons, List.map_nil, List.length_map]
    rw [hwm, hwc, hww, hwi, hwo, hwq, hwp, hwsg, hwx]

theorem compPCols_main (t : Nat → Tup) (α β α' β' : EF) :
    ∀ k ∈ [0, 2, 4, 6, 8, 10, 12, 14, 16],
      (pCols off hd0 stk0 ctr0 n nilA J root N W heap segRoots calls C Mm Wt Pi Po Pp t α β).getD k [] =
        (pCols off hd0 stk0 ctr0 n nilA J root N W heap segRoots calls C Mm Wt Pi Po Pp t α' β').getD k [] := by
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [pCols, List.getD_cons_zero, List.getD_cons_succ]

end

set_option maxRecDepth 100000 in
/-- **The PCS with the Poseidon2 jet, FRI's randomness split off, hides
    exactly**: `compP_pcs` at every split (`comp_pcsX`). -/
theorem compP_pcsX {V Wv : Type} (off : EF → String → EF) {hd0 stk0 ctr0 n nilA J root : Nat} {heap : List Cell}
    {N W : Nat} {segRoots : List Nat} {calls : Nat} {C Mm Wt Pi Po Pp : Table}
    (hsM : Sat memAirC Mm)
    (hsC : Sat (cpuAirP2 hd0 stk0 ctr0 n nilA J root) C)
    (hsW : Sat (witAirP N W) Wt)
    (hsI : Sat p2inAirB Pi)
    (hsO : Sat p2outAirB Po)
    (hsQ : Sat p2AirB Pp)
    {tbM tbC tbI tbO tbQ tpP tpS : Nat} (hbtbM : tbM ≤ 23) (hbtbC : tbC ≤ 23) (hbtbI : tbI ≤ 23) (hbtbO : tbO ≤ 23) (hbtbQ : tbQ ≤ 23) (hbtpP : tpP ≤ 23) (hbtpS : tpS ≤ 23)
    (hMem : Mm.h = 2 ^ (tbM + 1)) (hCpu : C.h = 2 ^ (tbC + 1)) (hWit : Wt.h = 2 ^ 9) (hPin : Pi.h = 2 ^ (tbI + 1)) (hPout : Po.h = 2 ^ (tbO + 1)) (hP2 : Pp.h = 2 ^ (tbQ + 1))
    (hPg : (progTableC heap N W).h = 2 ^ (tpP + 1)) (hSg : (segsPub segRoots).h = 2 ^ (tpS + 1))
    {SM SC S9 SI SO SQ SP SS SX : List F} {ζ : EF} (qv : EF → EF → List EF → F → List F → List F → List EF)
    (wm wc ww wi wo wq wp wsg wx : List (EF → EF → List F))
    (hSM : ∀ x ∈ SM, x ∉ cosetL 1 (bbGen (tbM + 1)) (2 ^ (tbM + 1)))
    (hSC : ∀ x ∈ SC, x ∉ cosetL 1 (bbGen (tbC + 1)) (2 ^ (tbC + 1)))
    (hS9 : ∀ x ∈ S9, x ∉ cosetL 1 (bbGen (8 + 1)) (2 ^ (8 + 1)))
    (hSI : ∀ x ∈ SI, x ∉ cosetL 1 (bbGen (tbI + 1)) (2 ^ (tbI + 1)))
    (hSO : ∀ x ∈ SO, x ∉ cosetL 1 (bbGen (tbO + 1)) (2 ^ (tbO + 1)))
    (hSQ : ∀ x ∈ SQ, x ∉ cosetL 1 (bbGen (tbQ + 1)) (2 ^ (tbQ + 1)))
    (hSP : ∀ x ∈ SP, x ∉ cosetL 1 (bbGen (tpP + 1)) (2 ^ (tpP + 1)))
    (hSS : ∀ x ∈ SS, x ∉ cosetL 1 (bbGen (tpS + 1)) (2 ^ (tpS + 1)))
    (hSX : ∀ x ∈ SX, x ∉ cosetL 1 (bbGen (8 + 1)) (2 ^ (8 + 1)))
    (hszM : 2 * SM.length + 8 ≤ 2 ^ (tbM + 1))
    (hszC : 2 * SC.length + 8 ≤ 2 ^ (tbC + 1))
    (hsz9 : 2 * S9.length + 8 ≤ 2 ^ (8 + 1))
    (hszI : 2 * SI.length + 8 ≤ 2 ^ (tbI + 1))
    (hszO : 2 * SO.length + 8 ≤ 2 ^ (tbO + 1))
    (hszQ : 2 * SQ.length + 8 ≤ 2 ^ (tbQ + 1))
    (hszP : 2 * SP.length + 8 ≤ 2 ^ (tpP + 1))
    (hszS : 2 * SS.length + 8 ≤ 2 ^ (tpS + 1))
    (hszX : 2 * SX.length + 8 ≤ 2 ^ (8 + 1))
    (hζ : ∀ x : F, EF.ofF x ≠ ζ) (hdet : (mz ζ).det ≠ 0) {ncw : Nat} {αb : EF} (fri : EF → EF → List (EF → EF) → V)
    (hdb : (mz αb).det ≠ 0) (haw : ∀ w, apow αb w ≠ EF.zero) (hncw : 4 ≤ ncw) 
    (NR2 : Nat) (Rb : EF → EF → Nat → List (EF → EF)) (Ro : EF → EF → Nat → Wv) :
    let NR := pNR off hd0 stk0 ctr0 n nilA J root heap N W segRoots calls C Mm Wt Pi Po Pp tbM tbC tbI tbO tbQ tpP tpS SM SC S9 SI SO SQ SP SS SX ζ qv wm wc ww wi wo wq wp wsg wx ncw
    PCSCloseN off (NR * NR2)
      (fun pre β t => compPViewN pre β hd0 stk0 ctr0 n nilA J root N W C Mm Wt Pi Po Pp t)
      (fun t α β r => pPcs off hd0 stk0 ctr0 n nilA J root heap N W segRoots calls C Mm Wt Pi Po Pp tbM tbC tbI tbO tbQ tpP tpS SM SC S9 SI SO SQ SP SS SX ζ qv wm wc ww wi wo wq wp wsg wx ncw αb (friX fri Rb Ro (r / NR)) t α β (r % NR))
      (fun α β v r => pPsim off hd0 stk0 ctr0 n nilA J root heap N W segRoots calls C Mm Wt Pi Po Pp tbM tbC tbI tbO tbQ tpP tpS SM SC S9 SI SO SQ SP SS SX ζ qv wm wc ww wi wo wq wp wsg wx ncw αb (friX fri Rb Ro (r / NR)) α β v (r % NR)) 0 :=
  PCSCloseN.family (pcs := fun δ => pPcs off hd0 stk0 ctr0 n nilA J root heap N W segRoots calls C Mm Wt Pi Po Pp tbM tbC tbI tbO tbQ tpP tpS SM SC S9 SI SO SQ SP SS SX ζ qv wm wc ww wi wo wq wp wsg wx ncw αb (friX fri Rb Ro δ))
    (psim := fun δ => pPsim off hd0 stk0 ctr0 n nilA J root heap N W segRoots calls C Mm Wt Pi Po Pp tbM tbC tbI tbO tbQ tpP tpS SM SC S9 SI SO SQ SP SS SX ζ qv wm wc ww wi wo wq wp wsg wx ncw αb (friX fri Rb Ro δ))
    (fun δ => by apply compP_pcs (fri := friX fri Rb Ro δ) <;> assumption)

set_option maxRecDepth 100000 in
/-- **The proof with the Poseidon2 jet over four Fiat–Shamir rounds, the
    query points hashed**: `comp_fs_open4` for the circuit with the
    Poseidon2 jet.  The run is an accepting run of `compPG_complete_log`
    whose verifiers call the jet once (`hcalls`; ski-air's prover refuses
    any other count, `one_call`, and `p2pre`'s and the hand-off's verifiers
    meet it:
    `compP_calls_p2pre`, `compP_calls_p2commit`); the PCS is
    `compP_pcs`'s, over eighteen trace groups and nine quotient tables,
    P2OUT's and Poseidon2's of eight chunks.  Assumed as in
    `comp_fs_open4`. -/
theorem compP_fs_open4 {V Wv P1 P2 P3 : Type} (off : EF → String → EF) {R Lm LI LO LP : Nat} (hR : R ≤ 20)
    (hLm : Lm ≤ 20) (hLI : LI ≤ 20) (hLO : LO ≤ 20) (hLP : LP ≤ 20) {Vs : List OTerm}
    {ρ : Nat → Bool} {region : List Cell} (hrl : region.length = 1)
    (hr : ∀ i c, region[i]? = some c → cellOK (BT.nleaves shpP + 3 + i) c = true)
    {A : List Cell} {e : Nat → Nat} {row : Nat → Air.Row}
    (hA : AcceptsCP A (cMachineO ρ shpP region Vs) [] [] JP2 rootP (cHeapO ρ shpP region Vs).2
      (cHeapO ρ shpP region Vs).1.length Vs.length e row)
    (hlen : A.length = 2 ^ Lm) (hK : e (Vs.length - 1) < 2 ^ R)
    (hHI : ((runP ρ region Vs A e row).pinRows (2 ^ R)).length ≤ 2 ^ LI)
    (hHO : ((runP ρ region Vs A e row).poutRows (2 ^ R)).length ≤ 2 ^ LO)
    (hHP : ((runP ρ region Vs A e row).p2Rows (2 ^ R)).length ≤ 2 ^ LP)
    (hcalls : (runP ρ region Vs A e row).calls (2 ^ R) = 1)
    {tbM tbC tbI tbO tbQ tpP tpS : Nat} (htM : tbM + 1 = Lm) (htC : tbC + 1 = R) (htI : tbI + 1 = LI)
    (htO : tbO + 1 = LO) (htQ : tbQ + 1 = LP)
    (htP : tpP = progTpC (blankMO shpP 1 Vs).heap (BT.nleaves shpP) 1) (htS : tpS = segTp (blankRootsO shpP 1 Vs))
    (SM SC S9 SI SO SQ SP SS SX : Nat → List F) (qv : EF → EF → List EF → F → List F → List F → List EF)
    (wm wc ww wi wo wq wp wsg wx : Nat → List (EF → EF → List F))
    {Lwm Lwc Lww Lwi Lwo Lwq Lwp Lwsg Lwx : Nat}
    (hlwm : ∀ c, (wm c).length = Lwm) (hlwc : ∀ c, (wc c).length = Lwc) (hlww : ∀ c, (ww c).length = Lww) (hlwi : ∀ c, (wi c).length = Lwi) (hlwo : ∀ c, (wo c).length = Lwo) (hlwq : ∀ c, (wq c).length = Lwq) (hlwp : ∀ c, (wp c).length = Lwp) (hlwsg : ∀ c, (wsg c).length = Lwsg) (hlwx : ∀ c, (wx c).length = Lwx)
    {K2 K4 : Nat} (hK2 : 0 < K2) (hK4 : 0 < K4)
    (φ : Nat → Option (List (List (List EF)) × List (List (List (List EF))) × List (List (List EF))) → Nat) {N4 : Nat}
    (hφ : ∀ m w, φ m w < N4)
    (hSM : ∀ c4, ∀ x ∈ SM c4, x ∉ cosetL 1 (bbGen (tbM + 1)) (2 ^ (tbM + 1)))
    (hSC : ∀ c4, ∀ x ∈ SC c4, x ∉ cosetL 1 (bbGen (tbC + 1)) (2 ^ (tbC + 1)))
    (hS9 : ∀ c4, ∀ x ∈ S9 c4, x ∉ cosetL 1 (bbGen (8 + 1)) (2 ^ (8 + 1)))
    (hSI : ∀ c4, ∀ x ∈ SI c4, x ∉ cosetL 1 (bbGen (tbI + 1)) (2 ^ (tbI + 1)))
    (hSO : ∀ c4, ∀ x ∈ SO c4, x ∉ cosetL 1 (bbGen (tbO + 1)) (2 ^ (tbO + 1)))
    (hSQ : ∀ c4, ∀ x ∈ SQ c4, x ∉ cosetL 1 (bbGen (tbQ + 1)) (2 ^ (tbQ + 1)))
    (hSP : ∀ c4, ∀ x ∈ SP c4, x ∉ cosetL 1 (bbGen (tpP + 1)) (2 ^ (tpP + 1)))
    (hSS : ∀ c4, ∀ x ∈ SS c4, x ∉ cosetL 1 (bbGen (tpS + 1)) (2 ^ (tpS + 1)))
    (hSX : ∀ c4, ∀ x ∈ SX c4, x ∉ cosetL 1 (bbGen (8 + 1)) (2 ^ (8 + 1)))
    (hszM : ∀ c4, 2 * (SM c4).length + 8 ≤ 2 ^ (tbM + 1)) (hszC : ∀ c4, 2 * (SC c4).length + 8 ≤ 2 ^ (tbC + 1)) (hsz9 : ∀ c4, 2 * (S9 c4).length + 8 ≤ 2 ^ (8 + 1)) (hszI : ∀ c4, 2 * (SI c4).length + 8 ≤ 2 ^ (tbI + 1)) (hszO : ∀ c4, 2 * (SO c4).length + 8 ≤ 2 ^ (tbO + 1)) (hszQ : ∀ c4, 2 * (SQ c4).length + 8 ≤ 2 ^ (tbQ + 1)) (hszP : ∀ c4, 2 * (SP c4).length + 8 ≤ 2 ^ (tpP + 1)) (hszS : ∀ c4, 2 * (SS c4).length + 8 ≤ 2 ^ (tpS + 1)) (hszX : ∀ c4, 2 * (SX c4).length + 8 ≤ 2 ^ (8 + 1)) {ncw : Nat} (αd : Nat → EF) {B4 : Nat}
    (hB4 : sumTo K4 (fun c4 => indB (!genB (αd c4))) ≤ B4) (fri : Nat → EF → EF → List (EF → EF) → V) (hncw : 4 ≤ ncw)
    (NR2 : Nat) (Rb : Nat → EF → EF → Nat → List (EF → EF)) (Ro : Nat → EF → EF → Nat → Wv)
    {NS1 NS2 NS3 n1 n2 n3 : Nat}
    (Com1 : List (List (List F)) → Nat → Nat) (Pf1 : Nat → List (List (List F)) → Nat → P1) (hc1 : ComHides NS1 Com1)
    (hp1 : ∀ c4, ComPfHides NS1 Com1 (Pf1 c4) (opF ((pGroups tbM tbC tbI tbO tbQ tpP tpS (SM c4) (SC c4) (S9 c4) (SI c4) (SO c4) (SQ c4) (SP c4) (SS c4) (SX c4) EF.zero qv).map (·.base.S)) [0, 2, 4, 6, 8, 10, 12, 14, 16]))
    (hr1 : ∀ d σ, Com1 d σ < n1) (d1 : List (List (List F)))
    (Com2 : List (List (List F)) → Nat → Nat) (Pf2 : Nat → List (List (List F)) → Nat → P2) (hc2 : ComHides NS2 Com2)
    (hp2 : ∀ c4, ComPfHides NS2 Com2 (Pf2 c4) (opF ((pGroups tbM tbC tbI tbO tbQ tpP tpS (SM c4) (SC c4) (S9 c4) (SI c4) (SO c4) (SQ c4) (SP c4) (SS c4) (SX c4) EF.zero qv).map (·.base.S)) [1, 3, 5, 7, 9, 11, 13, 15, 17]))
    (hr2 : ∀ d σ, Com2 d σ < n2) (d2 : List (List (List F)))
    (Com3 : List (List (List (List F))) × List (List (List F)) → Nat → Nat)
    (Pf3 : Nat → List (List (List (List F))) × List (List (List F)) → Nat → P3) (hc3 : ComHides NS3 Com3)
    (hp3 : ∀ c4, ComPfHides NS3 Com3 (Pf3 c4) (fun d => (opQ (pSsT (SM c4) (SC c4) (S9 c4) (SI c4) (SO c4) (SQ c4) (SP c4) (SS c4) (SX c4)) d.1, opCw (pSsC tbM tbC tbI tbO tbQ tpP tpS (SM c4) (SC c4) (S9 c4) (SI c4) (SO c4) (SQ c4) (SP c4) (SS c4) (SX c4)) d.2)))
    (hr3 : ∀ d σ, Com3 d σ < n3) (d3 : List (List (List (List F))) × List (List (List F)))
    (E : Nat → Nat → Nat → Nat → Nat → Nat → Nat → Option P1 × Option (P2 × P3) × TViewN (PcsPV (V × Wv)) ((EF × EF) × EF) → Bool) :
    let m := blankMO shpP 1 Vs
    let segRoots := blankRootsO shpP 1 Vs
    let N := BT.nleaves shpP
    let Rn : P2Run := ⟨A, JP2, rootP, segRoots, e, Vs.length, row⟩
    let C := Rn.cpuTableP (2 ^ R)
    let Pg := progTableC m.heap N 1
    let Wt := witTableP A N 1
    let Pi := Rn.pinTable (2 ^ R) (2 ^ LI)
    let Po := Rn.poutTable (2 ^ R) (2 ^ LO)
    let Pp := Rn.p2Table (2 ^ R) (2 ^ LP)
    let Mm := memTable5 A (cpuAirP2 m.hd m.stk m.heap.length Vs.length m.stk JP2 rootP) (progAirC m.heap N 1)
      p2inAirB p2outAirB (witAirP N 1) C Pg Pi Po Wt
    let NR0 := pNR off m.hd m.stk m.heap.length Vs.length m.stk JP2 rootP m.heap N 1 segRoots 1 C Mm Wt Pi Po Pp tbM tbC tbI tbO tbQ tpP tpS (SM 0) (SC 0) (S9 0) (SI 0) (SO 0) (SQ 0) (SP 0) (SS 0) (SX 0) EF.zero qv (wm 0) (wc 0) (ww 0) (wi 0) (wo 0) (wq 0) (wp 0) (wsg 0) (wx 0) ncw
    let pcsZ := fun (c4 c2 : Nat) (ζ : EF) t α β r => pPcs off m.hd m.stk m.heap.length Vs.length m.stk JP2 rootP m.heap N 1 segRoots 1 C Mm Wt Pi Po Pp tbM tbC tbI tbO tbQ tpP tpS (SM c4) (SC c4) (S9 c4) (SI c4) (SO c4) (SQ c4) (SP c4) (SS c4) (SX c4) ζ qv (wm c2) (wc c2) (ww c2) (wi c2) (wo c2) (wq c2) (wp c2) (wsg c2) (wx c2) ncw (αd c4)
      (friX (fri c4) (Rb c4) (Ro c4) (r / NR0)) t α β (r % NR0)
    let psimZ := fun (c4 c2 : Nat) (ζ : EF) α β v r => pPsim off m.hd m.stk m.heap.length Vs.length m.stk JP2 rootP m.heap N 1 segRoots 1 C Mm Wt Pi Po Pp tbM tbC tbI tbO tbQ tpP tpS (SM c4) (SC c4) (S9 c4) (SI c4) (SO c4) (SQ c4) (SP c4) (SS c4) (SX c4) ζ qv (wm c2) (wc c2) (ww c2) (wi c2) (wo c2) (wq c2) (wp c2) (wsg c2) (wx c2) ncw (αd c4)
      (friX (fri c4) (Rb c4) (Ro c4) (r / NR0)) α β v (r % NR0)
    let NR := NR0 * NR2
    let tabs := fun t : Nat → Tup => compPTables m.hd m.stk m.heap.length Vs.length m.stk JP2 rootP m.heap N 1 segRoots
      (((C.setBlind BLA (t 1)).setBlind BLB (t 0)).setBlind (P2SEL + 1) (t 2)) (Mm.setBlind 5 (t 0))
      (progTableC m.heap N 1) (Wt.setBlind WT_BLIND (t 1)) (segsPub segRoots)
      ((Pi.setBlind p2inAir.width (t 2)).setBlind (p2inAir.width + 5) (t 3))
      ((Po.setBlind p2outAir.width (t 3)).setBlind (p2outAir.width + 5) (t 4))
      (Pp.setBlind P2Air.p2Air.width (t 4)) (idxPub 1)
    let tv := fun pre β t => compPViewN pre β m.hd m.stk m.heap.length Vs.length m.stk JP2 rootP N 1 C Mm Wt Pi Po Pp t
    let pb := fun pre β => ((terminal pre β (progAirC m.heap N 1) (progTableC m.heap N 1),
      terminal pre β (segsAir segRoots) (segsPub segRoots)), terminal pre β p2idxAir (idxPub 1))
    let ptm := fun pre β => ((terminal pre β (progAirC m.heap N 1) (progTableC m.heap N 1)).add
      (terminal pre β (segsAir segRoots) (segsPub segRoots))).add (terminal pre β p2idxAir (idxPub 1))
    let M := (allEntries (compPTables m.hd m.stk m.heap.length Vs.length m.stk JP2 rootP m.heap N 1 segRoots C Mm
      (progTableC m.heap N 1) Wt (segsPub segRoots) Pi Po Pp (idxPub 1))).length
    let q0 := pGroups tbM tbC tbI tbO tbQ tpP tpS (SM 0) (SC 0) (S9 0) (SI 0) (SO 0) (SQ 0) (SP 0) (SS 0) (SX 0) EF.zero qv
    let qZ := fun (c4 : Nat) (ζ : EF) => pGroups tbM tbC tbI tbO tbQ tpP tpS (SM c4) (SC c4) (S9 c4) (SI c4) (SO c4) (SQ c4) (SP c4) (SS c4) (SX c4) ζ qv
    let Ss := fun c4 => (qZ c4 EF.zero).map (·.base.S)
    let ks := pKs m.hd m.stk m.heap.length Vs.length m.stk JP2 rootP m.heap N 1 segRoots
    let cols := pCols off m.hd m.stk m.heap.length Vs.length m.stk JP2 rootP N 1 m.heap segRoots 1 C Mm Wt Pi Po Pp
    let tqZ := fun (c4 c2 : Nat) (ζ : EF) => (pTs off m.hd m.stk m.heap.length Vs.length m.stk JP2 rootP m.heap N 1 segRoots 1 C Mm Wt Pi Po Pp tbM tbC tbI tbO tbQ tpP tpS (SM c4) (SC c4) (S9 c4) (SI c4) (SO c4) (SQ c4) (SP c4) (SS c4) (SX c4) ζ qv (wm c2) (wc c2) (ww c2) (wi c2) (wo c2) (wq c2) (wp c2) (wsg c2) (wx c2)).map Prod.fst
    let qdZ := fun (c4 c2 : Nat) (ζ : EF) (t : Nat → Tup) (α β : EF) (ms : List F) =>
      (pTs off m.hd m.stk m.heap.length Vs.length m.stk JP2 rootP m.heap N 1 segRoots 1 C Mm Wt Pi Po Pp tbM tbC tbI tbO tbQ tpP tpS (SM c4) (SC c4) (S9 c4) (SI c4) (SO c4) (SQ c4) (SP c4) (SS c4) (SX c4) ζ qv (wm c2) (wc c2) (ww c2) (wi c2) (wo c2) (wq c2) (wp c2) (wsg c2) (wx c2)).map (fun p => p.2 t α β ms)
    let SsT := fun c4 => (tqZ c4 0 EF.zero).map (·.S)
    let SsC := fun c4 => (tabsInfo ncw (tqZ c4 0 EF.zero)).map (·.S)
    let mk1 := [0, 2, 4, 6, 8, 10, 12, 14, 16]
    let mk2 := [1, 3, 5, 7, 9, 11, 13, 15, 17]
    let main1 := fun (t : Nat → Tup) (r : Nat) => mainF2 q0 ks cols (tqZ 0 0 EF.zero) ncw mk1 t (r % NR0)
    let main2 := fun (c1 : Nat) (t : Nat → Tup) (r : Nat) =>
      mainP2 q0 ks cols (tqZ 0 0 EF.zero) ncw mk2 t (efOf (c1 / Q4)) (efOf (c1 % Q4)) (r % NR0)
    let main3 := fun (c1 c2 : Nat) (t : Nat → Tup) (r : Nat) =>
      (tabsPolys (tqZ 0 c2 EF.zero) (qdZ 0 c2 EF.zero t (efOf (c1 / Q4)) (efOf (c1 % Q4))
          (msF q0 ks (tqZ 0 c2 EF.zero) ncw (r % NR0))) (crF q0 ks (tqZ 0 c2 EF.zero) ncw (r % NR0)),
       tabsCws ncw (tqZ 0 c2 EF.zero) (ccF q0 ks (tqZ 0 c2 EF.zero) ncw (r % NR0)))
    let vS := fun (α β : EF) (t : Nat → Tup) => viewT β (fun k => prefixOf α (off β) (jetBus k)) jetSg
      jetPar 6 (xrefN (ptm (prefixOf α (off β)) β)) t
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
    let ov1 : Nat → TViewN (PcsPV (V × Wv)) ((EF × EF) × EF) → Option (List (List (List F))) := fun c4 v => match v with
      | some (pv, _) => some (ovF2 (Ss c4) mk1 pv)
      | none => none
    let ov2 : Nat → TViewN (PcsPV (V × Wv)) ((EF × EF) × EF) → Option (List (List (List F))) := fun c4 v => match v with
      | some (pv, _) => some (ovF2 (Ss c4) mk2 pv)
      | none => none
    let ov3 : Nat → TViewN (PcsPV (V × Wv)) ((EF × EF) × EF) → Option (List (List (List (List F))) × List (List (List F))) :=
      fun _ v => match v with
      | some (pv, _) => some (ovQ pv, cwQ 18 pv)
      | none => none
    let rvF := fun (c4 c2 c3 : Nat) (α β : EF) (r : Nat) (t : Nat → Tup) =>
      realVN off tabs tv pb (pcsZ c4 c2 (efOf c3)) α β r t
    let svF := fun (c4 c2 c3 : Nat) (α β : EF) (r : Nat) (t : Nat → Tup) =>
      simVN off pb jetBus jetSg jetPar 6 ptm (psimZ c4 c2 (efOf c3)) α β r t
    let ozF : TViewN (PcsPV (V × Wv)) ((EF × EF) × EF) → Option (List (List (List EF)) × List (List (List (List EF))) × List (List (List EF))) := fun v => match v with
      | some (pv, _) => some (pv.1.1.map (fun g => g.1.map Prod.snd), pv.1.2.map (List.map (List.map Prod.snd)),
        pv.2.1.map (List.map Prod.snd))
      | none => none
    let op3 := fun (c4 : Nat) (d : List (List (List (List F))) × List (List (List F))) =>
      (opQ (SsT c4) d.1, opCw (SsC c4) d.2)
    let sd3 := fun (c4 : Nat) (o : List (List (List (List F))) × List (List (List F))) =>
      (sdQ (SsT c4) o.1, sdCw (SsC c4) o.2)
    let sm := fun (g : Nat × Nat × Nat × (Nat → Tup) → Nat) =>
      sumTo NS1 (fun σ1 => sumTo (NS2 * NS3) (fun σ => sumTo NR (fun r => sumN 5 (fun t => g (σ1, σ, r, t)))))
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
          (K2 * (Q4 * (NS1 * (NS2 * NS3 * (Q4 * (NR * (Q4 ^ 5 * M)) + Q4 * (Q4 * (Q4 ^ 5 * 0)))))) +
            (Q4 * (P * P) * (K2 * Q4) + Q4 * Q4 * (K2 * (P * P))) * (NS1 * (NS2 * NS3 * (NR * (Q4 ^ 5 * 1)))))))) +
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
          (K2 * (Q4 * (NS1 * (NS2 * NS3 * (Q4 * (NR * (Q4 ^ 5 * M)) + Q4 * (Q4 * (Q4 ^ 5 * 0)))))) +
            (Q4 * (P * P) * (K2 * Q4) + Q4 * Q4 * (K2 * (P * P))) * (NS1 * (NS2 * NS3 * (NR * (Q4 ^ 5 * 1)))))))) +
            B4 * (Q4 * Q4 * (K2 * Q4) * sm4 (fun _ => 1)))) := by
  intro m segRoots N Rn C Pg Wt Pi Po Pp Mm NR0 pcsZ psimZ NR tabs tv pb ptm M q0 qZ Ss ks cols tqZ qdZ SsT SsC mk1 mk2 main1 main2 main3 vS sop1 sop2 sop3 ov1 ov2 ov3 rvF svF ozF op3 sd3
  obtain ⟨⟨hbal, hun⟩, ⟨sc, sms, sw, si, so, sq⟩, ⟨hC0, hM0, hWh, hI0, hO0, hQ0, p1, p2, s1, s2⟩⟩ :=
    compP_run_facts hR hLm hLI hLO hLP hrl hr hA hlen hK hHI hHO hHP hcalls
  rw [← htP] at p1 p2
  rw [← htS] at s1 s2
  have hM : Mm.h = 2 ^ (tbM + 1) := by rw [htM]; exact hM0
  have hC : C.h = 2 ^ (tbC + 1) := by rw [htC]; exact hC0
  have hI : Pi.h = 2 ^ (tbI + 1) := by rw [htI]; exact hI0
  have hO : Po.h = 2 ^ (tbO + 1) := by rw [htO]; exact hO0
  have hQ : Pp.h = 2 ^ (tbQ + 1) := by rw [htQ]; exact hQ0
  have hSw := fun (c4 c2 c3 : Nat) => compP_same_w off m.hd m.stk m.heap.length Vs.length m.stk JP2 rootP m.heap N 1 segRoots 1 C Mm Wt Pi Po Pp tbM tbC tbI tbO tbQ tpP tpS (SM c4) (SC c4) (S9 c4) (SI c4) (SO c4) (SQ c4) (SP c4) (SS c4) (SX c4) (efOf c3) EF.zero qv (wm c2) (wc c2) (ww c2) (wi c2) (wo c2) (wq c2) (wp c2) (wsg c2) (wx c2) (wm 0) (wc 0) (ww 0) (wi 0) (wo 0) (wq 0) (wp 0) (wsg 0) (wx 0) ncw (by rw [hlwm, hlwm]) (by rw [hlwc, hlwc]) (by rw [hlww, hlww]) (by rw [hlwi, hlwi]) (by rw [hlwo, hlwo]) (by rw [hlwq, hlwq]) (by rw [hlwp, hlwp]) (by rw [hlwsg, hlwsg]) (by rw [hlwx, hlwx])
  have hSz := fun (c4 c2 c3 : Nat) => compP_same_w off m.hd m.stk m.heap.length Vs.length m.stk JP2 rootP m.heap N 1 segRoots 1 C Mm Wt Pi Po Pp tbM tbC tbI tbO tbQ tpP tpS (SM c4) (SC c4) (S9 c4) (SI c4) (SO c4) (SQ c4) (SP c4) (SS c4) (SX c4) (efOf c3) EF.zero qv (wm c2) (wc c2) (ww c2) (wi c2) (wo c2) (wq c2) (wp c2) (wsg c2) (wx c2) (wm c2) (wc c2) (ww c2) (wi c2) (wo c2) (wq c2) (wp c2) (wsg c2) (wx c2) ncw rfl rfl rfl rfl rfl rfl rfl rfl rfl
  have hS0 := fun (c4 c2 : Nat) => compP_same_w off m.hd m.stk m.heap.length Vs.length m.stk JP2 rootP m.heap N 1 segRoots 1 C Mm Wt Pi Po Pp tbM tbC tbI tbO tbQ tpP tpS (SM c4) (SC c4) (S9 c4) (SI c4) (SO c4) (SQ c4) (SP c4) (SS c4) (SX c4) EF.zero EF.zero qv (wm c2) (wc c2) (ww c2) (wi c2) (wo c2) (wq c2) (wp c2) (wsg c2) (wx c2) (wm 0) (wc 0) (ww 0) (wi 0) (wo 0) (wq 0) (wp 0) (wsg 0) (wx 0) ncw (by rw [hlwm, hlwm]) (by rw [hlwc, hlwc]) (by rw [hlww, hlww]) (by rw [hlwi, hlwi]) (by rw [hlwo, hlwo]) (by rw [hlwq, hlwq]) (by rw [hlwp, hlwp]) (by rw [hlwsg, hlwsg]) (by rw [hlwx, hlwx])
  have hSd := fun (c4 c2 c3 : Nat) => compP_same_d off m.hd m.stk m.heap.length Vs.length m.stk JP2 rootP m.heap N 1 segRoots 1 C Mm Wt Pi Po Pp tbM tbC tbI tbO tbQ tpP tpS (SM c4) (SC c4) (S9 c4) (SI c4) (SO c4) (SQ c4) (SP c4) (SS c4) (SX c4) (SM 0) (SC 0) (S9 0) (SI 0) (SO 0) (SQ 0) (SP 0) (SS 0) (SX 0) (efOf c3) EF.zero qv (wm c2) (wc c2) (ww c2) (wi c2) (wo c2) (wq c2) (wp c2) (wsg c2) (wx c2) (wm 0) (wc 0) (ww 0) (wi 0) (wo 0) (wq 0) (wp 0) (wsg 0) (wx 0) (by rw [hlwm, hlwm]) (by rw [hlwc, hlwc]) (by rw [hlww, hlww]) (by rw [hlwi, hlwi]) (by rw [hlwo, hlwo]) (by rw [hlwq, hlwq]) (by rw [hlwp, hlwp]) (by rw [hlwsg, hlwsg]) (by rw [hlwx, hlwx])
  have hSdz := fun (c4 c2 c3 : Nat) => compP_same_d off m.hd m.stk m.heap.length Vs.length m.stk JP2 rootP m.heap N 1 segRoots 1 C Mm Wt Pi Po Pp tbM tbC tbI tbO tbQ tpP tpS (SM c4) (SC c4) (S9 c4) (SI c4) (SO c4) (SQ c4) (SP c4) (SS c4) (SX c4) (SM 0) (SC 0) (S9 0) (SI 0) (SO 0) (SQ 0) (SP 0) (SS 0) (SX 0) (efOf c3) EF.zero qv (wm c2) (wc c2) (ww c2) (wi c2) (wo c2) (wq c2) (wp c2) (wsg c2) (wx c2) (wm c2) (wc c2) (ww c2) (wi c2) (wo c2) (wq c2) (wp c2) (wsg c2) (wx c2) rfl rfl rfl rfl rfl rfl rfl rfl rfl
  have hb : ∀ c4 c2 c3, genB (αd c4) = true → genB (efOf c3) = true →
      (∀ E' : TViewN (PcsPV (V × Wv)) ((EF × EF) × EF) → Bool,
        tsumN NR 5 (fun α β r t => indB (genB β && E' (rvF c4 c2 c3 α β r t))) ≤
          tsumN NR 5 (fun α β r t => indB (genB β && E' (svF c4 c2 c3 α β r t))) + Q4 * (NR * (Q4 ^ 5 * M)) +
            Q4 * (Q4 * (Q4 ^ 5 * 0))) ∧
      (∀ E' : TViewN (PcsPV (V × Wv)) ((EF × EF) × EF) → Bool,
        tsumN NR 5 (fun α β r t => indB (genB β && E' (svF c4 c2 c3 α β r t))) ≤
          tsumN NR 5 (fun α β r t => indB (genB β && E' (rvF c4 c2 c3 α β r t))) + Q4 * (NR * (Q4 ^ 5 * M)) +
            Q4 * (Q4 * (Q4 ^ 5 * 0))) := fun c4 c2 c3 hg4 hg => by
    have hgz := (genB_iff _).1 hg
    have hgα := (genB_iff _).1 hg4
    have hpcs := compP_pcsX (heap := m.heap) (ζ := efOf c3) (segRoots := segRoots) (calls := 1) off sms sc sw si so sq (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      hM hC hWh hI hO hQ p2 s2 qv (wm c2) (wc c2) (ww c2) (wi c2) (wo c2) (wq c2) (wp c2) (wsg c2) (wx c2) (hSM c4) (hSC c4) (hS9 c4) (hSI c4) (hSO c4) (hSQ c4) (hSP c4) (hSS c4) (hSX c4) (hszM c4) (hszC c4) (hsz9 c4) (hszI c4) (hszO c4) (hszQ c4) (hszP c4) (hszS c4) (hszX c4) (generic_ofF_ne hgz) (mz_generic hgz) (fri c4) (mz_generic hgα) (generic_apow_ne hgα) hncw NR2 (Rb c4) (Ro c4)
    have hNR : pNR off m.hd m.stk m.heap.length Vs.length m.stk JP2 rootP m.heap N 1 segRoots 1 C Mm Wt Pi Po Pp tbM tbC tbI tbO tbQ tpP tpS (SM c4) (SC c4) (S9 c4) (SI c4) (SO c4) (SQ c4) (SP c4) (SS c4) (SX c4) (efOf c3) qv (wm c2) (wc c2) (ww c2) (wi c2) (wo c2) (wq c2) (wp c2) (wsg c2) (wx c2) ncw = pNR off m.hd m.stk m.heap.length Vs.length m.stk JP2 rootP m.heap N 1 segRoots 1 C Mm Wt Pi Po Pp tbM tbC tbI tbO tbQ tpP tpS (SM 0) (SC 0) (S9 0) (SI 0) (SO 0) (SQ 0) (SP 0) (SS 0) (SX 0) EF.zero qv (wm 0) (wc 0) (ww 0) (wi 0) (wo 0) (wq 0) (wp 0) (wsg 0) (wx 0) ncw := by
      unfold pNR; rw [(hSd c4 c2 c3).n1, (hSd c4 c2 c3).n2]
    rw [hNR] at hpcs
    exact ⟨fun E' => (compP_transcriptG off NR 0 1 (pcsZ c4 c2 (efOf c3)) (psimZ c4 c2 (efOf c3)) hbal hun hpcs E').1,
      fun E' => (compP_transcriptG off NR 0 1 (pcsZ c4 c2 (efOf c3)) (psimZ c4 c2 (efOf c3)) hbal hun hpcs E').2⟩
  have hlen8 : ∀ (c4 : Nat) (ζ : EF) t α β, (cols t α β).map List.length = (cols t EF.zero EF.zero).map List.length :=
    fun c4 ζ t α β => by
      rw [(pCols_shaped off m.hd m.stk m.heap.length Vs.length m.stk JP2 rootP 1 hM hC hWh hI hO hQ p2 s2
          (SM c4) (SC c4) (S9 c4) (SI c4) (SO c4) (SQ c4) (SP c4) (SS c4) (SX c4) ζ qv t α β).2,
        (pCols_shaped off m.hd m.stk m.heap.length Vs.length m.stk JP2 rootP 1 hM hC hWh hI hO hQ p2 s2
          (SM c4) (SC c4) (S9 c4) (SI c4) (SO c4) (SQ c4) (SP c4) (SS c4) (SX c4) ζ qv t EF.zero EF.zero).2]
  have hmk1 : ∀ k ∈ mk1, k < 18 ∧ ∀ t α β, k < (cols t α β).length ∧
      (cols t α β).getD k [] = (cols t EF.zero EF.zero).getD k [] := by
    intro k hk
    have hk' := hk
    simp only [mk1, List.mem_cons, List.not_mem_nil, or_false] at hk'
    have hkn : k < 18 := by rcases hk' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact ⟨hkn, fun t α β => ⟨hkn, compPCols_main off m.hd m.stk m.heap.length Vs.length m.stk JP2 rootP m.heap N 1 segRoots 1 C Mm Wt Pi Po Pp t α β
      EF.zero EF.zero k hk⟩⟩
  have hmk2 : ∀ k ∈ mk2, k < 18 ∧ ∀ t α β, k < (cols t α β).length := by
    intro k hk
    simp only [mk2, List.mem_cons, List.not_mem_nil, or_false] at hk
    have hkn : k < 18 := by rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact ⟨hkn, fun _ _ _ => hkn⟩
  have hvo1 : ∀ c4 c2 c3 c r t, rvF c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t = none ∨
      ov1 c4 (rvF c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (opF (Ss c4) mk1 (main1 t r)) := by
    intro c4 c2 c3 c r t
    show realVN off tabs tv pb (pcsZ c4 c2 (efOf c3)) _ _ r t = none ∨
      ov1 c4 (realVN off tabs tv pb (pcsZ c4 c2 (efOf c3)) _ _ r t) = _
    unfold realVN
    split
    · exact .inl rfl
    · have e := pcsFri_ov2 off (fun pre β t => compPViewN pre β m.hd m.stk m.heap.length Vs.length m.stk JP2 rootP N 1 C Mm Wt Pi Po Pp t) (pGroups tbM tbC tbI tbO tbQ tpP tpS (SM c4) (SC c4) (S9 c4) (SI c4) (SO c4) (SQ c4) (SP c4) (SS c4) (SX c4) (efOf c3) qv) ks cols ((pTs off m.hd m.stk m.heap.length Vs.length m.stk JP2 rootP m.heap N 1 segRoots 1 C Mm Wt Pi Po Pp tbM tbC tbI tbO tbQ tpP tpS (SM c4) (SC c4) (S9 c4) (SI c4) (SO c4) (SQ c4) (SP c4) (SS c4) (SX c4) (efOf c3) qv (wm c2) (wc c2) (ww c2) (wi c2) (wo c2) (wq c2) (wp c2) (wsg c2) (wx c2)).map Prod.fst) (fun t α β ms => (pTs off m.hd m.stk m.heap.length Vs.length m.stk JP2 rootP m.heap N 1 segRoots 1 C Mm Wt Pi Po Pp tbM tbC tbI tbO tbQ tpP tpS (SM c4) (SC c4) (S9 c4) (SI c4) (SO c4) (SQ c4) (SP c4) (SS c4) (SX c4) (efOf c3) qv (wm c2) (wc c2) (ww c2) (wi c2) (wo c2) (wq c2) (wp c2) (wsg c2) (wx c2)).map fun p => p.2 t α β ms) ncw (αd c4)
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
    · have e := pcsFri_ovP off (fun pre β t => compPViewN pre β m.hd m.stk m.heap.length Vs.length m.stk JP2 rootP N 1 C Mm Wt Pi Po Pp t) (pGroups tbM tbC tbI tbO tbQ tpP tpS (SM c4) (SC c4) (S9 c4) (SI c4) (SO c4) (SQ c4) (SP c4) (SS c4) (SX c4) (efOf c3) qv) ks cols ((pTs off m.hd m.stk m.heap.length Vs.length m.stk JP2 rootP m.heap N 1 segRoots 1 C Mm Wt Pi Po Pp tbM tbC tbI tbO tbQ tpP tpS (SM c4) (SC c4) (S9 c4) (SI c4) (SO c4) (SQ c4) (SP c4) (SS c4) (SX c4) (efOf c3) qv (wm c2) (wc c2) (ww c2) (wi c2) (wo c2) (wq c2) (wp c2) (wsg c2) (wx c2)).map Prod.fst) (fun t α β ms => (pTs off m.hd m.stk m.heap.length Vs.length m.stk JP2 rootP m.heap N 1 segRoots 1 C Mm Wt Pi Po Pp tbM tbC tbI tbO tbQ tpP tpS (SM c4) (SC c4) (S9 c4) (SI c4) (SO c4) (SQ c4) (SP c4) (SS c4) (SX c4) (efOf c3) qv (wm c2) (wc c2) (ww c2) (wi c2) (wo c2) (wq c2) (wp c2) (wsg c2) (wx c2)).map fun p => p.2 t α β ms) ncw (αd c4)
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
      have e0 := pcsFri_ovR2 off (fun pre β t => compPViewN pre β m.hd m.stk m.heap.length Vs.length m.stk JP2 rootP N 1 C Mm Wt Pi Po Pp t) (pGroups tbM tbC tbI tbO tbQ tpP tpS (SM c4) (SC c4) (S9 c4) (SI c4) (SO c4) (SQ c4) (SP c4) (SS c4) (SX c4) (efOf c3) qv) ks cols ((pTs off m.hd m.stk m.heap.length Vs.length m.stk JP2 rootP m.heap N 1 segRoots 1 C Mm Wt Pi Po Pp tbM tbC tbI tbO tbQ tpP tpS (SM c4) (SC c4) (S9 c4) (SI c4) (SO c4) (SQ c4) (SP c4) (SS c4) (SX c4) (efOf c3) qv (wm c2) (wc c2) (ww c2) (wi c2) (wo c2) (wq c2) (wp c2) (wsg c2) (wx c2)).map Prod.fst) (fun t α β ms => (pTs off m.hd m.stk m.heap.length Vs.length m.stk JP2 rootP m.heap N 1 segRoots 1 C Mm Wt Pi Po Pp tbM tbC tbI tbO tbQ tpP tpS (SM c4) (SC c4) (S9 c4) (SI c4) (SO c4) (SQ c4) (SP c4) (SS c4) (SX c4) (efOf c3) qv (wm c2) (wc c2) (ww c2) (wi c2) (wo c2) (wq c2) (wp c2) (wsg c2) (wx c2)).map fun p => p.2 t α β ms) ncw (αd c4)
        (friX (fri c4) (Rb c4) (Ro c4) (r / NR0)) mk2 hmk2 rfl t (efOf (c / Q4)) (efOf (c % Q4)) (r % NR0)
      have e := congrArg Prod.snd e0
      rw [(hSz c4 c2 c3).tS, (hSz c4 c2 c3).iS, tabsPolys_congr _ _ _ _ (hSdz c4 c2 c3).shape,
        tabsCws_congr ncw _ _ _ (hSdz c4 c2 c3).shape, (hSdz c4 c2 c3).cr (r % NR0), (hSdz c4 c2 c3).cc (r % NR0),
        (hSdz c4 c2 c3).ms (r % NR0), (hS0 c4 c2).tS, (hS0 c4 c2).iS,
        compP_data_q off m.hd m.stk m.heap.length Vs.length m.stk JP2 rootP m.heap N 1 segRoots 1 C Mm Wt Pi Po Pp tbM tbC tbI tbO tbQ tpP tpS (SM c4) (SC c4) (S9 c4) (SI c4) (SO c4) (SQ c4) (SP c4) (SS c4) (SX c4) (SM 0) (SC 0) (S9 0) (SI 0) (SO 0) (SQ 0) (SP 0) (SS 0) (SX 0) (efOf c3) EF.zero
          qv (wm c2) (wc c2) (ww c2) (wi c2) (wo c2) (wq c2) (wp c2) (wsg c2) (wx c2) t _ _ _ hab'] at e
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
    have e0 := psimFri_ovR2 (pGroups tbM tbC tbI tbO tbQ tpP tpS (SM c4) (SC c4) (S9 c4) (SI c4) (SO c4) (SQ c4) (SP c4) (SS c4) (SX c4) (efOf c3) qv) ks ((pTs off m.hd m.stk m.heap.length Vs.length m.stk JP2 rootP m.heap N 1 segRoots 1 C Mm Wt Pi Po Pp tbM tbC tbI tbO tbQ tpP tpS (SM c4) (SC c4) (S9 c4) (SI c4) (SO c4) (SQ c4) (SP c4) (SS c4) (SX c4) (efOf c3) qv (wm c2) (wc c2) (ww c2) (wi c2) (wo c2) (wq c2) (wp c2) (wsg c2) (wx c2)).map Prod.fst) ncw (αd c4) (friX (fri c4) (Rb c4) (Ro c4) (r / NR0)) mk2
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
    have e1 : SsT c4 = pSsT (SM c4) (SC c4) (S9 c4) (SI c4) (SO c4) (SQ c4) (SP c4) (SS c4) (SX c4) := compP_SsT off m.hd m.stk m.heap.length Vs.length m.stk JP2 rootP m.heap N 1 segRoots 1 C Mm Wt Pi Po Pp tbM tbC tbI tbO tbQ tpP tpS (SM c4) (SC c4) (S9 c4) (SI c4) (SO c4) (SQ c4) (SP c4) (SS c4) (SX c4) EF.zero qv (wm 0) (wc 0) (ww 0) (wi 0) (wo 0) (wq 0) (wp 0) (wsg 0) (wx 0)
    have e2 : SsC c4 = pSsC tbM tbC tbI tbO tbQ tpP tpS (SM c4) (SC c4) (S9 c4) (SI c4) (SO c4) (SQ c4) (SP c4) (SS c4) (SX c4) := compP_SsC off m.hd m.stk m.heap.length Vs.length m.stk JP2 rootP m.heap N 1 segRoots 1 C Mm Wt Pi Po Pp tbM tbC tbI tbO tbQ tpP tpS (SM c4) (SC c4) (S9 c4) (SI c4) (SO c4) (SQ c4) (SP c4) (SS c4) (SX c4) EF.zero qv (wm 0) (wc 0) (ww 0) (wi 0) (wo 0) (wq 0) (wp 0) (wsg 0) (wx 0) ncw
    show ComPfHides NS3 Com3 (Pf3 c4) (fun d => (opQ (SsT c4) d.1, opCw (SsC c4) d.2))
    rw [e1, e2]; exact hp3 c4
  have hoz : ∀ c4 c2 c3 α β r t, ozF (rvF c4 c2 c3 α β r t) = ozF (rvF 0 c2 c3 α β r t) := by
    intro c4 c2 c3 α β r t
    simp only [rvF]
    unfold realVN
    cases hA : Aborts (prefixOf α (off β)) β (tabs t)
    · simp only [Bool.false_eq_true, ↓reduceIte, ozF, Option.some.injEq, Prod.mk.injEq]
      have hd := compP_same_d off m.hd m.stk m.heap.length Vs.length m.stk JP2 rootP m.heap N 1 segRoots 1 C Mm Wt Pi Po Pp tbM tbC tbI tbO tbQ tpP tpS (SM c4) (SC c4) (S9 c4) (SI c4) (SO c4) (SQ c4) (SP c4) (SS c4) (SX c4) (SM 0) (SC 0) (S9 0) (SI 0) (SO 0) (SQ 0) (SP 0) (SS 0) (SX 0) (efOf c3) (efOf c3) qv (wm c2) (wc c2) (ww c2) (wi c2) (wo c2) (wq c2) (wp c2) (wsg c2) (wx c2) (wm c2) (wc c2) (ww c2) (wi c2) (wo c2) (wq c2) (wp c2) (wsg c2) (wx c2) rfl rfl rfl rfl rfl rfl rfl rfl rfl
      refine ⟨pcsFri_ood off (fun pre β t => compPViewN pre β m.hd m.stk m.heap.length Vs.length m.stk JP2 rootP N 1 C Mm Wt Pi Po Pp t) (pGroups tbM tbC tbI tbO tbQ tpP tpS (SM c4) (SC c4) (S9 c4) (SI c4) (SO c4) (SQ c4) (SP c4) (SS c4) (SX c4) (efOf c3) qv) (pGroups tbM tbC tbI tbO tbQ tpP tpS (SM 0) (SC 0) (S9 0) (SI 0) (SO 0) (SQ 0) (SP 0) (SS 0) (SX 0) (efOf c3) qv) ks cols
        ((pTs off m.hd m.stk m.heap.length Vs.length m.stk JP2 rootP m.heap N 1 segRoots 1 C Mm Wt Pi Po Pp tbM tbC tbI tbO tbQ tpP tpS (SM c4) (SC c4) (S9 c4) (SI c4) (SO c4) (SQ c4) (SP c4) (SS c4) (SX c4) (efOf c3) qv (wm c2) (wc c2) (ww c2) (wi c2) (wo c2) (wq c2) (wp c2) (wsg c2) (wx c2)).map Prod.fst) ((pTs off m.hd m.stk m.heap.length Vs.length m.stk JP2 rootP m.heap N 1 segRoots 1 C Mm Wt Pi Po Pp tbM tbC tbI tbO tbQ tpP tpS (SM 0) (SC 0) (S9 0) (SI 0) (SO 0) (SQ 0) (SP 0) (SS 0) (SX 0) (efOf c3) qv (wm c2) (wc c2) (ww c2) (wi c2) (wo c2) (wq c2) (wp c2) (wsg c2) (wx c2)).map Prod.fst) _ _ ncw (αd c4) (αd 0) _ _
        hd rfl rfl t α β (r % NR0), pcsFri_oodT off (fun pre β t => compPViewN pre β m.hd m.stk m.heap.length Vs.length m.stk JP2 rootP N 1 C Mm Wt Pi Po Pp t) (pGroups tbM tbC tbI tbO tbQ tpP tpS (SM c4) (SC c4) (S9 c4) (SI c4) (SO c4) (SQ c4) (SP c4) (SS c4) (SX c4) (efOf c3) qv) (pGroups tbM tbC tbI tbO tbQ tpP tpS (SM 0) (SC 0) (S9 0) (SI 0) (SO 0) (SQ 0) (SP 0) (SS 0) (SX 0) (efOf c3) qv) ks cols
        ((pTs off m.hd m.stk m.heap.length Vs.length m.stk JP2 rootP m.heap N 1 segRoots 1 C Mm Wt Pi Po Pp tbM tbC tbI tbO tbQ tpP tpS (SM c4) (SC c4) (S9 c4) (SI c4) (SO c4) (SQ c4) (SP c4) (SS c4) (SX c4) (efOf c3) qv (wm c2) (wc c2) (ww c2) (wi c2) (wo c2) (wq c2) (wp c2) (wsg c2) (wx c2)).map Prod.fst) ((pTs off m.hd m.stk m.heap.length Vs.length m.stk JP2 rootP m.heap N 1 segRoots 1 C Mm Wt Pi Po Pp tbM tbC tbI tbO tbQ tpP tpS (SM 0) (SC 0) (S9 0) (SI 0) (SO 0) (SQ 0) (SP 0) (SS 0) (SX 0) (efOf c3) qv (wm c2) (wc c2) (ww c2) (wi c2) (wo c2) (wq c2) (wp c2) (wsg c2) (wx c2)).map Prod.fst) _ _ ncw (αd c4) (αd 0) _ _
        hd (by simp only [pTs, bbTabL, airQTabG, List.map_cons, List.map_nil]) t α β (r % NR0)
        (compP_data_q off m.hd m.stk m.heap.length Vs.length m.stk JP2 rootP m.heap N 1 segRoots 1 C Mm Wt Pi Po Pp tbM tbC tbI tbO tbQ tpP tpS (SM c4) (SC c4) (S9 c4) (SI c4) (SO c4) (SQ c4) (SP c4) (SS c4) (SX c4) (SM 0) (SC 0) (S9 0) (SI 0) (SO 0) (SQ 0) (SP 0) (SS 0) (SX 0) (efOf c3) (efOf c3) qv (wm c2) (wc c2) (ww c2) (wi c2) (wo c2) (wq c2) (wp c2) (wsg c2) (wx c2) t _ _ _ hA),
        pcsFri_oodC off (fun pre β t => compPViewN pre β m.hd m.stk m.heap.length Vs.length m.stk JP2 rootP N 1 C Mm Wt Pi Po Pp t) (pGroups tbM tbC tbI tbO tbQ tpP tpS (SM c4) (SC c4) (S9 c4) (SI c4) (SO c4) (SQ c4) (SP c4) (SS c4) (SX c4) (efOf c3) qv) (pGroups tbM tbC tbI tbO tbQ tpP tpS (SM 0) (SC 0) (S9 0) (SI 0) (SO 0) (SQ 0) (SP 0) (SS 0) (SX 0) (efOf c3) qv) ks cols
        ((pTs off m.hd m.stk m.heap.length Vs.length m.stk JP2 rootP m.heap N 1 segRoots 1 C Mm Wt Pi Po Pp tbM tbC tbI tbO tbQ tpP tpS (SM c4) (SC c4) (S9 c4) (SI c4) (SO c4) (SQ c4) (SP c4) (SS c4) (SX c4) (efOf c3) qv (wm c2) (wc c2) (ww c2) (wi c2) (wo c2) (wq c2) (wp c2) (wsg c2) (wx c2)).map Prod.fst) ((pTs off m.hd m.stk m.heap.length Vs.length m.stk JP2 rootP m.heap N 1 segRoots 1 C Mm Wt Pi Po Pp tbM tbC tbI tbO tbQ tpP tpS (SM 0) (SC 0) (S9 0) (SI 0) (SO 0) (SQ 0) (SP 0) (SS 0) (SX 0) (efOf c3) qv (wm c2) (wc c2) (ww c2) (wi c2) (wo c2) (wq c2) (wp c2) (wsg c2) (wx c2)).map Prod.fst) _ _ ncw (αd c4) (αd 0) _ _
        hd rfl (by simp only [pTs, bbTabL, airQTabG, List.map_cons, List.map_nil]) t α β (r % NR0)⟩
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


/-- **`p2pre h`'s verifier calls the jet once**: `compP_fs_open4`'s `hcalls`
    for the preimage statement (`runP_calls_one`, as in
    `compP_complete_log`). -/
theorem compP_calls_p2pre {h R : Nat} {ρ : Nat → Bool} {region : List Cell} (hrl : region.length = 1)
    (hr : ∀ i c, region[i]? = some c → cellOK (BT.nleaves shpP + 3 + i) c = true)
    {A : List Cell} {e : Nat → Nat} {row : Nat → Air.Row}
    (hA : AcceptsCP A (cMachineO ρ shpP region (VsP h)) [] [] JP2 rootP (cHeapO ρ shpP region (VsP h)).2
      (cHeapO ρ shpP region (VsP h)).1.length (VsP h).length e row) (hK : e 0 < 2 ^ R) :
    (runP ρ region (VsP h) A e row).calls (2 ^ R) = 1 :=
  runP_calls_one (G := P2Once.GP JP2) (U := P2Once.UP JP2) (P2Once.partP JP2)
    ⟨checkO h, P2Once.checkO_free h JP2, rfl⟩ (P2Once.verifierO_eq h) hrl hr hA hK

/-- **The hand-off's verifier calls the jet once**: `compP_fs_open4`'s
    `hcalls` for `p2commit c pat` (as in `compPC_complete_log`). -/
theorem compP_calls_p2commit {c : List Nat} {pat : List (Option Bool)} {R : Nat} {ρ : Nat → Bool}
    {region : List Cell} (hrl : region.length = 1)
    (hr : ∀ i c, region[i]? = some c → cellOK (BT.nleaves shpP + 3 + i) c = true)
    {A : List Cell} {e : Nat → Nat} {row : Nat → Air.Row}
    (hA : AcceptsCP A (cMachineO ρ shpP region [verifierC c pat]) [] [] JP2 rootP
      (cHeapO ρ shpP region [verifierC c pat]).2 (cHeapO ρ shpP region [verifierC c pat]).1.length 1 e row)
    (hK : e 0 < 2 ^ R) :
    (runP ρ region [verifierC c pat] A e row).calls (2 ^ R) = 1 :=
  runP_calls_one (G := P2Once.GC JP2) (U := P2Once.UC JP2) (P2Once.partC JP2)
    ⟨checkC c, patO pat, P2Commit.checkC_closed c JP2, P2Commit.patO_closed JP2 pat, rfl⟩
    (P2Once.verifierC_eq c pat) hrl hr hA hK

end Circuit
