import Ski.ZK.ROMInstMCP
import Ski.ZK.ROMMerkleIdxC

/-!
# The proof with the Poseidon2 jet at FRI's leaves, Plonky3's leaf hash

`comp_fs_open4ROMMC_fri` for the circuit with the Poseidon2 jet
(`compP_fs_open4ROMMC_fri`), over the eighteen groups' nine main ones.
One direction.
-/

set_option autoImplicit false
namespace Circuit

open ZKF B Air Compose CompM Stmt Mach Wit ComposedPText

/-- **The circuit with the Poseidon2 jet's openings fix the queried leaves'
    positions** (main groups `0, 2, …, 16`). -/
theorem compP_hposO_idx {tbM tbC tbI tbO tbQ tpP tpS : Nat} {SM SC S9 SI SO SQ SP SS SX : Nat → List F}
    {qv : EF → EF → List EF → F → List F → List F → List EF} {xs : Nat → Nat → F} {idx : Nat → List Nat}
    {h : List (List F) → Nat} {L NSl Mh : Nat}
    (h0 : ∀ c4, SM c4 = (idx c4).map (fun l => xs l 0)) (h2 : ∀ c4, SC c4 = (idx c4).map (fun l => xs l 2)) (h4 : ∀ c4, S9 c4 = (idx c4).map (fun l => xs l 4)) (h6 : ∀ c4, SI c4 = (idx c4).map (fun l => xs l 6)) (h8 : ∀ c4, SO c4 = (idx c4).map (fun l => xs l 8)) (h10 : ∀ c4, SQ c4 = (idx c4).map (fun l => xs l 10)) (h12 : ∀ c4, SP c4 = (idx c4).map (fun l => xs l 12)) (h14 : ∀ c4, SS c4 = (idx c4).map (fun l => xs l 14)) (h16 : ∀ c4, SX c4 = (idx c4).map (fun l => xs l 16)) :
    ∀ c4 d d', opF ((pGroups tbM tbC tbI tbO tbQ tpP tpS (SM c4) (SC c4) (S9 c4) (SI c4) (SO c4) (SQ c4) (SP c4) (SS c4) (SX c4) EF.zero qv).map (·.base.S)) [0, 2, 4, 6, 8, 10, 12, 14, 16] d =
        opF ((pGroups tbM tbC tbI tbO tbQ tpP tpS (SM c4) (SC c4) (S9 c4) (SI c4) (SO c4) (SQ c4) (SP c4) (SS c4) (SX c4) EF.zero qv).map (·.base.S)) [0, 2, 4, 6, 8, 10, 12, 14, 16] d' →
      ∀ l a, decide (l ∈ idx c4) = true →
        posRows xs [0, 2, 4, 6, 8, 10, 12, 14, 16] h L NSl Mh d l a = posRows xs [0, 2, 4, 6, 8, 10, 12, 14, 16] h L NSl Mh d' l a := by
  intro c4 d d' e l a hl
  refine posRows_hposO _ d d' e l a (isOfRows_of_mem (fun k hk => ?_) (of_decide_eq_true hl))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h0 c4
  · exact h2 c4
  · exact h4 c4
  · exact h6 c4
  · exact h8 c4
  · exact h10 c4
  · exact h12 c4
  · exact h14 c4
  · exact h16 c4

/-- **The circuit with the Poseidon2 jet's opened real leaves are FRI's
    queried indices** (main groups `0, 2, …, 16`). -/
theorem compP_opened_iff {tbM tbC tbI tbO tbQ tpP tpS : Nat} {SM SC S9 SI SO SQ SP SS SX : List F}
    {ζ : EF} {qv : EF → EF → List EF → F → List F → List F → List EF} {xs : Nat → Nat → F} {idx : List Nat}
    {L : Nat} (h0 : SM = idx.map (fun l => xs l 0)) (h2 : SC = idx.map (fun l => xs l 2)) (h4 : S9 = idx.map (fun l => xs l 4)) (h6 : SI = idx.map (fun l => xs l 6)) (h8 : SO = idx.map (fun l => xs l 8)) (h10 : SQ = idx.map (fun l => xs l 10)) (h12 : SP = idx.map (fun l => xs l 12)) (h14 : SS = idx.map (fun l => xs l 14)) (h16 : SX = idx.map (fun l => xs l 16))
    (hidx : ∀ l ∈ idx, l < L) {k0 : Nat} (hk0 : k0 ∈ [0, 2, 4, 6, 8, 10, 12, 14, 16])
    (hinj : ∀ l l', l < L → l' < L → xs l k0 = xs l' k0 → l = l') {l : Nat} (hl : l < L) :
    isOfRows ((pGroups tbM tbC tbI tbO tbQ tpP tpS SM SC S9 SI SO SQ SP SS SX ζ qv).map (·.base.S)) [0, 2, 4, 6, 8, 10, 12, 14, 16] xs l = true ↔ l ∈ idx := by
  refine isOfRows_iff (fun k hk => ?_) hidx hk0 hinj hl
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h0
  · exact h2
  · exact h4
  · exact h6
  · exact h8
  · exact h10
  · exact h12
  · exact h14
  · exact h16

/-- **The circuit with the Poseidon2 jet with FRI's query sets**: the sets
    built from FRI's indices at the LDE points meet the off-trace
    conditions, the openings fix the queried leaves' positions, and the
    opened real leaves are exactly the queried ones. -/
theorem compP_fri_leaves {tbM tbC tbI tbO tbQ tpP tpS : Nat}
    {qv : EF → EF → List EF → F → List F → List F → List EF}
    {bl sh : Nat → Nat} (hbl : ∀ k, bl k ≤ 26) {k0 : Nat} (hk0 : k0 ∈ [0, 2, 4, 6, 8, 10, 12, 14, 16]) (hs0 : sh k0 = 0)
    (hM : tbM ≤ 26) (hC : tbC ≤ 26) (hI : tbI ≤ 26) (hO : tbO ≤ 26) (hQ : tbQ ≤ 26) (hP : tpP ≤ 26) (hSg : tpS ≤ 26)
    {idx : Nat → List Nat} (hidx : ∀ c4, ∀ l ∈ idx c4, l < 2 ^ (bl k0 + 1))
    {h : List (List F) → Nat} {NSl Mh : Nat} :
    let SM := fun c4 => (idx c4).map (fun l => xsL bl sh l 0)
    let SC := fun c4 => (idx c4).map (fun l => xsL bl sh l 2)
    let S9 := fun c4 => (idx c4).map (fun l => xsL bl sh l 4)
    let SI := fun c4 => (idx c4).map (fun l => xsL bl sh l 6)
    let SO := fun c4 => (idx c4).map (fun l => xsL bl sh l 8)
    let SQ := fun c4 => (idx c4).map (fun l => xsL bl sh l 10)
    let SP := fun c4 => (idx c4).map (fun l => xsL bl sh l 12)
    let SS := fun c4 => (idx c4).map (fun l => xsL bl sh l 14)
    let SX := fun c4 => (idx c4).map (fun l => xsL bl sh l 16)
    (∀ c4, ∀ x ∈ SM c4, x ∉ cosetL 1 (bbGen (tbM + 1)) (2 ^ (tbM + 1))) ∧
    (∀ c4, ∀ x ∈ SC c4, x ∉ cosetL 1 (bbGen (tbC + 1)) (2 ^ (tbC + 1))) ∧
    (∀ c4, ∀ x ∈ S9 c4, x ∉ cosetL 1 (bbGen (8 + 1)) (2 ^ (8 + 1))) ∧
    (∀ c4, ∀ x ∈ SI c4, x ∉ cosetL 1 (bbGen (tbI + 1)) (2 ^ (tbI + 1))) ∧
    (∀ c4, ∀ x ∈ SO c4, x ∉ cosetL 1 (bbGen (tbO + 1)) (2 ^ (tbO + 1))) ∧
    (∀ c4, ∀ x ∈ SQ c4, x ∉ cosetL 1 (bbGen (tbQ + 1)) (2 ^ (tbQ + 1))) ∧
    (∀ c4, ∀ x ∈ SP c4, x ∉ cosetL 1 (bbGen (tpP + 1)) (2 ^ (tpP + 1))) ∧
    (∀ c4, ∀ x ∈ SS c4, x ∉ cosetL 1 (bbGen (tpS + 1)) (2 ^ (tpS + 1))) ∧
    (∀ c4, ∀ x ∈ SX c4, x ∉ cosetL 1 (bbGen (8 + 1)) (2 ^ (8 + 1))) ∧
    (∀ c4 d d', opF ((pGroups tbM tbC tbI tbO tbQ tpP tpS (SM c4) (SC c4) (S9 c4) (SI c4) (SO c4) (SQ c4) (SP c4) (SS c4) (SX c4) EF.zero qv).map (·.base.S)) [0, 2, 4, 6, 8, 10, 12, 14, 16] d =
        opF ((pGroups tbM tbC tbI tbO tbQ tpP tpS (SM c4) (SC c4) (S9 c4) (SI c4) (SO c4) (SQ c4) (SP c4) (SS c4) (SX c4) EF.zero qv).map (·.base.S)) [0, 2, 4, 6, 8, 10, 12, 14, 16] d' →
      ∀ l a, decide (l ∈ idx c4) = true →
        posRows (xsL bl sh) [0, 2, 4, 6, 8, 10, 12, 14, 16] h (2 ^ (bl k0 + 1)) NSl Mh d l a =
          posRows (xsL bl sh) [0, 2, 4, 6, 8, 10, 12, 14, 16] h (2 ^ (bl k0 + 1)) NSl Mh d' l a) ∧
    (∀ c4 l, l < 2 ^ (bl k0 + 1) →
      (isOfRows ((pGroups tbM tbC tbI tbO tbQ tpP tpS (SM c4) (SC c4) (S9 c4) (SI c4) (SO c4) (SQ c4) (SP c4) (SS c4) (SX c4) EF.zero qv).map (·.base.S))
        [0, 2, 4, 6, 8, 10, 12, 14, 16] (xsL bl sh) l = true ↔ l ∈ idx c4)) := by
  intro SM SC S9 SI SO SQ SP SS SX
  refine ⟨fun c4 => xsL_off hbl hM _ 0, fun c4 => xsL_off hbl hC _ 2, fun c4 => xsL_off hbl (tb := 8) (by decide) _ 4, fun c4 => xsL_off hbl hI _ 6, fun c4 => xsL_off hbl hO _ 8, fun c4 => xsL_off hbl hQ _ 10, fun c4 => xsL_off hbl hP _ 12, fun c4 => xsL_off hbl hSg _ 14, fun c4 => xsL_off hbl (tb := 8) (by decide) _ 16,
    compP_hposO_idx (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl), ?_⟩
  intro c4 l hl
  exact compP_opened_iff rfl rfl rfl rfl rfl rfl rfl rfl rfl (hidx c4) hk0 (xsL_inj hs0 (hbl k0)) hl

set_option maxRecDepth 100000 in
/-- **`comp_fs_open4ROMMC_fri` with the Poseidon2 jet**: the query sets
    FRI's at its leaves' LDE points, the leaf hash its row and salt alone,
    so leaves may share a hash (`compP_fs_open4ROMMC`); one direction. -/
theorem compP_fs_open4ROMMC_fri {V Wv Pq P2 P3 : Type} (off : EF → String → EF) {R Lm LI LO LP : Nat} (hR : R ≤ 20)
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
    {bl sh : Nat → Nat} {idx : Nat → List Nat}
    (qv : EF → EF → List EF → F → List F → List F → List EF)
    (wm wc ww wi wo wq wp wsg wx : Nat → List (EF → EF → List F))
    {Lwm Lwc Lww Lwi Lwo Lwq Lwp Lwsg Lwx : Nat}
    (hlwm : ∀ c, (wm c).length = Lwm) (hlwc : ∀ c, (wc c).length = Lwc) (hlww : ∀ c, (ww c).length = Lww) (hlwi : ∀ c, (wi c).length = Lwi) (hlwo : ∀ c, (wo c).length = Lwo) (hlwq : ∀ c, (wq c).length = Lwq) (hlwp : ∀ c, (wp c).length = Lwp) (hlwsg : ∀ c, (wsg c).length = Lwsg) (hlwx : ∀ c, (wx c).length = Lwx)
    {K2 K4 : Nat} (hK2 : 0 < K2) (hK4 : 0 < K4)
    (φ : Nat → Option (List (List (List EF)) × List (List (List (List EF))) × List (List (List EF))) → Nat) {N4 : Nat}
    (hφ : ∀ m w, φ m w < N4)
    (hszM : ∀ c4, 2 * ((friS bl sh idx 0) c4).length + 8 ≤ 2 ^ (tbM + 1)) (hszC : ∀ c4, 2 * ((friS bl sh idx 2) c4).length + 8 ≤ 2 ^ (tbC + 1)) (hsz9 : ∀ c4, 2 * ((friS bl sh idx 4) c4).length + 8 ≤ 2 ^ (8 + 1)) (hszI : ∀ c4, 2 * ((friS bl sh idx 6) c4).length + 8 ≤ 2 ^ (tbI + 1)) (hszO : ∀ c4, 2 * ((friS bl sh idx 8) c4).length + 8 ≤ 2 ^ (tbO + 1)) (hszQ : ∀ c4, 2 * ((friS bl sh idx 10) c4).length + 8 ≤ 2 ^ (tbQ + 1)) (hszP : ∀ c4, 2 * ((friS bl sh idx 12) c4).length + 8 ≤ 2 ^ (tpP + 1)) (hszS : ∀ c4, 2 * ((friS bl sh idx 14) c4).length + 8 ≤ 2 ^ (tpS + 1)) (hszX : ∀ c4, 2 * ((friS bl sh idx 16) c4).length + 8 ≤ 2 ^ (8 + 1))
    {ncw : Nat} (αd : Nat → EF) {B4 : Nat}
    (hB4 : sumTo K4 (fun c4 => indB (!genB (αd c4))) ≤ B4) (fri : Nat → EF → EF → List (EF → EF) → V) (hncw : 4 ≤ ncw)
    (NR2 : Nat) (Rb : Nat → EF → EF → Nat → List (EF → EF)) (Ro : Nat → EF → EF → Nat → Wv)
    {NSl L KA sQ kQ nQ KQ NS2 NS3 n2 n3 : Nat} (hKA : 0 < KA) (hN : 0 < NSl) (hKL : KQ = KA ^ L)
    (hbl : ∀ k, bl k ≤ 26) {k0 : Nat} (hk0 : k0 ∈ [0, 2, 4, 6, 8, 10, 12, 14, 16])
    (hs0 : sh k0 = 0) (hidx : ∀ c4, ∀ l ∈ idx c4, l < L) (hL : L = 2 ^ (bl k0 + 1))
    {h : List (List F) → Nat} {Mh : Nat} (hMh : 0 < Mh) (hnQ : L * (NSl * Mh) ≤ nQ) (hsQ : 1 ≤ sQ) (g : List (List (List F)) → List Nat → Pq)
    (nxt : Pq → Nat → List Nat → Nat) (d1 : List (List (List F)))
    (Com2 : List (List (List F)) → Nat → Nat) (Pf2 : Nat → List (List (List F)) → Nat → P2) (hc2 : ComHides NS2 Com2)
    (hp2 : ∀ c4, ComPfHides NS2 Com2 (Pf2 c4) (opF ((pGroups tbM tbC tbI tbO tbQ tpP tpS ((friS bl sh idx 0) c4) ((friS bl sh idx 2) c4) ((friS bl sh idx 4) c4) ((friS bl sh idx 6) c4) ((friS bl sh idx 8) c4) ((friS bl sh idx 10) c4) ((friS bl sh idx 12) c4) ((friS bl sh idx 14) c4) ((friS bl sh idx 16) c4) EF.zero qv).map (·.base.S)) [1, 3, 5, 7, 9, 11, 13, 15, 17]))
    (hr2 : ∀ d σ, Com2 d σ < n2) (d2 : List (List (List F)))
    (Com3 : List (List (List (List F))) × List (List (List F)) → Nat → Nat)
    (Pf3 : Nat → List (List (List (List F))) × List (List (List F)) → Nat → P3) (hc3 : ComHides NS3 Com3)
    (hp3 : ∀ c4, ComPfHides NS3 Com3 (Pf3 c4) (fun d => (opQ (pSsT ((friS bl sh idx 0) c4) ((friS bl sh idx 2) c4) ((friS bl sh idx 4) c4) ((friS bl sh idx 6) c4) ((friS bl sh idx 8) c4) ((friS bl sh idx 10) c4) ((friS bl sh idx 12) c4) ((friS bl sh idx 14) c4) ((friS bl sh idx 16) c4)) d.1, opCw (pSsC tbM tbC tbI tbO tbQ tpP tpS ((friS bl sh idx 0) c4) ((friS bl sh idx 2) c4) ((friS bl sh idx 4) c4) ((friS bl sh idx 6) c4) ((friS bl sh idx 8) c4) ((friS bl sh idx 10) c4) ((friS bl sh idx 12) c4) ((friS bl sh idx 14) c4) ((friS bl sh idx 16) c4)) d.2)))
    (hr3 : ∀ d σ, Com3 d σ < n3) (d3 : List (List (List (List F))) × List (List (List F)))
    (E : Nat → Nat → Nat → Nat → Nat → Nat → Nat → Option (Pq × List Nat) × Option (P2 × P3) × TViewN (PcsPV (V × Wv)) ((EF × EF) × EF) → Bool) :
    let opS := fun (c4 : Nat) => opF ((pGroups tbM tbC tbI tbO tbQ tpP tpS ((friS bl sh idx 0) c4) ((friS bl sh idx 2) c4) ((friS bl sh idx 4) c4) ((friS bl sh idx 6) c4) ((friS bl sh idx 8) c4) ((friS bl sh idx 10) c4) ((friS bl sh idx 12) c4) ((friS bl sh idx 14) c4) ((friS bl sh idx 16) c4) EF.zero qv).map (·.base.S)) [0, 2, 4, 6, 8, 10, 12, 14, 16]
    let Com1 := comM KA NSl L (posRowsP (xsL bl sh) [0, 2, 4, 6, 8, 10, 12, 14, 16] h NSl Mh)
    let Pf1 := fun (c4 : Nat) => pfM KA NSl L kQ (posRowsP (xsL bl sh) [0, 2, 4, 6, 8, 10, 12, 14, 16] h NSl Mh) ((fun c4 l => decide (l ∈ idx c4)) c4) (opS c4) g nxt
    let Cmi := comMI KA NSl L L (posRowsP (xsL bl sh) [0, 2, 4, 6, 8, 10, 12, 14, 16] h NSl Mh)
    let Pfi := fun (c4 : Nat) => pfMI KA NSl L L kQ (posRowsP (xsL bl sh) [0, 2, 4, 6, 8, 10, 12, 14, 16] h NSl Mh) ((fun c4 l => decide (l ∈ idx c4)) c4) (opS c4) g nxt
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
    let NR0 := pNR off m.hd m.stk m.heap.length Vs.length m.stk JP2 rootP m.heap N 1 segRoots 1 C Mm Wt Pi Po Pp tbM tbC tbI tbO tbQ tpP tpS ((friS bl sh idx 0) 0) ((friS bl sh idx 2) 0) ((friS bl sh idx 4) 0) ((friS bl sh idx 6) 0) ((friS bl sh idx 8) 0) ((friS bl sh idx 10) 0) ((friS bl sh idx 12) 0) ((friS bl sh idx 14) 0) ((friS bl sh idx 16) 0) EF.zero qv (wm 0) (wc 0) (ww 0) (wi 0) (wo 0) (wq 0) (wp 0) (wsg 0) (wx 0) ncw
    let pcsZ := fun (c4 c2 : Nat) (ζ : EF) t α β r => pPcs off m.hd m.stk m.heap.length Vs.length m.stk JP2 rootP m.heap N 1 segRoots 1 C Mm Wt Pi Po Pp tbM tbC tbI tbO tbQ tpP tpS ((friS bl sh idx 0) c4) ((friS bl sh idx 2) c4) ((friS bl sh idx 4) c4) ((friS bl sh idx 6) c4) ((friS bl sh idx 8) c4) ((friS bl sh idx 10) c4) ((friS bl sh idx 12) c4) ((friS bl sh idx 14) c4) ((friS bl sh idx 16) c4) ζ qv (wm c2) (wc c2) (ww c2) (wi c2) (wo c2) (wq c2) (wp c2) (wsg c2) (wx c2) ncw (αd c4)
      (friX (fri c4) (Rb c4) (Ro c4) (r / NR0)) t α β (r % NR0)
    let psimZ := fun (c4 c2 : Nat) (ζ : EF) α β v r => pPsim off m.hd m.stk m.heap.length Vs.length m.stk JP2 rootP m.heap N 1 segRoots 1 C Mm Wt Pi Po Pp tbM tbC tbI tbO tbQ tpP tpS ((friS bl sh idx 0) c4) ((friS bl sh idx 2) c4) ((friS bl sh idx 4) c4) ((friS bl sh idx 6) c4) ((friS bl sh idx 8) c4) ((friS bl sh idx 10) c4) ((friS bl sh idx 12) c4) ((friS bl sh idx 14) c4) ((friS bl sh idx 16) c4) ζ qv (wm c2) (wc c2) (ww c2) (wi c2) (wo c2) (wq c2) (wp c2) (wsg c2) (wx c2) ncw (αd c4)
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
    let q0 := pGroups tbM tbC tbI tbO tbQ tpP tpS ((friS bl sh idx 0) 0) ((friS bl sh idx 2) 0) ((friS bl sh idx 4) 0) ((friS bl sh idx 6) 0) ((friS bl sh idx 8) 0) ((friS bl sh idx 10) 0) ((friS bl sh idx 12) 0) ((friS bl sh idx 14) 0) ((friS bl sh idx 16) 0) EF.zero qv
    let qZ := fun (c4 : Nat) (ζ : EF) => pGroups tbM tbC tbI tbO tbQ tpP tpS ((friS bl sh idx 0) c4) ((friS bl sh idx 2) c4) ((friS bl sh idx 4) c4) ((friS bl sh idx 6) c4) ((friS bl sh idx 8) c4) ((friS bl sh idx 10) c4) ((friS bl sh idx 12) c4) ((friS bl sh idx 14) c4) ((friS bl sh idx 16) c4) ζ qv
    let Ss := fun c4 => (qZ c4 EF.zero).map (·.base.S)
    let ks := pKs m.hd m.stk m.heap.length Vs.length m.stk JP2 rootP m.heap N 1 segRoots
    let cols := pCols off m.hd m.stk m.heap.length Vs.length m.stk JP2 rootP N 1 m.heap segRoots 1 C Mm Wt Pi Po Pp
    let tqZ := fun (c4 c2 : Nat) (ζ : EF) => (pTs off m.hd m.stk m.heap.length Vs.length m.stk JP2 rootP m.heap N 1 segRoots 1 C Mm Wt Pi Po Pp tbM tbC tbI tbO tbQ tpP tpS ((friS bl sh idx 0) c4) ((friS bl sh idx 2) c4) ((friS bl sh idx 4) c4) ((friS bl sh idx 6) c4) ((friS bl sh idx 8) c4) ((friS bl sh idx 10) c4) ((friS bl sh idx 12) c4) ((friS bl sh idx 14) c4) ((friS bl sh idx 16) c4) ζ qv (wm c2) (wc c2) (ww c2) (wi c2) (wo c2) (wq c2) (wp c2) (wsg c2) (wx c2)).map Prod.fst
    let qdZ := fun (c4 c2 : Nat) (ζ : EF) (t : Nat → Tup) (α β : EF) (ms : List F) =>
      (pTs off m.hd m.stk m.heap.length Vs.length m.stk JP2 rootP m.heap N 1 segRoots 1 C Mm Wt Pi Po Pp tbM tbC tbI tbO tbQ tpP tpS ((friS bl sh idx 0) c4) ((friS bl sh idx 2) c4) ((friS bl sh idx 4) c4) ((friS bl sh idx 6) c4) ((friS bl sh idx 8) c4) ((friS bl sh idx 10) c4) ((friS bl sh idx 12) c4) ((friS bl sh idx 14) c4) ((friS bl sh idx 16) c4) ζ qv (wm c2) (wc c2) (ww c2) (wi c2) (wo c2) (wq c2) (wp c2) (wsg c2) (wx c2)).map (fun p => p.2 t α β ms)
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
      sumTo (NSl ^ L * KA ^ nQ * KQ) (fun σ1 => sumTo (NS2 * NS3) (fun σ => sumTo NR (fun r => sumN 5 (fun t => g (σ1, σ, r, t)))))
    let smR := fun (g : Nat × Nat × Nat × (Nat → Tup) → Nat) =>
      sumTo (NSl ^ L * KA ^ nQ) (fun σ1 => sumTo (NS2 * NS3) (fun σ => sumTo NR (fun r => sumN 5 (fun t => g (σ1, σ, r, t)))))
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
          (K2 * (Q4 * ((NSl ^ L * KA ^ nQ * KQ) * (NS2 * NS3 * (Q4 * (NR * (Q4 ^ 5 * M)) + Q4 * (Q4 * (Q4 ^ 5 * 0)))) +
            Q4 * Q4 * (NS2 * NS3 * (NR * (Q4 ^ 5 * (2 * (L * (L * (NSl ^ (L - 1) * sQ))) * (KA ^ nQ * KQ))))))) +
            (Q4 * (P * P) * (K2 * Q4) + Q4 * Q4 * (K2 * (P * P))) * ((NSl ^ L * KA ^ nQ * KQ) * (NS2 * NS3 * (NR * (Q4 ^ 5 * 1)))))))) +
            B4 * (Q4 * Q4 * (K2 * Q4) * sm4 (fun _ => 1))) +
      K4 * (Q4 * Q4 * (K2 * Q4) * (K4 ^ N4 * ((Q4 * Q4) ^ KQ * (K2 ^ (KQ * n2) * (Q4 ^ (KQ * (n2 * n3)) *
        (KQ * (L * (KA ^ nQ * (NSl ^ (L - 1) * (sQ * (kQ + L))))) * (NS2 * NS3 * (NR * (Q4 ^ 5 * 1))))))))) := by
  have hM26 : tbM ≤ 26 := by omega
  have hC26 : tbC ≤ 26 := by omega
  have hI26 : tbI ≤ 26 := by omega
  have hO26 : tbO ≤ 26 := by omega
  have hQ26 : tbQ ≤ 26 := by omega
  obtain ⟨_, _, ⟨_, _, _, _, _, _, p1, _, s1, _⟩⟩ := compP_run_facts hR hLm hLI hLO hLP hrl hr hA hlen hK hHI hHO hHP hcalls
  have hP26 : tpP ≤ 26 := by rw [htP]; omega
  have hS26 : tpS ≤ 26 := by rw [htS]; omega
  subst hL
  have fl := compP_fri_leaves (qv := qv) (h := h) (NSl := NSl) (Mh := Mh) hbl hk0 hs0 hM26 hC26 hI26 hO26 hQ26 hP26 hS26 hidx
  exact compP_fs_open4ROMMC (kQ := kQ) (nQ := nQ) (sQ := sQ) off hR hLm hLI hLO hLP hrl hr hA hlen hK hHI hHO hHP
    hcalls htM htC htI htO htQ htP htS (friS bl sh idx 0) (friS bl sh idx 2) (friS bl sh idx 4) (friS bl sh idx 6) (friS bl sh idx 8) (friS bl sh idx 10) (friS bl sh idx 12) (friS bl sh idx 14) (friS bl sh idx 16) qv
    wm wc ww wi wo wq wp wsg wx hlwm hlwc hlww hlwi hlwo hlwq hlwp hlwsg hlwx hK2 hK4 φ hφ
    fl.1 fl.2.1 fl.2.2.1 fl.2.2.2.1 fl.2.2.2.2.1 fl.2.2.2.2.2.1 fl.2.2.2.2.2.2.1 fl.2.2.2.2.2.2.2.1 fl.2.2.2.2.2.2.2.2.1
    hszM hszC hsz9 hszI hszO hszQ hszP hszS hszX αd hB4 fri hncw NR2 Rb Ro
    hKA hN hKL (posRowsP (xsL bl sh) [0, 2, 4, 6, 8, 10, 12, 14, 16] h NSl Mh)
    (fun d l a hl => Nat.lt_of_lt_of_le (posRowsP_lt (L := 2 ^ (bl k0 + 1)) hN hMh d l a hl)
      (Nat.le_trans (Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _)) hnQ)) g
    (fun d l v => Nat.le_trans (posRowsP_spread d l v) hsQ) nxt (fun c4 l => decide (l ∈ idx c4))
    (fun c4 d d' e l a hl => by
      rw [posRowsP_of_posRows (Nat.two_pow_pos (bl k0 + 1)), posRowsP_of_posRows (Nat.two_pow_pos (bl k0 + 1)),
        fl.2.2.2.2.2.2.2.2.2.1 c4 d d' e l a hl]) d1 Com2 Pf2 hc2 hp2 hr2 d2 Com3 Pf3
    hc3 hp3 hr3 d3 E

end Circuit
