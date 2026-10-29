import Ski.ZK.ROMInstMCJ
import Ski.ZK.ROMMerkleIdxC

/-!
# The proof with jets at FRI's leaves, Plonky3's leaf hash

`comp_fs_open4ROMMC_fri` for the circuit with jets
(`compJ_fs_open4ROMMC_fri`): the query sets FRI's (`friS`) at its leaves'
LDE points, the leaf hash its row and salt alone (`posRowsP`).  The opened
real leaves are FRI's queried indices (`compJ_opened_iff`), and the
openings fix the leaves' positions (`compJ_hposO_idx`), as for the composed
circuit, over the twenty groups' ten main ones.  One direction.
-/

set_option autoImplicit false
namespace Circuit

open ZKF B Air JetTable Compose CompM Stmt Mach Wit

/-- **The circuit with jets' openings fix the queried leaves' positions**
    (main groups `0, 2, …, 18`). -/
theorem compJ_hposO_idx {tbM tbC tbPo tbI tpT tpH tpR tpP tpS : Nat}
    {SM SC S9 SPo SI ST SH SR SP SS : Nat → List F}
    {qv : EF → EF → List EF → F → List F → List F → List EF} {xs : Nat → Nat → F} {idx : Nat → List Nat}
    {h : List (List F) → Nat} {L NSl Mh : Nat}
    (h0 : ∀ c4, SM c4 = (idx c4).map (fun l => xs l 0)) (h2 : ∀ c4, SC c4 = (idx c4).map (fun l => xs l 2)) (h4 : ∀ c4, S9 c4 = (idx c4).map (fun l => xs l 4)) (h6 : ∀ c4, SPo c4 = (idx c4).map (fun l => xs l 6)) (h8 : ∀ c4, SI c4 = (idx c4).map (fun l => xs l 8)) (h10 : ∀ c4, ST c4 = (idx c4).map (fun l => xs l 10)) (h12 : ∀ c4, SH c4 = (idx c4).map (fun l => xs l 12)) (h14 : ∀ c4, SR c4 = (idx c4).map (fun l => xs l 14)) (h16 : ∀ c4, SP c4 = (idx c4).map (fun l => xs l 16)) (h18 : ∀ c4, SS c4 = (idx c4).map (fun l => xs l 18)) :
    ∀ c4 d d', opF ((jGroups tbM tbC tbPo tbI tpT tpH tpR tpP tpS (SM c4) (SC c4) (S9 c4) (SPo c4) (SI c4) (ST c4) (SH c4) (SR c4) (SP c4) (SS c4) EF.zero qv).map (·.base.S)) [0, 2, 4, 6, 8, 10, 12, 14, 16, 18] d =
        opF ((jGroups tbM tbC tbPo tbI tpT tpH tpR tpP tpS (SM c4) (SC c4) (S9 c4) (SPo c4) (SI c4) (ST c4) (SH c4) (SR c4) (SP c4) (SS c4) EF.zero qv).map (·.base.S)) [0, 2, 4, 6, 8, 10, 12, 14, 16, 18] d' →
      ∀ l a, decide (l ∈ idx c4) = true →
        posRows xs [0, 2, 4, 6, 8, 10, 12, 14, 16, 18] h L NSl Mh d l a = posRows xs [0, 2, 4, 6, 8, 10, 12, 14, 16, 18] h L NSl Mh d' l a := by
  intro c4 d d' e l a hl
  refine posRows_hposO _ d d' e l a (isOfRows_of_mem (fun k hk => ?_) (of_decide_eq_true hl))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h0 c4
  · exact h2 c4
  · exact h4 c4
  · exact h6 c4
  · exact h8 c4
  · exact h10 c4
  · exact h12 c4
  · exact h14 c4
  · exact h16 c4
  · exact h18 c4

/-- **The circuit with jets' opened real leaves are FRI's queried
    indices** (main groups `0, 2, …, 18`). -/
theorem compJ_opened_iff {tbM tbC tbPo tbI tpT tpH tpR tpP tpS : Nat} {SM SC S9 SPo SI ST SH SR SP SS : List F}
    {ζ : EF} {qv : EF → EF → List EF → F → List F → List F → List EF} {xs : Nat → Nat → F} {idx : List Nat}
    {L : Nat} (h0 : SM = idx.map (fun l => xs l 0)) (h2 : SC = idx.map (fun l => xs l 2)) (h4 : S9 = idx.map (fun l => xs l 4)) (h6 : SPo = idx.map (fun l => xs l 6)) (h8 : SI = idx.map (fun l => xs l 8)) (h10 : ST = idx.map (fun l => xs l 10)) (h12 : SH = idx.map (fun l => xs l 12)) (h14 : SR = idx.map (fun l => xs l 14)) (h16 : SP = idx.map (fun l => xs l 16)) (h18 : SS = idx.map (fun l => xs l 18))
    (hidx : ∀ l ∈ idx, l < L) {k0 : Nat} (hk0 : k0 ∈ [0, 2, 4, 6, 8, 10, 12, 14, 16, 18])
    (hinj : ∀ l l', l < L → l' < L → xs l k0 = xs l' k0 → l = l') {l : Nat} (hl : l < L) :
    isOfRows ((jGroups tbM tbC tbPo tbI tpT tpH tpR tpP tpS SM SC S9 SPo SI ST SH SR SP SS ζ qv).map (·.base.S)) [0, 2, 4, 6, 8, 10, 12, 14, 16, 18] xs l = true ↔ l ∈ idx := by
  refine isOfRows_iff (fun k hk => ?_) hidx hk0 hinj hl
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h0
  · exact h2
  · exact h4
  · exact h6
  · exact h8
  · exact h10
  · exact h12
  · exact h14
  · exact h16
  · exact h18

/-- **The circuit with jets with FRI's query sets**: the sets built from
    FRI's indices at the LDE points `xsL` meet the off-trace conditions, the
    openings fix the queried leaves' positions, and the opened real leaves
    are exactly the queried ones; the tallest opened group `k0` is any of
    the ten main ones. -/
theorem compJ_fri_leaves {tbM tbC tbPo tbI tpT tpH tpR tpP tpS : Nat}
    {qv : EF → EF → List EF → F → List F → List F → List EF}
    {bl sh : Nat → Nat} (hbl : ∀ k, bl k ≤ 26) {k0 : Nat} (hk0 : k0 ∈ [0, 2, 4, 6, 8, 10, 12, 14, 16, 18]) (hs0 : sh k0 = 0)
    (hM : tbM ≤ 26) (hC : tbC ≤ 26) (hPo : tbPo ≤ 26) (hI : tbI ≤ 26) (hT : tpT ≤ 26) (hH : tpH ≤ 26)
    (hR : tpR ≤ 26) (hP : tpP ≤ 26) (hSg : tpS ≤ 26)
    {idx : Nat → List Nat} (hidx : ∀ c4, ∀ l ∈ idx c4, l < 2 ^ (bl k0 + 1))
    {h : List (List F) → Nat} {NSl Mh : Nat} :
    let SM := fun c4 => (idx c4).map (fun l => xsL bl sh l 0)
    let SC := fun c4 => (idx c4).map (fun l => xsL bl sh l 2)
    let S9 := fun c4 => (idx c4).map (fun l => xsL bl sh l 4)
    let SPo := fun c4 => (idx c4).map (fun l => xsL bl sh l 6)
    let SI := fun c4 => (idx c4).map (fun l => xsL bl sh l 8)
    let ST := fun c4 => (idx c4).map (fun l => xsL bl sh l 10)
    let SH := fun c4 => (idx c4).map (fun l => xsL bl sh l 12)
    let SR := fun c4 => (idx c4).map (fun l => xsL bl sh l 14)
    let SP := fun c4 => (idx c4).map (fun l => xsL bl sh l 16)
    let SS := fun c4 => (idx c4).map (fun l => xsL bl sh l 18)
    (∀ c4, ∀ x ∈ SM c4, x ∉ cosetL 1 (bbGen (tbM + 1)) (2 ^ (tbM + 1))) ∧
    (∀ c4, ∀ x ∈ SC c4, x ∉ cosetL 1 (bbGen (tbC + 1)) (2 ^ (tbC + 1))) ∧
    (∀ c4, ∀ x ∈ S9 c4, x ∉ cosetL 1 (bbGen 9) (2 ^ 9)) ∧
    (∀ c4, ∀ x ∈ SPo c4, x ∉ cosetL 1 (bbGen (tbPo + 1)) (2 ^ (tbPo + 1))) ∧
    (∀ c4, ∀ x ∈ SI c4, x ∉ cosetL 1 (bbGen (tbI + 1)) (2 ^ (tbI + 1))) ∧
    (∀ c4, ∀ x ∈ ST c4, x ∉ cosetL 1 (bbGen (tpT + 1)) (2 ^ (tpT + 1))) ∧
    (∀ c4, ∀ x ∈ SH c4, x ∉ cosetL 1 (bbGen (tpH + 1)) (2 ^ (tpH + 1))) ∧
    (∀ c4, ∀ x ∈ SR c4, x ∉ cosetL 1 (bbGen (tpR + 1)) (2 ^ (tpR + 1))) ∧
    (∀ c4, ∀ x ∈ SP c4, x ∉ cosetL 1 (bbGen (tpP + 1)) (2 ^ (tpP + 1))) ∧
    (∀ c4, ∀ x ∈ SS c4, x ∉ cosetL 1 (bbGen (tpS + 1)) (2 ^ (tpS + 1))) ∧
    (∀ c4 d d', opF ((jGroups tbM tbC tbPo tbI tpT tpH tpR tpP tpS (SM c4) (SC c4) (S9 c4) (SPo c4) (SI c4) (ST c4) (SH c4) (SR c4) (SP c4) (SS c4) EF.zero qv).map (·.base.S)) [0, 2, 4, 6, 8, 10, 12, 14, 16, 18] d =
        opF ((jGroups tbM tbC tbPo tbI tpT tpH tpR tpP tpS (SM c4) (SC c4) (S9 c4) (SPo c4) (SI c4) (ST c4) (SH c4) (SR c4) (SP c4) (SS c4) EF.zero qv).map (·.base.S)) [0, 2, 4, 6, 8, 10, 12, 14, 16, 18] d' →
      ∀ l a, decide (l ∈ idx c4) = true →
        posRows (xsL bl sh) [0, 2, 4, 6, 8, 10, 12, 14, 16, 18] h (2 ^ (bl k0 + 1)) NSl Mh d l a =
          posRows (xsL bl sh) [0, 2, 4, 6, 8, 10, 12, 14, 16, 18] h (2 ^ (bl k0 + 1)) NSl Mh d' l a) ∧
    (∀ c4 l, l < 2 ^ (bl k0 + 1) →
      (isOfRows ((jGroups tbM tbC tbPo tbI tpT tpH tpR tpP tpS (SM c4) (SC c4) (S9 c4) (SPo c4) (SI c4) (ST c4) (SH c4) (SR c4) (SP c4) (SS c4) EF.zero qv).map (·.base.S))
        [0, 2, 4, 6, 8, 10, 12, 14, 16, 18] (xsL bl sh) l = true ↔ l ∈ idx c4)) := by
  intro SM SC S9 SPo SI ST SH SR SP SS
  refine ⟨fun c4 => xsL_off hbl hM _ 0, fun c4 => xsL_off hbl hC _ 2, fun c4 => xsL_off hbl (tb := 8) (by decide) _ 4, fun c4 => xsL_off hbl hPo _ 6, fun c4 => xsL_off hbl hI _ 8, fun c4 => xsL_off hbl hT _ 10, fun c4 => xsL_off hbl hH _ 12, fun c4 => xsL_off hbl hR _ 14, fun c4 => xsL_off hbl hP _ 16, fun c4 => xsL_off hbl hSg _ 18,
    compJ_hposO_idx (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl), ?_⟩
  intro c4 l hl
  exact compJ_opened_iff rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl (hidx c4) hk0 (xsL_inj hs0 (hbl k0)) hl

set_option maxRecDepth 100000 in
/-- **`comp_fs_open4ROMMC_fri` with jets**: the query sets FRI's at its
    leaves' LDE points, the leaf hash its row and salt alone, so leaves may
    share a hash (`compJ_fs_open4ROMMC`).  Its Merkle hiding term is
    `L sQ (kQ + L) / NSl + 2 L² sQ / NSl` a draw; one direction. -/
theorem compJ_fs_open4ROMMC_fri {V Wv Pq P2 P3 : Type} (off : EF → String → EF) {R Lm Lp Li : Nat} (hR : R ≤ 20)
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
    {bl sh : Nat → Nat} {idx : Nat → List Nat}
    (qv : EF → EF → List EF → F → List F → List F → List EF)
    (wm wc ww wpo wi wt wh wr wp wsg : Nat → List (EF → EF → List F))
    {Lwm Lwc Lww Lwpo Lwi Lwt Lwh Lwr Lwp Lwsg : Nat} (hlwm : ∀ c, (wm c).length = Lwm)
    (hlwc : ∀ c, (wc c).length = Lwc) (hlww : ∀ c, (ww c).length = Lww) (hlwpo : ∀ c, (wpo c).length = Lwpo)
    (hlwi : ∀ c, (wi c).length = Lwi) (hlwt : ∀ c, (wt c).length = Lwt) (hlwh : ∀ c, (wh c).length = Lwh)
    (hlwr : ∀ c, (wr c).length = Lwr) (hlwp : ∀ c, (wp c).length = Lwp) (hlwsg : ∀ c, (wsg c).length = Lwsg)
    {K2 K4 : Nat} (hK2 : 0 < K2) (hK4 : 0 < K4)
    (φ : Nat → Option (List (List (List EF)) × List (List (List (List EF))) × List (List (List EF))) → Nat) {N4 : Nat}
    (hφ : ∀ m w, φ m w < N4)
    (hszM : ∀ c4, 2 * ((friS bl sh idx 0) c4).length + 8 ≤ 2 ^ (tbM + 1))
    (hszC : ∀ c4, 2 * ((friS bl sh idx 2) c4).length + 8 ≤ 2 ^ (tbC + 1))
    (hsz9 : ∀ c4, 2 * ((friS bl sh idx 4) c4).length + 8 ≤ 2 ^ 9)
    (hszPo : ∀ c4, 2 * ((friS bl sh idx 6) c4).length + 8 ≤ 2 ^ (tbPo + 1))
    (hszI : ∀ c4, 2 * ((friS bl sh idx 8) c4).length + 8 ≤ 2 ^ (tbI + 1))
    (hszT : ∀ c4, 2 * ((friS bl sh idx 10) c4).length + 8 ≤ 2 ^ (tpT + 1))
    (hszH : ∀ c4, 2 * ((friS bl sh idx 12) c4).length + 8 ≤ 2 ^ (tpH + 1))
    (hszR : ∀ c4, 2 * ((friS bl sh idx 14) c4).length + 8 ≤ 2 ^ (tpR + 1))
    (hszP : ∀ c4, 2 * ((friS bl sh idx 16) c4).length + 8 ≤ 2 ^ (tpP + 1))
    (hszS : ∀ c4, 2 * ((friS bl sh idx 18) c4).length + 8 ≤ 2 ^ (tpS + 1))
    {ncw : Nat} (αd : Nat → EF) {B4 : Nat}
    (hB4 : sumTo K4 (fun c4 => indB (!genB (αd c4))) ≤ B4) (fri : Nat → EF → EF → List (EF → EF) → V) (hncw : 4 ≤ ncw)
    (NR2 : Nat) (Rb : Nat → EF → EF → Nat → List (EF → EF)) (Ro : Nat → EF → EF → Nat → Wv)
    {NSl L KA sQ kQ nQ KQ NS2 NS3 n2 n3 : Nat} (hKA : 0 < KA) (hN : 0 < NSl) (hKL : KQ = KA ^ L)
    (hbl : ∀ k, bl k ≤ 26) {k0 : Nat} (hk0 : k0 ∈ [0, 2, 4, 6, 8, 10, 12, 14, 16, 18])
    (hs0 : sh k0 = 0) (hidx : ∀ c4, ∀ l ∈ idx c4, l < L) (hL : L = 2 ^ (bl k0 + 1))
    {h : List (List F) → Nat} {Mh : Nat} (hMh : 0 < Mh) (hnQ : L * (NSl * Mh) ≤ nQ) (hsQ : 1 ≤ sQ) (g : List (List (List F)) → List Nat → Pq)
    (nxt : Pq → Nat → List Nat → Nat) (d1 : List (List (List F)))
    (Com2 : List (List (List F)) → Nat → Nat) (Pf2 : Nat → List (List (List F)) → Nat → P2) (hc2 : ComHides NS2 Com2)
    (hp2 : ∀ c4, ComPfHides NS2 Com2 (Pf2 c4) (opF ((jGroups tbM tbC tbPo tbI tpT tpH tpR tpP tpS ((friS bl sh idx 0) c4) ((friS bl sh idx 2) c4) ((friS bl sh idx 4) c4) ((friS bl sh idx 6) c4) ((friS bl sh idx 8) c4) ((friS bl sh idx 10) c4) ((friS bl sh idx 12) c4) ((friS bl sh idx 14) c4) ((friS bl sh idx 16) c4) ((friS bl sh idx 18) c4) EF.zero qv).map (·.base.S)) [1, 3, 5, 7, 9, 11, 13, 15, 17, 19]))
    (hr2 : ∀ d σ, Com2 d σ < n2) (d2 : List (List (List F)))
    (Com3 : List (List (List (List F))) × List (List (List F)) → Nat → Nat)
    (Pf3 : Nat → List (List (List (List F))) × List (List (List F)) → Nat → P3) (hc3 : ComHides NS3 Com3)
    (hp3 : ∀ c4, ComPfHides NS3 Com3 (Pf3 c4) (fun d => (opQ (jSsT ((friS bl sh idx 0) c4) ((friS bl sh idx 2) c4) ((friS bl sh idx 4) c4) ((friS bl sh idx 6) c4) ((friS bl sh idx 8) c4) ((friS bl sh idx 10) c4) ((friS bl sh idx 12) c4) ((friS bl sh idx 14) c4) ((friS bl sh idx 16) c4) ((friS bl sh idx 18) c4)) d.1, opCw (jSsC tbM tbC tbPo tbI tpT tpH tpR tpP tpS ((friS bl sh idx 0) c4) ((friS bl sh idx 2) c4) ((friS bl sh idx 4) c4) ((friS bl sh idx 6) c4) ((friS bl sh idx 8) c4) ((friS bl sh idx 10) c4) ((friS bl sh idx 12) c4) ((friS bl sh idx 14) c4) ((friS bl sh idx 16) c4) ((friS bl sh idx 18) c4)) d.2)))
    (hr3 : ∀ d σ, Com3 d σ < n3) (d3 : List (List (List (List F))) × List (List (List F)))
    (E : Nat → Nat → Nat → Nat → Nat → Nat → Nat → Option (Pq × List Nat) × Option (P2 × P3) × TViewN (PcsPV (V × Wv)) (EF × EF) → Bool) :
    let opS := fun (c4 : Nat) => opF ((jGroups tbM tbC tbPo tbI tpT tpH tpR tpP tpS ((friS bl sh idx 0) c4) ((friS bl sh idx 2) c4) ((friS bl sh idx 4) c4) ((friS bl sh idx 6) c4) ((friS bl sh idx 8) c4) ((friS bl sh idx 10) c4) ((friS bl sh idx 12) c4) ((friS bl sh idx 14) c4) ((friS bl sh idx 16) c4) ((friS bl sh idx 18) c4) EF.zero qv).map (·.base.S)) [0, 2, 4, 6, 8, 10, 12, 14, 16, 18]
    let Com1 := comM KA NSl L (posRowsP (xsL bl sh) [0, 2, 4, 6, 8, 10, 12, 14, 16, 18] h NSl Mh)
    let Pf1 := fun (c4 : Nat) => pfM KA NSl L kQ (posRowsP (xsL bl sh) [0, 2, 4, 6, 8, 10, 12, 14, 16, 18] h NSl Mh) ((fun c4 l => decide (l ∈ idx c4)) c4) (opS c4) g nxt
    let Cmi := comMI KA NSl L L (posRowsP (xsL bl sh) [0, 2, 4, 6, 8, 10, 12, 14, 16, 18] h NSl Mh)
    let Pfi := fun (c4 : Nat) => pfMI KA NSl L L kQ (posRowsP (xsL bl sh) [0, 2, 4, 6, 8, 10, 12, 14, 16, 18] h NSl Mh) ((fun c4 l => decide (l ∈ idx c4)) c4) (opS c4) g nxt
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
    let NR0 := jNR off m.hd m.stk m.heap.length Ps.length m.stk m.heap N W segRoots roots jets C Mm Wt Rt Hd Tm Po Iw tbM tbC tbPo tbI tpT tpH tpR tpP tpS ((friS bl sh idx 0) 0) ((friS bl sh idx 2) 0) ((friS bl sh idx 4) 0) ((friS bl sh idx 6) 0) ((friS bl sh idx 8) 0) ((friS bl sh idx 10) 0) ((friS bl sh idx 12) 0) ((friS bl sh idx 14) 0) ((friS bl sh idx 16) 0) ((friS bl sh idx 18) 0) EF.zero qv (wm 0) (wc 0) (ww 0) (wpo 0) (wi 0) (wt 0) (wh 0) (wr 0) (wp 0) (wsg 0) ncw
    let pcsZ := fun (c4 c2 : Nat) (ζ : EF) t α β r => jPcs off m.hd m.stk m.heap.length Ps.length m.stk m.heap N W segRoots roots jets C Mm Wt Rt Hd Tm Po Iw tbM tbC tbPo tbI tpT tpH tpR tpP tpS ((friS bl sh idx 0) c4) ((friS bl sh idx 2) c4) ((friS bl sh idx 4) c4) ((friS bl sh idx 6) c4) ((friS bl sh idx 8) c4) ((friS bl sh idx 10) c4) ((friS bl sh idx 12) c4) ((friS bl sh idx 14) c4) ((friS bl sh idx 16) c4) ((friS bl sh idx 18) c4) ζ qv (wm c2) (wc c2) (ww c2) (wpo c2) (wi c2) (wt c2) (wh c2) (wr c2) (wp c2) (wsg c2) ncw (αd c4)
      (friX (fri c4) (Rb c4) (Ro c4) (r / NR0)) t α β (r % NR0)
    let psimZ := fun (c4 c2 : Nat) (ζ : EF) α β v r => jPsim off m.hd m.stk m.heap.length Ps.length m.stk m.heap N W segRoots roots jets C Mm Wt Rt Hd Tm Po Iw tbM tbC tbPo tbI tpT tpH tpR tpP tpS ((friS bl sh idx 0) c4) ((friS bl sh idx 2) c4) ((friS bl sh idx 4) c4) ((friS bl sh idx 6) c4) ((friS bl sh idx 8) c4) ((friS bl sh idx 10) c4) ((friS bl sh idx 12) c4) ((friS bl sh idx 14) c4) ((friS bl sh idx 16) c4) ((friS bl sh idx 18) c4) ζ qv (wm c2) (wc c2) (ww c2) (wpo c2) (wi c2) (wt c2) (wh c2) (wr c2) (wp c2) (wsg c2) ncw (αd c4)
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
    let q0 := jGroups tbM tbC tbPo tbI tpT tpH tpR tpP tpS ((friS bl sh idx 0) 0) ((friS bl sh idx 2) 0) ((friS bl sh idx 4) 0) ((friS bl sh idx 6) 0) ((friS bl sh idx 8) 0) ((friS bl sh idx 10) 0) ((friS bl sh idx 12) 0) ((friS bl sh idx 14) 0) ((friS bl sh idx 16) 0) ((friS bl sh idx 18) 0) EF.zero qv
    let qZ := fun (c4 : Nat) (ζ : EF) => jGroups tbM tbC tbPo tbI tpT tpH tpR tpP tpS ((friS bl sh idx 0) c4) ((friS bl sh idx 2) c4) ((friS bl sh idx 4) c4) ((friS bl sh idx 6) c4) ((friS bl sh idx 8) c4) ((friS bl sh idx 10) c4) ((friS bl sh idx 12) c4) ((friS bl sh idx 14) c4) ((friS bl sh idx 16) c4) ((friS bl sh idx 18) c4) ζ qv
    let Ss := fun c4 => (qZ c4 EF.zero).map (·.base.S)
    let ks := jKs m.hd m.stk m.heap.length Ps.length m.stk m.heap N W segRoots roots jets
    let cols := jCols off m.hd m.stk m.heap.length Ps.length m.stk m.heap N W segRoots roots jets C Mm Wt Rt Hd Tm Po Iw
    let tqZ := fun (c4 c2 : Nat) (ζ : EF) => (jTs off m.hd m.stk m.heap.length Ps.length m.stk m.heap N W segRoots roots jets C Mm Wt Rt Hd Tm Po Iw tbM tbC tbPo tbI tpT tpH tpR tpP tpS ((friS bl sh idx 0) c4) ((friS bl sh idx 2) c4) ((friS bl sh idx 4) c4) ((friS bl sh idx 6) c4) ((friS bl sh idx 8) c4) ((friS bl sh idx 10) c4) ((friS bl sh idx 12) c4) ((friS bl sh idx 14) c4) ((friS bl sh idx 16) c4) ((friS bl sh idx 18) c4) ζ qv (wm c2) (wc c2) (ww c2) (wpo c2) (wi c2) (wt c2) (wh c2) (wr c2) (wp c2) (wsg c2)).map Prod.fst
    let qdZ := fun (c4 c2 : Nat) (ζ : EF) (t : Nat → Tup) (α β : EF) (ms : List F) =>
      (jTs off m.hd m.stk m.heap.length Ps.length m.stk m.heap N W segRoots roots jets C Mm Wt Rt Hd Tm Po Iw tbM tbC tbPo tbI tpT tpH tpR tpP tpS ((friS bl sh idx 0) c4) ((friS bl sh idx 2) c4) ((friS bl sh idx 4) c4) ((friS bl sh idx 6) c4) ((friS bl sh idx 8) c4) ((friS bl sh idx 10) c4) ((friS bl sh idx 12) c4) ((friS bl sh idx 14) c4) ((friS bl sh idx 16) c4) ((friS bl sh idx 18) c4) ζ qv (wm c2) (wc c2) (ww c2) (wpo c2) (wi c2) (wt c2) (wh c2) (wr c2) (wp c2) (wsg c2)).map (fun p => p.2 t α β ms)
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
  have hM26 : tbM ≤ 26 := by omega
  have hC26 : tbC ≤ 26 := by omega
  have hPo26 : tbPo ≤ 26 := by omega
  have hI26 : tbI ≤ 26 := by omega
  obtain ⟨_, _, ⟨_, _, _, _, _, t1, _, h1, _, r1, _, p1, _, s1, _⟩⟩ :=
    compJ_run_facts hR hLm hLp hLi hprov hprov24 hrl hr hroots hA hlen hK hHP hHW hNW
  have hT26 : tpT ≤ 26 := by rw [htT]; omega
  have hH26 : tpH ≤ 26 := by rw [htH]; omega
  have hR26 : tpR ≤ 26 := by rw [htR]; omega
  have hP26 : tpP ≤ 26 := by rw [htP]; omega
  have hS26 : tpS ≤ 26 := by rw [htS]; omega
  subst hL
  have fl := compJ_fri_leaves (qv := qv) (h := h) (NSl := NSl) (Mh := Mh) hbl hk0 hs0 hM26 hC26 hPo26 hI26 hT26 hH26 hR26 hP26 hS26 hidx
  exact compJ_fs_open4ROMMC (kQ := kQ) (nQ := nQ) (sQ := sQ) off hR hLm hLp hLi hprov hprov24 hrl hr hroots hA hlen hK
    hHP hHW hNW htM htC htPo htI htT htH htR htP htS (friS bl sh idx 0) (friS bl sh idx 2) (friS bl sh idx 4) (friS bl sh idx 6) (friS bl sh idx 8) (friS bl sh idx 10) (friS bl sh idx 12) (friS bl sh idx 14) (friS bl sh idx 16) (friS bl sh idx 18) qv
    wm wc ww wpo wi wt wh wr wp wsg hlwm hlwc hlww hlwpo hlwi hlwt hlwh hlwr hlwp hlwsg hK2 hK4 φ hφ
    fl.1 fl.2.1 fl.2.2.1 fl.2.2.2.1 fl.2.2.2.2.1 fl.2.2.2.2.2.1 fl.2.2.2.2.2.2.1 fl.2.2.2.2.2.2.2.1 fl.2.2.2.2.2.2.2.2.1 fl.2.2.2.2.2.2.2.2.2.1
    hszM hszC hsz9 hszPo hszI hszT hszH hszR hszP hszS αd hB4 fri hncw NR2 Rb Ro
    hKA hN hKL (posRowsP (xsL bl sh) [0, 2, 4, 6, 8, 10, 12, 14, 16, 18] h NSl Mh)
    (fun d l a hl => Nat.lt_of_lt_of_le (posRowsP_lt (L := 2 ^ (bl k0 + 1)) hN hMh d l a hl)
      (Nat.le_trans (Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _)) hnQ)) g
    (fun d l v => Nat.le_trans (posRowsP_spread d l v) hsQ) nxt (fun c4 l => decide (l ∈ idx c4))
    (fun c4 d d' e l a hl => by
      rw [posRowsP_of_posRows (Nat.two_pow_pos (bl k0 + 1)), posRowsP_of_posRows (Nat.two_pow_pos (bl k0 + 1)),
        fl.2.2.2.2.2.2.2.2.2.2.1 c4 d d' e l a hl]) d1 Com2 Pf2 hc2 hp2 hr2 d2 Com3 Pf3
    hc3 hp3 hr3 d3 E

end Circuit
