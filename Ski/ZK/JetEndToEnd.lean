import Ski.ZK.ROMMerkleIdxCJ
import Ski.ZK.ROMMerkleIdxCP
import Ski.ZK.WitCompEndToEnd

/-!
# Every hypothesis of the jet and Poseidon2 Merkle-committed bounds, met at once

`WitCompEndToEnd` meets every hypothesis of `comp_fs_open4ROMMC_fri` beyond
the run's.  Here the same is done for `compJ_fs_open4ROMMC_fri` and
`compP_fs_open4ROMMC_fri`, so both bounds apply to every accepted run of
their circuits.

- **The heights.** At log blowup `1`, a group of height `2 ^ (t + 1)` has
  `bl = t + 1`.  The circuit with jets has ten main groups: memory, CPU,
  the fixed group `2 ^ 9`, POP and INSTW at the statement's `2 ^ Lp` and
  `2 ^ Li`, the template, header and roots provider tables, program and
  segments (`jetBl`).  The circuit with the Poseidon2 jet has nine:
  memory, CPU, the fixed group, P2IN, P2OUT and Poseidon2 at the
  statement's `2 ^ LI`, `2 ^ LO`, `2 ^ LP`, program, segments and the
  level table at `2 ^ 9` (`p2Bl`).
- **The floors.** Every table is padded from `2 ^ 9` (`pub_bounds`,
  `provCJ_tp_ge`), and the witness asks the statement's heights to meet
  the floor the statement check sets (`logOK`): `9 ≤ R, Lm`, and
  `9 ≤ Lp, Li` or `9 ≤ LI, LO, LP`.  So `100` queries fit every group.
- **The ceilings.** The program and segment tables are no taller than the
  memory and CPU traces (`pub_bounds`), as in the composed circuit.  With
  the Poseidon2 jet every group is then at most `2 ^ 20`: the tallest has
  `bl ≤ 20`, and the Merkle term is the composed one's (`compStd_merkle`).
  With jets the provider tables depend on the public jet list, not the
  run, and are bounded only by `compJ_fs_open4ROMMC_fri`'s own `2 ^ 24`
  rows: the tallest has `bl ≤ 24`, so the Merkle tree has at most
  `2 ^ 25` leaves and the term is below `NSl / 2 ^ 34` (`jetStd_merkle`),
  against the composed `NSl / 2 ^ 38`.

Limits, as `WitCompEndToEnd`'s: the salt commitments hide and bind nothing,
and one salt of four field elements stands in for Plonky3's per-matrix
salts, so these show the hypotheses consistent, not that Plonky3 meets
them.  Lean ties the heights to the statement text's by name only.
-/

set_option autoImplicit false

namespace Circuit
open ZKF

/-- **A provider table is at least `2 ^ 9` rows**, the floor `padCopiesMin`
    pads to. -/
theorem provCJ_tp_ge {raw : List (List F)} (h0 : 0 < (padCopiesMin raw).length)
    (h24 : (padCopiesMin raw).length ≤ 2 ^ 24) : 8 ≤ provTpCJ (padCopiesMin raw) := by
  match raw, h0 with
  | r :: rs, _ =>
    have hle : (r :: rs).length ≤ 2 ^ 24 := Nat.le_trans (padCopiesMin_length_ge (r :: rs)) h24
    obtain ⟨d, h9, _, hd⟩ := padPow (r :: rs) r (e := 9) (by decide) hle
    have hd' : (padCopiesMin (r :: rs)).length = 2 ^ d := hd
    have ht : provTpCJ (padCopiesMin (r :: rs)) = d - 1 := by unfold provTpCJ; rw [hd', lgF_pow 64 d (by omega)]
    rw [ht]; exact Nat.le_sub_of_add_le h9

/-- **The public program and segment tables lie between `2 ^ 9` and the
    traces**: a heap within `2 ^ Lm` cells and roots within `2 ^ R`, each
    padded from `2 ^ 9`. -/
theorem pub_bounds {R Lm : Nat} (hR : R ≤ 20) (hLm : Lm ≤ 20) (h9R : 9 ≤ R) (h9M : 9 ≤ Lm)
    {heap : List Cell} {N W : Nat} {roots : List Nat}
    (hh : heap.length ≤ 2 ^ Lm) (hr : roots.length ≤ 2 ^ R) :
    8 ≤ progTpC heap N W ∧ 8 ≤ segTp roots ∧ progTpC heap N W + 1 ≤ Lm ∧ segTp roots + 1 ≤ R := by
  have hh24 : heap.length ≤ 2 ^ 24 := Nat.le_trans hh (Nat.pow_le_pow_right (by decide) (by omega))
  have hr24 : roots.length ≤ 2 ^ 24 := Nat.le_trans hr (Nat.pow_le_pow_right (by decide) (by omega))
  obtain ⟨_, p2⟩ := progC_height (heap := heap) (N := N) (W := W) hh24
  obtain ⟨_, s2⟩ := segsC_height (roots := roots) hr24
  have hP0 := pad9_le ((heap.zipIdx.filter fun (_, i) => !(3 ≤ i && i < 3 + N + W)).map
      fun (c, i) => [ofN i, ofN (cellTag c), ofN (cellFields c).1, ofN (cellFields c).2, ofN 1])
      [ofN 0, ofN 0, ofN 0, ofN 0, ofN 0] h9M (Nat.le_trans hLm (by decide))
      (by rw [List.length_map]; exact Nat.le_trans (List.length_filter_le _ _) (by rw [List.length_zipIdx]; exact hh))
  have hP : (progTableC heap N W).h ≤ 2 ^ Lm := hP0
  have hS0 := pad9_le (roots.zipIdx.map fun (r, j) => [ofN j, ofN r])
      ((roots.zipIdx.map fun (r, j) => [ofN j, ofN r]).headD []) h9R (Nat.le_trans hR (by decide))
      (by rw [List.length_map, List.length_zipIdx]; exact hr)
  have hS : (segsPub roots).h ≤ 2 ^ R := hS0
  exact ⟨progC_tp_ge hh24, segsC_tp_ge hr24, tp_le_of_h p2 hP, tp_le_of_h s2 hS⟩

/-- The circuit with jets' group heights at log blowup `1`: memory, CPU,
    the fixed group `2 ^ 9`, POP, INSTW, templates, headers, roots, program,
    segments. -/
def jetBl (tbM tbC tbPo tbI tpT tpH tpR tpP tpS k : Nat) : Nat :=
  if k < 2 then tbM + 1 else if k < 4 then tbC + 1 else if k < 6 then 9 else if k < 8 then tbPo + 1
  else if k < 10 then tbI + 1 else if k < 12 then tpT + 1 else if k < 14 then tpH + 1
  else if k < 16 then tpR + 1 else if k < 18 then tpP + 1 else tpS + 1

/-- Every group of the circuit with jets is at most `2 ^ B`, when each
    height is and `9 ≤ B`. -/
theorem jetBl_le {tbM tbC tbPo tbI tpT tpH tpR tpP tpS B : Nat} (h9 : 9 ≤ B)
    (hM : tbM + 1 ≤ B) (hC : tbC + 1 ≤ B) (hPo : tbPo + 1 ≤ B) (hI : tbI + 1 ≤ B) (hT : tpT + 1 ≤ B)
    (hH : tpH + 1 ≤ B) (hR : tpR + 1 ≤ B) (hP : tpP + 1 ≤ B) (hS : tpS + 1 ≤ B) :
    ∀ k, jetBl tbM tbC tbPo tbI tpT tpH tpR tpP tpS k ≤ B := fun k => by
  unfold jetBl
  repeat' split
  all_goals assumption

/-- The circuit with the Poseidon2 jet's group heights at log blowup `1`:
    memory, CPU, the fixed group `2 ^ 9`, P2IN, P2OUT, Poseidon2, program,
    segments, the level table `2 ^ 9`. -/
def p2Bl (tbM tbC tbI tbO tbQ tpP tpS k : Nat) : Nat :=
  if k < 2 then tbM + 1 else if k < 4 then tbC + 1 else if k < 6 then 9 else if k < 8 then tbI + 1
  else if k < 10 then tbO + 1 else if k < 12 then tbQ + 1 else if k < 14 then tpP + 1
  else if k < 16 then tpS + 1 else 9

/-- Every group of the circuit with the Poseidon2 jet is at most `2 ^ B`,
    when each height is and `9 ≤ B`. -/
theorem p2Bl_le {tbM tbC tbI tbO tbQ tpP tpS B : Nat} (h9 : 9 ≤ B)
    (hM : tbM + 1 ≤ B) (hC : tbC + 1 ≤ B) (hI : tbI + 1 ≤ B) (hO : tbO + 1 ≤ B) (hQ : tbQ + 1 ≤ B)
    (hP : tpP + 1 ≤ B) (hS : tpS + 1 ≤ B) :
    ∀ k, p2Bl tbM tbC tbI tbO tbQ tpP tpS k ≤ B := fun k => by
  unfold p2Bl
  repeat' split
  all_goals assumption

/-- **The Merkle hiding term with jets**, for every `L ≤ 2 ^ 25` leaves (the
    tallest provider table `2 ^ 24` rows at log blowup `1`), one salt of
    four BabyBear elements, `2 ^ 64` leaf-hash queries. -/
theorem jetStd_merkle {L : Nat} (hL : L ≤ 2 ^ 25) :
    2 ^ 34 * (L * 1 * (2 ^ 64 + L) + 2 * L ^ 2 * 1) < 2013265921 ^ 4 :=
  Nat.lt_of_le_of_lt
    (Nat.mul_le_mul_left _ (Nat.add_le_add
      (Nat.mul_le_mul (Nat.mul_le_mul_right 1 hL) (Nat.add_le_add_left hL _))
      (Nat.mul_le_mul_right 1 (Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left hL 2)))))
    (by decide)

section
open B Air Stmt Mach Sudoku SudokuText Compose CompM Wit

set_option maxRecDepth 100000 in
/-- **`compJ_fs_open4ROMMC_fri` applies to every accepted run with jets**
    whose statement's heights meet the statement check's floor `2 ^ 9`: its
    hypotheses beyond the run's met together at log blowup `1`, `100`
    queries over the tallest group, `8`-element leaf digests and salt
    commitments in the second and third slots.  The tallest group has
    `bl ≤ 24`, so the Merkle tree has at most `2 ^ 25` leaves. -/
theorem compJ_fs_open4ROMMC_fri_sat {V Wv Pq : Type} (off : EF → String → EF) {R Lm Lp Li : Nat} (hR : R ≤ 20)
    (hLm : Lm ≤ 20) (hLp : Lp ≤ 20) (hLi : Li ≤ 20)
    (h9R : 9 ≤ R) (h9M : 9 ≤ Lm) (h9P : 9 ≤ Lp) (h9I : 9 ≤ Li)
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
    (qv : EF → EF → List EF → F → List F → List F → List EF)
    (wm wc ww wpo wi wt wh wr wp wsg : Nat → List (EF → EF → List F))
    {Lwm Lwc Lww Lwpo Lwi Lwt Lwh Lwr Lwp Lwsg : Nat} (hlwm : ∀ c, (wm c).length = Lwm)
    (hlwc : ∀ c, (wc c).length = Lwc) (hlww : ∀ c, (ww c).length = Lww) (hlwpo : ∀ c, (wpo c).length = Lwpo)
    (hlwi : ∀ c, (wi c).length = Lwi) (hlwt : ∀ c, (wt c).length = Lwt) (hlwh : ∀ c, (wh c).length = Lwh)
    (hlwr : ∀ c, (wr c).length = Lwr) (hlwp : ∀ c, (wp c).length = Lwp) (hlwsg : ∀ c, (wsg c).length = Lwsg)
    {K2 K4 : Nat} (hK2 : 0 < K2) (hK4 : 0 < K4)
    (φ : Nat → Option (List (List (List EF)) × List (List (List (List EF))) × List (List (List EF))) → Nat)
    {N4 : Nat} (hφ : ∀ m w, φ m w < N4) (αd : Nat → EF)
    (fri : Nat → EF → EF → List (EF → EF) → V) (NR2 : Nat)
    (Rb : Nat → EF → EF → Nat → List (EF → EF)) (Ro : Nat → EF → EF → Nat → Wv)
    {n2 n3 : Nat} (hn2 : 0 < n2) (hn3 : 0 < n3)
    (h : List (List F) → Nat) (kQ : Nat)
    (g : List (List (List F)) → List Nat → Pq) (nxt : Pq → Nat → List Nat → Nat)
    (d1 : List (List (List F))) (d2 : List (List (List F)))
    (d3 : List (List (List (List F))) × List (List (List F))) :
    jetBl (Lm - 1) (R - 1) (Lp - 1) (Li - 1) (provTpCJ (tmplRowsCJ jets)) (provTpCJ (hdrRowsCJ jets))
      (provTpCJ (rootsRowsCJ roots)) (progTpC (blankM shp W Ps).heap (BT.nleaves shp) W)
      (segTp (blankRoots shp W Ps))
      (topK (jetBl (Lm - 1) (R - 1) (Lp - 1) (Li - 1) (provTpCJ (tmplRowsCJ jets)) (provTpCJ (hdrRowsCJ jets))
        (provTpCJ (rootsRowsCJ roots)) (progTpC (blankM shp W Ps).heap (BT.nleaves shp) W)
        (segTp (blankRoots shp W Ps))) [0, 2, 4, 6, 8, 10, 12, 14, 16, 18]) ≤ 24 := by
  -- the public tables, between `2 ^ 9` and the traces
  have hl : region.length = (List.replicate W Cell.S).length := by rw [List.length_replicate, hrl]
  obtain ⟨_, hstk, hroots', hlenm, _, _⟩ :=
    cMachine_public ρ (fun _ => false) shp region (List.replicate W .S) Ps hl
  have hA' := hA
  have eR : (cHeap ρ shp region Ps).2 = blankRoots shp W Ps := hroots'
  have eN : (cHeap ρ shp region Ps).1.length = (blankM shp W Ps).stk := hstk
  rw [eR, eN] at hA'
  have hn : 0 < Ps.length := hA'.npos
  have hnK : Ps.length ≤ 2 ^ R := by
    have := emono_ge hA'.emono (Ps.length - 1) (by omega); omega
  have h0 : A.take (cMachine ρ shp region Ps).heap.length = (cMachine ρ shp region Ps).heap := by
    rw [← hA'.ctr0]; exact hA'.heap0
  have hml := congrArg List.length h0
  rw [List.length_take] at hml
  have e1 : (cMachine ρ shp region Ps).heap.length = (blankM shp W Ps).heap.length := hlenm
  have hpub := pub_bounds (N := BT.nleaves shp) (W := W) hR hLm h9R h9M
    (heap := (blankM shp W Ps).heap) (roots := blankRoots shp W Ps) (by omega)
    (by rw [blankRoots_length]; exact hnK)
  -- the provider tables, between `2 ^ 9` and `2 ^ 24`
  have hT8 : 8 ≤ provTpCJ (tmplRowsCJ jets) := provCJ_tp_ge hprov.2.2 hprov24.2.2
  have hH8 : 8 ≤ provTpCJ (hdrRowsCJ jets) := provCJ_tp_ge hprov.2.1 hprov24.2.1
  have hR8 : 8 ≤ provTpCJ (rootsRowsCJ roots) := provCJ_tp_ge hprov.1 hprov24.1
  have hT23 : provTpCJ (tmplRowsCJ jets) ≤ 23 := (provCJ_height hprov.2.2 hprov24.2.2).1
  have hH23 : provTpCJ (hdrRowsCJ jets) ≤ 23 := (provCJ_height hprov.2.1 hprov24.2.1).1
  have hR23 : provTpCJ (rootsRowsCJ roots) ≤ 23 := (provCJ_height hprov.1 hprov24.1).1
  let tpT := provTpCJ (tmplRowsCJ jets)
  let tpH := provTpCJ (hdrRowsCJ jets)
  let tpR := provTpCJ (rootsRowsCJ roots)
  let tpP := progTpC (blankM shp W Ps).heap (BT.nleaves shp) W
  let tpS := segTp (blankRoots shp W Ps)
  let tbM := Lm - 1
  let tbC := R - 1
  let tbPo := Lp - 1
  let tbI := Li - 1
  have htM : tbM + 1 = Lm := Nat.sub_add_cancel (Nat.le_trans (by decide) h9M)
  have htC : tbC + 1 = R := Nat.sub_add_cancel (Nat.le_trans (by decide) h9R)
  have htPo : tbPo + 1 = Lp := Nat.sub_add_cancel (Nat.le_trans (by decide) h9P)
  have htI : tbI + 1 = Li := Nat.sub_add_cancel (Nat.le_trans (by decide) h9I)
  let bl := jetBl tbM tbC tbPo tbI tpT tpH tpR tpP tpS
  let k0 := topK bl [0, 2, 4, 6, 8, 10, 12, 14, 16, 18]
  let sh := fun k => bl k0 - bl k
  let idx := fun c => qIdx (bl k0 + 1) 100 c
  have hbl26' : ∀ k, bl k ≤ 24 := fun k => jetBl_le (B := 24) (by decide)
      (by rw [htM]; exact Nat.le_trans hLm (by decide)) (by rw [htC]; exact Nat.le_trans hR (by decide))
      (by rw [htPo]; exact Nat.le_trans hLp (by decide)) (by rw [htI]; exact Nat.le_trans hLi (by decide))
      (Nat.succ_le_succ hT23) (Nat.succ_le_succ hH23) (Nat.succ_le_succ hR23)
      (Nat.le_trans (Nat.le_trans hpub.2.2.1 hLm) (by decide)) (Nat.le_trans (Nat.le_trans hpub.2.2.2 hR) (by decide)) k
  have hbl26 : ∀ k, bl k ≤ 26 := fun k => Nat.le_trans (hbl26' k) (by decide)
  have _ := compJ_fs_open4ROMMC_fri off hR hLm hLp hLi hprov hprov24 hrl hr hroots hA hlen hK hHP hHW hNW
    htM htC htPo htI (tpT := tpT) (tpH := tpH) (tpR := tpR) (tpP := tpP) (tpS := tpS) rfl rfl rfl rfl rfl
    (bl := bl) (sh := sh) (idx := idx)
    qv wm wc ww wpo wi wt wh wr wp wsg hlwm hlwc hlww hlwpo hlwi hlwt hlwh hlwr hlwp hlwsg hK2 hK4 φ hφ
    (fun c4 => friS_qIdx100_fits bl sh _ 0 c4 (by rw [htM]; exact Nat.pow_le_pow_right (by decide) h9M))
    (fun c4 => friS_qIdx100_fits bl sh _ 2 c4 (by rw [htC]; exact Nat.pow_le_pow_right (by decide) h9R))
    (fun c4 => friS_qIdx100_fits bl sh _ 4 c4 (Nat.le_refl _))
    (fun c4 => friS_qIdx100_fits bl sh _ 6 c4 (by rw [htPo]; exact Nat.pow_le_pow_right (by decide) h9P))
    (fun c4 => friS_qIdx100_fits bl sh _ 8 c4 (by rw [htI]; exact Nat.pow_le_pow_right (by decide) h9I))
    (fun c4 => friS_qIdx100_fits bl sh _ 10 c4 (pow9_le hT8))
    (fun c4 => friS_qIdx100_fits bl sh _ 12 c4 (pow9_le hH8))
    (fun c4 => friS_qIdx100_fits bl sh _ 14 c4 (pow9_le hR8))
    (fun c4 => friS_qIdx100_fits bl sh _ 16 c4 (pow9_le hpub.1))
    (fun c4 => friS_qIdx100_fits bl sh _ 18 c4 (pow9_le hpub.2.1))
    αd (Nat.le_refl _) fri (Nat.le_refl 4) NR2 Rb Ro
    (NSl := 2013265921 ^ 4) (L := 2 ^ (bl k0 + 1)) (KA := 2013265921 ^ 8) (sQ := 1) (kQ := kQ)
    (nQ := 2 ^ (bl k0 + 1) * (2013265921 ^ 4 * 2013265921 ^ 8)) (KQ := (2013265921 ^ 8) ^ 2 ^ (bl k0 + 1))
    (NS2 := n2) (NS3 := n3) (n2 := n2) (n3 := n3)
    (Nat.pow_pos (by decide)) (by decide) rfl hbl26
    (topK_mem bl 0 [2, 4, 6, 8, 10, 12, 14, 16, 18]) (Nat.sub_self _) (fun c4 => qIdx_lt _ 100 c4) rfl (h := h)
    (Mh := 2013265921 ^ 8) (Nat.pow_pos (by decide))
    (Nat.le_refl _) (Nat.le_refl 1) g nxt d1
    (fun _ σ => σ % n2)
    (fun c4 d _ => opF ((jGroups tbM tbC tbPo tbI tpT tpH tpR tpP tpS ((friS bl sh idx 0) c4) ((friS bl sh idx 2) c4)
      ((friS bl sh idx 4) c4) ((friS bl sh idx 6) c4) ((friS bl sh idx 8) c4) ((friS bl sh idx 10) c4)
      ((friS bl sh idx 12) c4) ((friS bl sh idx 14) c4) ((friS bl sh idx 16) c4) ((friS bl sh idx 18) c4)
      EF.zero qv).map (·.base.S)) [1, 3, 5, 7, 9, 11, 13, 15, 17, 19] d)
    (comSalt_hides n2) (fun _ => comSalt_pf n2 _) (comSalt_lt hn2) d2
    (fun _ σ => σ % n3)
    (fun c4 d _ => (opQ (jSsT ((friS bl sh idx 0) c4) ((friS bl sh idx 2) c4) ((friS bl sh idx 4) c4)
        ((friS bl sh idx 6) c4) ((friS bl sh idx 8) c4) ((friS bl sh idx 10) c4) ((friS bl sh idx 12) c4)
        ((friS bl sh idx 14) c4) ((friS bl sh idx 16) c4) ((friS bl sh idx 18) c4)) d.1,
      opCw (jSsC tbM tbC tbPo tbI tpT tpH tpR tpP tpS ((friS bl sh idx 0) c4) ((friS bl sh idx 2) c4)
        ((friS bl sh idx 4) c4) ((friS bl sh idx 6) c4) ((friS bl sh idx 8) c4) ((friS bl sh idx 10) c4)
        ((friS bl sh idx 12) c4) ((friS bl sh idx 14) c4) ((friS bl sh idx 16) c4) ((friS bl sh idx 18) c4)) d.2))
    (comSalt_hides n3) (fun _ => comSalt_pf n3 _) (comSalt_lt hn3) d3 (fun _ _ _ _ _ _ _ _ => true)
  exact hbl26' _

end

section
open B Air Compose CompM Stmt Mach Wit ComposedPText

set_option maxRecDepth 100000 in
/-- **`compP_fs_open4ROMMC_fri` applies to every accepted run with the
    Poseidon2 jet**, at any public call count `nc`, whose statement's heights
    meet the statement check's floor `2 ^ 9`: its hypotheses beyond the
    run's met together at log blowup `1`, `100` queries over the tallest
    group, `8`-element leaf digests and salt commitments in the second and
    third slots.  The tallest group has `bl ≤ 20`, so the Merkle tree has at
    most `2 ^ 21` leaves, as the composed circuit's. -/
theorem compP_fs_open4ROMMC_fri_sat {V Wv Pq : Type} (off : EF → String → EF) {R Lm LI LO LP : Nat} (hR : R ≤ 20)
    (hLm : Lm ≤ 20) (hLI : LI ≤ 20) (hLO : LO ≤ 20) (hLP : LP ≤ 20)
    (h9R : 9 ≤ R) (h9M : 9 ≤ Lm) (h9I : 9 ≤ LI) (h9O : 9 ≤ LO) (h9P : 9 ≤ LP) {Vs : List OTerm}
    {ρ : Nat → Bool} {region : List Cell} (hrl : region.length = 1)
    (hr : ∀ i c, region[i]? = some c → cellOK (BT.nleaves shpP + 3 + i) c = true)
    {A : List Cell} {e : Nat → Nat} {row : Nat → Air.Row}
    (hA : AcceptsCP A (cMachineO ρ shpP region Vs) [] [] JP2 rootP (cHeapO ρ shpP region Vs).2
      (cHeapO ρ shpP region Vs).1.length Vs.length e row)
    (hlen : A.length = 2 ^ Lm) (hK : e (Vs.length - 1) < 2 ^ R)
    (hHI : ((runP ρ region Vs A e row).pinRows (2 ^ R)).length ≤ 2 ^ LI)
    (hHO : ((runP ρ region Vs A e row).poutRows (2 ^ R)).length ≤ 2 ^ LO)
    (hHP : ((runP ρ region Vs A e row).p2Rows (2 ^ R)).length ≤ 2 ^ LP)
    {nc : Nat} (hcalls : (runP ρ region Vs A e row).calls (2 ^ R) = nc)
    (qv : EF → EF → List EF → F → List F → List F → List EF)
    (wm wc ww wi wo wq wp wsg wx : Nat → List (EF → EF → List F))
    {Lwm Lwc Lww Lwi Lwo Lwq Lwp Lwsg Lwx : Nat}
    (hlwm : ∀ c, (wm c).length = Lwm) (hlwc : ∀ c, (wc c).length = Lwc) (hlww : ∀ c, (ww c).length = Lww)
    (hlwi : ∀ c, (wi c).length = Lwi) (hlwo : ∀ c, (wo c).length = Lwo) (hlwq : ∀ c, (wq c).length = Lwq)
    (hlwp : ∀ c, (wp c).length = Lwp) (hlwsg : ∀ c, (wsg c).length = Lwsg) (hlwx : ∀ c, (wx c).length = Lwx)
    {K2 K4 : Nat} (hK2 : 0 < K2) (hK4 : 0 < K4)
    (φ : Nat → Option (List (List (List EF)) × List (List (List (List EF))) × List (List (List EF))) → Nat)
    {N4 : Nat} (hφ : ∀ m w, φ m w < N4) (αd : Nat → EF)
    (fri : Nat → EF → EF → List (EF → EF) → V) (NR2 : Nat)
    (Rb : Nat → EF → EF → Nat → List (EF → EF)) (Ro : Nat → EF → EF → Nat → Wv)
    {n2 n3 : Nat} (hn2 : 0 < n2) (hn3 : 0 < n3)
    (h : List (List F) → Nat) (kQ : Nat)
    (g : List (List (List F)) → List Nat → Pq) (nxt : Pq → Nat → List Nat → Nat)
    (d1 : List (List (List F))) (d2 : List (List (List F)))
    (d3 : List (List (List (List F))) × List (List (List F))) :
    p2Bl (Lm - 1) (R - 1) (LI - 1) (LO - 1) (LP - 1) (progTpC (blankMO shpP 1 Vs).heap (BT.nleaves shpP) 1)
      (segTp (blankRootsO shpP 1 Vs))
      (topK (p2Bl (Lm - 1) (R - 1) (LI - 1) (LO - 1) (LP - 1) (progTpC (blankMO shpP 1 Vs).heap (BT.nleaves shpP) 1)
        (segTp (blankRootsO shpP 1 Vs))) [0, 2, 4, 6, 8, 10, 12, 14, 16]) ≤ 20 := by
  -- the public tables, between `2 ^ 9` and the traces
  have hl : region.length = (List.replicate 1 Cell.S).length := by rw [List.length_replicate, hrl]
  obtain ⟨_, hstk, hroots', hlenm, _, _⟩ :=
    cMachineO_public ρ (fun _ => false) shpP region (List.replicate 1 .S) Vs hl
  have hA' := hA
  have eR : (cHeapO ρ shpP region Vs).2 = blankRootsO shpP 1 Vs := hroots'
  have eN : (cHeapO ρ shpP region Vs).1.length = (blankMO shpP 1 Vs).stk := hstk
  rw [eR, eN] at hA'
  have hn : 0 < Vs.length := hA'.npos
  have hnK : Vs.length ≤ 2 ^ R := by
    have := emono_ge hA'.emono (Vs.length - 1) (by omega); omega
  have h0 : A.take (cMachineO ρ shpP region Vs).heap.length = (cMachineO ρ shpP region Vs).heap := by
    rw [← hA'.ctr0]; exact hA'.heap0
  have hml := congrArg List.length h0
  rw [List.length_take] at hml
  have e1 : (cMachineO ρ shpP region Vs).heap.length = (blankMO shpP 1 Vs).heap.length := hlenm
  have hpub := pub_bounds (N := BT.nleaves shpP) (W := 1) hR hLm h9R h9M
    (heap := (blankMO shpP 1 Vs).heap) (roots := blankRootsO shpP 1 Vs) (by omega)
    (by rw [blankRootsO_length]; exact hnK)
  let tpP := progTpC (blankMO shpP 1 Vs).heap (BT.nleaves shpP) 1
  let tpS := segTp (blankRootsO shpP 1 Vs)
  let tbM := Lm - 1
  let tbC := R - 1
  let tbI := LI - 1
  let tbO := LO - 1
  let tbQ := LP - 1
  have htM : tbM + 1 = Lm := Nat.sub_add_cancel (Nat.le_trans (by decide) h9M)
  have htC : tbC + 1 = R := Nat.sub_add_cancel (Nat.le_trans (by decide) h9R)
  have htI : tbI + 1 = LI := Nat.sub_add_cancel (Nat.le_trans (by decide) h9I)
  have htO : tbO + 1 = LO := Nat.sub_add_cancel (Nat.le_trans (by decide) h9O)
  have htQ : tbQ + 1 = LP := Nat.sub_add_cancel (Nat.le_trans (by decide) h9P)
  let bl := p2Bl tbM tbC tbI tbO tbQ tpP tpS
  let k0 := topK bl [0, 2, 4, 6, 8, 10, 12, 14, 16]
  let sh := fun k => bl k0 - bl k
  let idx := fun c => qIdx (bl k0 + 1) 100 c
  have hbl20 : ∀ k, bl k ≤ 20 := p2Bl_le (by decide)
    (by rw [htM]; exact hLm) (by rw [htC]; exact hR) (by rw [htI]; exact hLI) (by rw [htO]; exact hLO)
    (by rw [htQ]; exact hLP) (Nat.le_trans hpub.2.2.1 hLm) (Nat.le_trans hpub.2.2.2 hR)
  have _ := compP_fs_open4ROMMC_fri off hR hLm hLI hLO hLP hrl hr hA hlen hK hHI hHO hHP hcalls
    htM htC htI htO htQ (tpP := tpP) (tpS := tpS) rfl rfl
    (bl := bl) (sh := sh) (idx := idx)
    qv wm wc ww wi wo wq wp wsg wx hlwm hlwc hlww hlwi hlwo hlwq hlwp hlwsg hlwx hK2 hK4 φ hφ
    (fun c4 => friS_qIdx100_fits bl sh _ 0 c4 (by rw [htM]; exact Nat.pow_le_pow_right (by decide) h9M))
    (fun c4 => friS_qIdx100_fits bl sh _ 2 c4 (by rw [htC]; exact Nat.pow_le_pow_right (by decide) h9R))
    (fun c4 => friS_qIdx100_fits bl sh _ 4 c4 (Nat.le_refl _))
    (fun c4 => friS_qIdx100_fits bl sh _ 6 c4 (by rw [htI]; exact Nat.pow_le_pow_right (by decide) h9I))
    (fun c4 => friS_qIdx100_fits bl sh _ 8 c4 (by rw [htO]; exact Nat.pow_le_pow_right (by decide) h9O))
    (fun c4 => friS_qIdx100_fits bl sh _ 10 c4 (by rw [htQ]; exact Nat.pow_le_pow_right (by decide) h9P))
    (fun c4 => friS_qIdx100_fits bl sh _ 12 c4 (pow9_le hpub.1))
    (fun c4 => friS_qIdx100_fits bl sh _ 14 c4 (pow9_le hpub.2.1))
    (fun c4 => friS_qIdx100_fits bl sh _ 16 c4 (Nat.le_refl _))
    αd (Nat.le_refl _) fri (Nat.le_refl 4) NR2 Rb Ro
    (NSl := 2013265921 ^ 4) (L := 2 ^ (bl k0 + 1)) (KA := 2013265921 ^ 8) (sQ := 1) (kQ := kQ)
    (nQ := 2 ^ (bl k0 + 1) * (2013265921 ^ 4 * 2013265921 ^ 8)) (KQ := (2013265921 ^ 8) ^ 2 ^ (bl k0 + 1))
    (NS2 := n2) (NS3 := n3) (n2 := n2) (n3 := n3)
    (Nat.pow_pos (by decide)) (by decide) rfl (fun k => Nat.le_trans (hbl20 k) (by decide))
    (topK_mem bl 0 [2, 4, 6, 8, 10, 12, 14, 16]) (Nat.sub_self _) (fun c4 => qIdx_lt _ 100 c4) rfl (h := h)
    (Mh := 2013265921 ^ 8) (Nat.pow_pos (by decide))
    (Nat.le_refl _) (Nat.le_refl 1) g nxt d1
    (fun _ σ => σ % n2)
    (fun c4 d _ => opF ((pGroups tbM tbC tbI tbO tbQ tpP tpS ((friS bl sh idx 0) c4) ((friS bl sh idx 2) c4)
      ((friS bl sh idx 4) c4) ((friS bl sh idx 6) c4) ((friS bl sh idx 8) c4) ((friS bl sh idx 10) c4)
      ((friS bl sh idx 12) c4) ((friS bl sh idx 14) c4) ((friS bl sh idx 16) c4) EF.zero qv).map (·.base.S))
      [1, 3, 5, 7, 9, 11, 13, 15, 17] d)
    (comSalt_hides n2) (fun _ => comSalt_pf n2 _) (comSalt_lt hn2) d2
    (fun _ σ => σ % n3)
    (fun c4 d _ => (opQ (pSsT ((friS bl sh idx 0) c4) ((friS bl sh idx 2) c4) ((friS bl sh idx 4) c4)
        ((friS bl sh idx 6) c4) ((friS bl sh idx 8) c4) ((friS bl sh idx 10) c4) ((friS bl sh idx 12) c4)
        ((friS bl sh idx 14) c4) ((friS bl sh idx 16) c4)) d.1,
      opCw (pSsC tbM tbC tbI tbO tbQ tpP tpS ((friS bl sh idx 0) c4) ((friS bl sh idx 2) c4)
        ((friS bl sh idx 4) c4) ((friS bl sh idx 6) c4) ((friS bl sh idx 8) c4) ((friS bl sh idx 10) c4)
        ((friS bl sh idx 12) c4) ((friS bl sh idx 14) c4) ((friS bl sh idx 16) c4)) d.2))
    (comSalt_hides n3) (fun _ => comSalt_pf n3 _) (comSalt_lt hn3) d3 (fun _ _ _ _ _ _ _ _ => true)
  exact hbl20 _

end

end Circuit
