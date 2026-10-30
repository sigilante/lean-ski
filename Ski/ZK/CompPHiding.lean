import Ski.ZK.CompPInst

/-!
# The composed proof with the Poseidon2 jet: the honest run's facts

`compP_run_facts`: for an accepting run of the circuit with the Poseidon2
jet (the hypotheses of `compPG_complete_log`, whose verifiers call the jet
a public number of times `nc`, `hcalls`), the honest tables meet `compP_transcript`'s hypotheses
(`P2Run.honest_zkP`), each private table meets its AIR (`Sat`), and each
has the height its quotient group needs: the CPU `2^R`, the memory `2^Lm`,
the witness `2^9`, P2IN, P2OUT and Poseidon2 their budgets `2^LI`,
`2^LO`, `2^LP`, and the program and segments tables powers of two
`2^(tp + 1)`, `tp ≤ 23`.  The level table is the published `idxPub nc`.
-/

namespace Circuit

open ZKF B Air Compose CompM Stmt Mach Wit ComposedPText

set_option maxRecDepth 100000 in
/-- **An accepting run with the Poseidon2 jet meets the hiding PCS's
    hypotheses.** -/
theorem compP_run_facts {R Lm LI LO LP : Nat} (hR : R ≤ 20) (hLm : Lm ≤ 20) (hLI : LI ≤ 20)
    (hLO : LO ≤ 20) (hLP : LP ≤ 20) {Vs : List OTerm}
    {ρ : Nat → Bool} {region : List Cell} (hrl : region.length = 1)
    (hr : ∀ i c, region[i]? = some c → cellOK (BT.nleaves shpP + 3 + i) c = true)
    {A : List Cell} {e : Nat → Nat} {row : Nat → Air.Row}
    (hA : AcceptsCP A (cMachineO ρ shpP region Vs) [] [] JP2 rootP (cHeapO ρ shpP region Vs).2
      (cHeapO ρ shpP region Vs).1.length Vs.length e row)
    (hlen : A.length = 2 ^ Lm) (hK : e (Vs.length - 1) < 2 ^ R)
    (hHI : ((runP ρ region Vs A e row).pinRows (2 ^ R)).length ≤ 2 ^ LI)
    (hHO : ((runP ρ region Vs A e row).poutRows (2 ^ R)).length ≤ 2 ^ LO)
    (hHP : ((runP ρ region Vs A e row).p2Rows (2 ^ R)).length ≤ 2 ^ LP)
    {nc : Nat} (hcalls : (runP ρ region Vs A e row).calls (2 ^ R) = nc) :
    let m := blankMO shpP 1 Vs
    let segRoots := blankRootsO shpP 1 Vs
    let N := BT.nleaves shpP
    let Rn : P2Run := ⟨A, JP2, rootP, segRoots, e, Vs.length, row⟩
    let cpu := cpuAirP2 m.hd m.stk m.heap.length Vs.length m.stk JP2 rootP
    let C := Rn.cpuTableP (2 ^ R)
    let Pg := progTableC m.heap N 1
    let Wt := witTableP A N 1
    let Pi := Rn.pinTable (2 ^ R) (2 ^ LI)
    let Po := Rn.poutTable (2 ^ R) (2 ^ LO)
    let Pp := Rn.p2Table (2 ^ R) (2 ^ LP)
    let Mm := memTable5 A cpu (progAirC m.heap N 1) p2inAirB p2outAirB (witAirP N 1) C Pg Pi Po Wt
    (Balanced (compPTables m.hd m.stk m.heap.length Vs.length m.stk JP2 rootP m.heap N 1 segRoots C Mm Pg Wt
        (segsPub segRoots) Pi Po Pp (idxPub nc)) ∧
      UnblindedCP C Mm Wt Pi Po Pp) ∧
    (Sat cpu C ∧ Sat memAirC Mm ∧ Sat (witAirP N 1) Wt ∧ Sat p2inAirB Pi ∧ Sat p2outAirB Po ∧ Sat p2AirB Pp) ∧
    (C.h = 2 ^ R ∧ Mm.h = 2 ^ Lm ∧ Wt.h = 2 ^ 9 ∧ Pi.h = 2 ^ LI ∧ Po.h = 2 ^ LO ∧ Pp.h = 2 ^ LP ∧
      progTpC m.heap N 1 ≤ 23 ∧ Pg.h = 2 ^ (progTpC m.heap N 1 + 1) ∧
      segTp segRoots ≤ 23 ∧ (segsPub segRoots).h = 2 ^ (segTp segRoots + 1)) := by
  intro m segRoots N Rn cpu C Pg Wt Pi Po Pp Mm
  have hRb : 2 ^ R ≤ 1048576 := Nat.pow_le_pow_right (by decide) hR
  have hLb : 2 ^ Lm ≤ 1048576 := Nat.pow_le_pow_right (by decide) hLm
  have hIb : 2 ^ LI ≤ 1048576 := Nat.pow_le_pow_right (by decide) hLI
  have hOb : 2 ^ LO ≤ 1048576 := Nat.pow_le_pow_right (by decide) hLO
  have hPb : 2 ^ LP ≤ 1048576 := Nat.pow_le_pow_right (by decide) hLP
  have hI0 : 0 < 2 ^ LI := Nat.two_pow_pos _
  have hO0 : 0 < 2 ^ LO := Nat.two_pow_pos _
  have hP0 : 0 < 2 ^ LP := Nat.two_pow_pos _
  have hN : BT.nleaves shpP = 496 := shpP_nleaves
  have hl : region.length = (List.replicate 1 Cell.S).length := by rw [List.length_replicate, hrl]
  obtain ⟨hhd, hstk, hroots', hlenm, htake, hpub⟩ :=
    cMachineO_public ρ (fun _ => false) shpP region (List.replicate 1 .S) Vs hl
  have eR : (cHeapO ρ shpP region Vs).2 = blankRootsO shpP 1 Vs := hroots'
  have eN : (cHeapO ρ shpP region Vs).1.length = (blankMO shpP 1 Vs).stk := hstk
  unfold runP at hHI hHO hHP hcalls
  rw [eR] at hHI hHO hHP hcalls
  rw [eR, eN] at hA
  obtain ⟨m0, hm0⟩ : ∃ m, cMachineO ρ shpP region Vs = m := ⟨_, rfl⟩
  rw [hm0] at hA htake hpub hlenm hhd hstk
  have hA' : AcceptsCP Rn.A m0 [] [] Rn.J Rn.root Rn.segRoots (blankMO shpP 1 Vs).stk Rn.n Rn.e Rn.row := hA
  have hn : 0 < Vs.length := hA.npos
  have hnR : (blankRootsO shpP 1 Vs).length = Vs.length := blankRootsO_length _ _ _
  -- the memory holds the machine
  have h0 : A.take m0.heap.length = m0.heap := by rw [← hA.ctr0]; exact hA.heap0
  have hmlen : m0.heap.length ≤ A.length := by
    have := congrArg List.length h0; rw [List.length_take] at this; omega
  have hpre : BT.nleaves shpP + 3 + 1 ≤ m0.heap.length := by
    have := congrArg List.length htake
    simp only [List.length_take, List.length_append, slotHeap_length, hrl] at this
    omega
  have hAm : ∀ i, i < m0.heap.length → A.getD i .nil = m0.heap.getD i .nil := by
    intro i hi
    have := congrArg (fun l => l[i]?) h0
    simp only [List.getElem?_take, if_pos hi] at this
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, this]
  have hslot : ∀ k, k < BT.nleaves shpP + 3 + 1 →
      A.getD k .nil = (slotHeap ρ (BT.nleaves shpP) ++ region).getD k .nil := by
    intro k hk
    rw [hAm k (by omega)]
    have := congrArg (fun l => l[k]?) htake
    simp only [List.getElem?_take, if_pos (show k < BT.nleaves shpP + 3 + region.length by omega)] at this
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, this]
  have hbits : ∀ i, i < BT.nleaves shpP → A.getD (3 + i) .nil = .K ∨ A.getD (3 + i) .nil = .app 0 1 := by
    intro i hi
    rw [hslot (3 + i) (by omega), List.getD_eq_getElem?_getD,
      List.getElem?_append_left (by rw [slotHeap_length]; omega)]
    unfold slotHeap
    rw [List.getElem?_append_right (by simp),
      show 3 + i - ([Cell.K, Cell.I, Cell.app 0 1] : List Cell).length = i by simp, List.getElem?_map,
      List.getElem?_range hi, Option.map_some, Option.getD_some]
    cases ρ i
    · exact .inr rfl
    · exact .inl rfl
  have hreg : ∀ i, i < 1 → cellOK (3 + BT.nleaves shpP + i) (A.getD (3 + BT.nleaves shpP + i) .nil) = true := by
    intro i hi
    rw [hslot _ (by omega), List.getD_eq_getElem?_getD,
      List.getElem?_append_right (by rw [slotHeap_length]; omega), slotHeap_length,
      show 3 + BT.nleaves shpP + i - (BT.nleaves shpP + 3) = i by omega]
    have hri : i < region.length := by omega
    rw [List.getElem?_eq_getElem hri, Option.getD_some]
    have := hr i region[i] (List.getElem?_eq_getElem hri)
    rwa [show BT.nleaves shpP + 3 + i = 3 + BT.nleaves shpP + i by omega] at this
  -- the numbers
  have hPP : P = 2013265921 := rfl
  have hAl : A.length < P := by rw [hlen, hPP]; omega
  have hnK : Vs.length ≤ 2 ^ R := by
    have := emono_ge hA.emono (Vs.length - 1) (by omega); omega
  have hsmall : 3 + BT.nleaves shpP + 1 ≤ 2 ^ 24 := by rw [hN]; decide
  have hlenW : 3 + BT.nleaves shpP + 1 ≤ A.length := by omega
  have hbl : (blankMO shpP 1 Vs).heap.length = m0.heap.length := hlenm.symm
  have hl24 : A.length ≤ 2 ^ 24 := by omega
  have hK' : Rn.e (Rn.n - 1) < 2 ^ R := hK
  have hctr := hA.ctr_le
  have hcpu : Sat cpu C := by
    have := P2Run.cpuP_sat hA' hK' (fun i hi => by
      unfold rowP
      split
      · next h => exact Nat.le_trans (hctr i h) hl24
      · exact Nat.le_trans (hctr _ (Nat.le_refl _)) hl24)
    have eAir : cpuAirP2 (Rn.segRoots.getD 0 0) (blankMO shpP 1 Vs).stk m0.heap.length Rn.n
        (blankMO shpP 1 Vs).stk Rn.J Rn.root = cpu := by
      show cpuAirP2 ((blankRootsO shpP 1 Vs).getD 0 0) _ m0.heap.length Vs.length _ JP2 rootP = _
      rw [← hbl]; rfl
    rw [eAir] at this
    exact this
  have hpubA : ∀ i, i < m.heap.length → ¬ (3 ≤ i ∧ i < 3 + BT.nleaves shpP + 1) →
      i < A.length ∧ A.getD i .nil = m.heap.getD i .nil := by
    intro i hi hp
    have hi' : i < m0.heap.length := by
      have : m.heap.length = m0.heap.length := hbl
      omega
    refine ⟨by omega, ?_⟩
    have hor : i < 3 ∨ BT.nleaves shpP + 3 + region.length ≤ i := by
      rcases Nat.lt_or_ge i 3 with h3 | h3
      · exact .inl h3
      · refine .inr ?_
        have := Nat.le_of_not_lt (fun hlt => hp ⟨h3, hlt⟩)
        omega
    rw [hAm i hi', List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, hpub i hor]
    rfl
  have hz := P2Run.honest_zkP hA' hK' m.hd m.stk m.heap.length JP2 rootP (heap := m.heap) (N := BT.nleaves shpP)
    (W := 1) (HI := 2 ^ LI) (HO := 2 ^ LO) (HP := 2 ^ LP)
    hAl hnR (show Vs.length < P by omega) hHI hHO hHP hI0 hO0 hP0 hpubA hbits (by rw [hN]; exact Nat.le_refl _)
    hreg hlenW
  have hc1 : Rn.calls (2 ^ R) = nc := hcalls
  rw [hc1] at hz
  have hmh : m.heap.length ≤ 2 ^ 24 := by show (blankMO shpP 1 Vs).heap.length ≤ _; omega
  have hsr : segRoots.length ≤ 2 ^ 24 := by
    show (blankRootsO shpP 1 Vs).length ≤ _
    have : 2 ^ R ≤ 2 ^ 24 := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  obtain ⟨p1, p2⟩ := progC_height (heap := m.heap) (N := N) (W := 1) hmh
  obtain ⟨s1, s2⟩ := segsC_height (roots := segRoots) hsr
  refine ⟨hz, ⟨hcpu, memC5_sat A _ _ _ _ _ _ _ _ _ _ (by omega), witP_sat hbits hreg hsmall,
    sat_withBlocks (Rn.pin_sat hI0) Rn.pin_wide, sat_withBlocks (Rn.pout_sat hO0) Rn.pout_wide,
    sat_withBlocks (Rn.p2_sat hP0 hHP) Rn.p2_wide⟩,
    rfl, hlen, (show (witRowsP (BT.nleaves shpP) 1).length = _ by rw [hN]; exact witRowsP_512), rfl, rfl, rfl, p1, p2, s1, s2⟩

end Circuit
