import Ski.ZK.CompPHonest
import Ski.Circuit.CompPSat
import Ski.Circuit.CompPCpuSat
import Ski.Circuit.CompPFinal
import Ski.Circuit.CompJComplete

/-!
# Completeness of the circuit with the Poseidon2 jet

**`compPG_complete_log`**: a run of the circuit with the Poseidon2 jet,
from the open composed machine of literal bits and a well-formed region,
gives tables that AIRs with the normal forms of `compPAirsG Vs` accept, with
Plonky3's selectors, at the heights a statement names.  The program,
segment and level tables are the public ones, the level table's
multiplicities those of the run's jet calls, and the tables decode back to
the memory and the run.  It assembles each table's `Sat`
(`Ski/Circuit/CompPSat.lean`, `Ski/Circuit/CompPCpuSat.lean`) with the
balance (`P2Run.balancedP`).
-/

namespace Circuit

open B Air Compose CompM Mach

set_option maxRecDepth 100000 in
/-- **The public level table satisfies its AIR**, which has no constraints. -/
theorem idx_sat (n : Nat) : Sat p2idxAir (idxPub n) :=
  ⟨show 0 < idxRows.length by decide, fun _ hc => nomatch hc⟩

set_option maxRecDepth 100000 in
theorem idx_pre (n : Nat) : PreIs p2idxAir (idxPub n) := ⟨rfl, fun _ _ _ _ => rfl⟩

theorem witRowsP_le {N W : Nat} (h : N + W ≤ 2 ^ 24) : (witRowsP N W).length ≤ 2 ^ 24 := by
  have hp := pow2From_le (n := N + W) h 64 9 (by decide)
  unfold witRowsP pow2Min
  simp only [List.length_append, List.length_map, List.length_range, List.length_replicate]
  omega

theorem witRowsP_512 : (witRowsP 496 1).length = 2 ^ 9 := by
  unfold witRowsP
  simp only [List.length_append, List.length_map, List.length_range, List.length_replicate]
  rfl

-- ---------------------------------------------------------------------------
-- The run's registers lie in memory
-- ---------------------------------------------------------------------------

section

variable {M : List Cell} {m0 : Mach} {J root : Nat} {roots : List Nat} {nilA n : Nat} {e : Nat → Nat}
  {row : Nat → Air.Row} (hA : AcceptsCP M m0 [] [] J root roots nilA n e row)
include hA

/-- **Every counter of a run with the Poseidon2 jet is within the memory.** -/
theorem _root_.CompM.AcceptsCP.ctr_le : ∀ i, i ≤ e (n - 1) → (row i).ctr ≤ M.length := by
  intro i hi
  have hn := hA.npos
  have hro : Air.RootsOK m0.heap [] [] := fun _ _ h => absurd h List.not_mem_nil
  obtain ⟨j, hj, h1, h2⟩ := seg_cover (e := e) (n := n) (n - 1) (by omega) i hi
  obtain ⟨hc, hm, _, _⟩ := hA.runs hro j (by omega)
  have hc0 : (row 0).ctr ≤ (row (segStart e j)).ctr := by rw [hA.ctr0]; exact hm
  exact (hA.within_ctr hro (by omega) hc hc0 i h1 h2).1

/-- **Every stack pointer of a run with the Poseidon2 jet is in memory.** -/
theorem _root_.CompM.AcceptsCP.stk_le (hfit : Fits M) (hnil : nilA ≤ M.length) :
    ∀ i, i ≤ e (n - 1) → (row i).stk ≤ M.length := by
  have hc := hA.ctr_le
  intro i
  induction i with
  | zero => intro _; rw [hA.stk0]; exact hnil
  | succ i ih =>
    intro hi
    cases hr : isRestart e n i with
    | true =>
      obtain ⟨j, hj, rfl⟩ := isRestart_iff.1 hr
      rw [hA.restart j hj]; exact hnil
    | false =>
      rcases hA.trans i (by omega) (AcceptsCJ.notEnd hr) with (h | ⟨_, _, hm, _, _⟩ | h) | h
      · exact step_stk hfit h (hc i (by omega)) (hc (i + 1) hi)
      · exact absurd hm List.not_mem_nil
      · rw [h.2]; exact ih (by omega)
      · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hr'⟩ := p2Row_inv h
        have hc' := hc (i + 1) hi
        rw [hr'] at hc' ⊢
        exact Nat.le_trans (Nat.le_succ _) hc'

end

-- ---------------------------------------------------------------------------
-- Completeness
-- ---------------------------------------------------------------------------

open ComposedPText in
/-- The run of `compPG_complete_log`, over the open composed machine of `ρ`
    and `region`. -/
def runP (ρ : Nat → Bool) (region : List Cell) (Vs : List OTerm) (A : List Cell) (e : Nat → Nat)
    (row : Nat → Air.Row) : P2Run :=
  ⟨A, JP2, rootP, (cHeapO ρ shpP region Vs).2, e, Vs.length, row⟩

set_option maxRecDepth 100000 in
open Stmt Wit ComposedPText in
/-- **Completeness of the circuit with the Poseidon2 jet**, for any
    verifiers `Vs`, at the heights a statement names: a run with the jet from
    the open composed machine of literal bits and a well-formed one-cell
    region, over a memory of `2^Lm` cells whose cells point into it, ending
    within `2^R` rows, its jet calls' P2IN, P2OUT and Poseidon2 rows within
    `2^LI`, `2^LO` and `2^LP` rows, all five logarithms at most `20`, gives
    tables that AIRs with the normal forms of `compPAirsG Vs` accept, with
    Plonky3's selectors.  The private tables are the honest ones, those
    `P2Run.honest_zkP` shows balanced with clear flags; the program and
    segment tables are the public ones, the level table is `idxPub` of the
    run's jet calls, and the tables decode back to the memory and the run. -/
theorem compPG_complete_log {R Lm LI LO LP : Nat} (hR : R ≤ 20) (hLm : Lm ≤ 20) (hLI : LI ≤ 20)
    (hLO : LO ≤ 20) (hLP : LP ≤ 20) {Vs : List OTerm} {Rs : List AirD}
    (hs : sameAirsB Rs (compPAirsG Vs) = true)
    {ρ : Nat → Bool} {region : List Cell} (hrl : region.length = 1)
    (hr : ∀ i c, region[i]? = some c → cellOK (BT.nleaves shpP + 3 + i) c = true)
    {A : List Cell} {e : Nat → Nat} {row : Nat → Air.Row}
    (hA : AcceptsCP A (cMachineO ρ shpP region Vs) [] [] JP2 rootP (cHeapO ρ shpP region Vs).2
      (cHeapO ρ shpP region Vs).1.length Vs.length e row)
    (hfit : Fits A) (hlen : A.length = 2 ^ Lm) (hK : e (Vs.length - 1) < 2 ^ R)
    (hHI : ((runP ρ region Vs A e row).pinRows (2 ^ R)).length ≤
      2 ^ LI)
    (hHO : ((runP ρ region Vs A e row).poutRows (2 ^ R)).length ≤
      2 ^ LO)
    (hHP : ((runP ρ region Vs A e row).p2Rows (2 ^ R)).length ≤
      2 ^ LP) :
    ∃ C Mm Pg Wt Sg Pi Po Pp Px, AcceptedP Rs [C, Mm, Pg, Wt, Sg, Pi, Po, Pp, Px] ∧
      C = (runP ρ region Vs A e row).cpuTableP (2 ^ R) ∧
      Mm = memTable5 A (cpuAirP2 (blankMO shpP 1 Vs).hd (blankMO shpP 1 Vs).stk
        (blankMO shpP 1 Vs).heap.length (blankRootsO shpP 1 Vs).length (blankMO shpP 1 Vs).stk JP2 rootP)
        (progAirC (blankMO shpP 1 Vs).heap (BT.nleaves shpP) 1) p2inAirB p2outAirB
        (witAirP (BT.nleaves shpP) 1) C Pg Pi Po Wt ∧
      Wt = witTableP A (BT.nleaves shpP) 1 ∧
      Pi = (runP ρ region Vs A e row).pinTable (2 ^ R) (2 ^ LI) ∧
      Po = (runP ρ region Vs A e row).poutTable (2 ^ R) (2 ^ LO) ∧
      Pp = (runP ρ region Vs A e row).p2Table (2 ^ R) (2 ^ LP) ∧
      Pg = progTableC (blankMO shpP 1 Vs).heap (BT.nleaves shpP) 1 ∧ Sg = segsPub (blankRootsO shpP 1 Vs) ∧
      Px = idxPub ((runP ρ region Vs A e row).calls (2 ^ R)) ∧
      C.h = 2 ^ R ∧ Mm.h = 2 ^ Lm ∧ Wt.h = 2 ^ 9 ∧ Pi.h = 2 ^ LI ∧ Po.h = 2 ^ LO ∧ Pp.h = 2 ^ LP ∧
      memOf Mm = A ∧ ∀ i, i ≤ e (Vs.length - 1) → rowOf C i = row i := by
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
  -- the run, named
  let Rn : P2Run := ⟨A, JP2, rootP, blankRootsO shpP 1 Vs, e, Vs.length, row⟩
  unfold runP at hHI hHO hHP ⊢
  rw [eR] at hHI hHO hHP ⊢
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
  -- the tables
  let cpu := cpuAirP2 (blankMO shpP 1 Vs).hd (blankMO shpP 1 Vs).stk (blankMO shpP 1 Vs).heap.length
    (blankRootsO shpP 1 Vs).length (blankMO shpP 1 Vs).stk JP2 rootP
  let heap := (blankMO shpP 1 Vs).heap
  let C := Rn.cpuTableP (2 ^ R)
  let Pg := progTableC heap (BT.nleaves shpP) 1
  let Wt := witTableP A (BT.nleaves shpP) 1
  let Pi := Rn.pinTable (2 ^ R) (2 ^ LI)
  let Po := Rn.poutTable (2 ^ R) (2 ^ LO)
  let Pp := Rn.p2Table (2 ^ R) (2 ^ LP)
  let Px := idxPub (Rn.calls (2 ^ R))
  let Mm := memTable5 A cpu (progAirC heap (BT.nleaves shpP) 1) p2inAirB p2outAirB (witAirP (BT.nleaves shpP) 1)
    C Pg Pi Po Wt
  let Sg := segsPub (blankRootsO shpP 1 Vs)
  have hcpu : Sat cpu C := by
    have := P2Run.cpuP_sat hA' hK' (fun i hi => by
      unfold rowP
      split
      · next h => exact Nat.le_trans (hctr i h) hl24
      · exact Nat.le_trans (hctr _ (Nat.le_refl _)) hl24)
    have eAir : cpuAirP2 (Rn.segRoots.getD 0 0) (blankMO shpP 1 Vs).stk m0.heap.length Rn.n
        (blankMO shpP 1 Vs).stk Rn.J Rn.root = cpu := by
      show cpuAirP2 ((blankRootsO shpP 1 Vs).getD 0 0) _ m0.heap.length Vs.length _ JP2 rootP = _
      rw [← hbl, ← hnR]; rfl
    rw [eAir] at this
    exact this
  have hpubA : ∀ i, i < heap.length → ¬ (3 ≤ i ∧ i < 3 + BT.nleaves shpP + 1) →
      i < A.length ∧ A.getD i .nil = heap.getD i .nil := by
    intro i hi hp
    have hi' : i < m0.heap.length := by
      have : heap.length = m0.heap.length := hbl
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
  have hbal : Balanced (compPTables (blankMO shpP 1 Vs).hd (blankMO shpP 1 Vs).stk
      (blankMO shpP 1 Vs).heap.length (blankRootsO shpP 1 Vs).length (blankMO shpP 1 Vs).stk JP2 rootP heap
      (BT.nleaves shpP) 1 (blankRootsO shpP 1 Vs) C Mm Pg Wt Sg Pi Po Pp Px) := by
    have := P2Run.balancedP hA' hK' (blankMO shpP 1 Vs).hd (blankMO shpP 1 Vs).stk
      (blankMO shpP 1 Vs).heap.length JP2 rootP (heap := heap) (N := BT.nleaves shpP) (W := 1)
      hAl hnR (show Vs.length < P by omega) hHI hHO hHP hpubA hbits (by rw [hN]; exact Nat.le_refl _) hreg hlenW
    rw [show Rn.n = (blankRootsO shpP 1 Vs).length from hnR.symm] at this
    exact this
  have hacc : Accepted (compPAirsG Vs) [C, Mm, Pg, Wt, Sg, Pi, Po, Pp, Px] := by
    have z : (compPAirsG Vs).zip [C, Mm, Pg, Wt, Sg, Pi, Po, Pp, Px] =
        compPTables (blankMO shpP 1 Vs).hd (blankMO shpP 1 Vs).stk
          (blankMO shpP 1 Vs).heap.length (blankRootsO shpP 1 Vs).length
          (blankMO shpP 1 Vs).stk JP2 rootP heap (BT.nleaves shpP) 1
          (blankRootsO shpP 1 Vs) C Mm Pg Wt Sg Pi Po Pp Px := rfl
    have hPg : Pg.h ≤ 2 ^ 24 := progRowsC_le (by have : heap.length = m0.heap.length := hbl; omega)
    have hSg : Sg.h ≤ 2 ^ 24 := segRows_le (by rw [hnR]; omega)
    have hWt : Wt.h = 2 ^ 9 := by show (witRowsP _ 1).length = _; rw [hN]; exact witRowsP_512
    refine ⟨rfl, ?_, ?_, ?_, ?_⟩
    · rw [z]
      intro p hp
      simp only [compPTables, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact ⟨hcpu, .inl rfl⟩
      · exact ⟨memC5_sat A _ _ _ _ _ _ _ _ _ _ (by omega), .inl rfl⟩
      · exact ⟨(progC_sat _ _ _).1, .inr (progC_sat _ _ _).2⟩
      · exact ⟨witP_sat hbits hreg hsmall, .inr ⟨rfl, fun _ _ _ _ => rfl⟩⟩
      · exact ⟨⟨segRows_pos _, fun c hc => nomatch hc⟩, .inr ⟨rfl, fun _ _ _ _ => rfl⟩⟩
      · exact ⟨sat_withBlocks (Rn.pin_sat hI0) Rn.pin_wide, .inl rfl⟩
      · exact ⟨sat_withBlocks (Rn.pout_sat hO0) Rn.pout_wide, .inl rfl⟩
      · exact ⟨sat_withBlocks (Rn.p2_sat hP0 hHP) Rn.p2_wide, .inl rfl⟩
      · exact ⟨idx_sat _, .inr (idx_pre _)⟩
    · rw [z]; exact hbal
    · rw [z]
      unfold HeightsOK compPTables
      simp only [List.foldr_cons, List.foldr_nil]
      have hC : C.h = 2 ^ R := rfl
      have hMm : Mm.h = 2 ^ Lm := hlen
      have hPi : Pi.h = 2 ^ LI := rfl
      have hPo : Po.h = 2 ^ LO := rfl
      have hPp : Pp.h = 2 ^ LP := rfl
      have hPx : Px.h = 512 := idxPub_h _
      show 19 * C.h + (1 * Mm.h + (1 * Pg.h + (2 * Wt.h + (0 * Sg.h + (7 * Pi.h + (7 * Po.h + (33 * Pp.h +
        (0 * Px.h + 0)))))))) < P
      omega
    · rw [z]
      intro p hp
      simp only [compPTables, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · show 2 ^ R ≤ 2 ^ 27; exact Nat.pow_le_pow_right (by decide) (by omega)
      · show A.length ≤ 2 ^ 27; omega
      · show Pg.h ≤ 2 ^ 27; omega
      · show Wt.h ≤ 2 ^ 27; rw [hWt]; decide
      · show Sg.h ≤ 2 ^ 27; omega
      · show 2 ^ LI ≤ 2 ^ 27; exact Nat.pow_le_pow_right (by decide) (by omega)
      · show 2 ^ LO ≤ 2 ^ 27; exact Nat.pow_le_pow_right (by decide) (by omega)
      · show 2 ^ LP ≤ 2 ^ 27; exact Nat.pow_le_pow_right (by decide) (by omega)
      · show Px.h ≤ 2 ^ 27; rw [idxPub_h]; decide
  have hRs : AcceptedP Rs [C, Mm, Pg, Wt, Sg, Pi, Po, Pp, Px] :=
    (acceptedP_iff_of (compPG_guarded Vs) hs _).2 (accepted_transfer (sameAirsB_symm hs) hacc)
  refine ⟨C, Mm, Pg, Wt, Sg, Pi, Po, Pp, Px, hRs, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hlen,
    (show (witRowsP _ 1).length = _ by rw [hN]; exact witRowsP_512), rfl, rfl, rfl, ?_, ?_⟩
  · -- the memory decodes back
    apply List.ext_getElem?
    intro m
    unfold memOf
    rw [List.getElem?_map]
    rcases Nat.lt_or_ge m Mm.h with hm | hm
    · rw [List.getElem?_range hm, Option.map_some]
      have hm' : m < A.length := hm
      have hg : A.getD m .nil = A[m] := by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hm']; rfl
      have hf := hfit _ (List.getElem_mem hm')
      show some (cellOf (ofN (cellTag (A.getD m .nil))) (ofN (cellFields (A.getD m .nil)).1)
        (ofN (cellFields (A.getD m .nil)).2)) = _
      rw [hg, cellOf_enc _ (by omega) (by omega), List.getElem?_eq_getElem hm']
    · rw [List.getElem?_eq_none (by rw [List.length_range]; exact hm), List.getElem?_eq_none hm]; rfl
  · -- the rows decode back
    intro i hi
    have hiK : i < 2 ^ R := by omega
    have hnil : (blankMO shpP 1 Vs).stk ≤ A.length := by
      show (cHeapO _ _ _ _).1.length ≤ _
      have : (cHeapO (fun _ => false) shpP (List.replicate 1 .S) Vs).1.length + 1 =
          (blankMO shpP 1 Vs).heap.length := by
        show _ = ((cHeapO _ _ _ _).1 ++ [Cell.nil]).length; simp
      omega
    have hc := hctr i hi
    have hst := hA.stk_le hfit hnil i hi
    have hS := shape ((P2Run.runC hA' hK').valid i hiK)
    obtain ⟨cell, hrd, _⟩ := hS.reads 0 (by decide) rfl
    have hh := (rd_get hrd).1
    have hq : Rn.rowQ i = row i := P2Run.rowQ_of_le (R := Rn) hi
    have e1 : rowP row e Vs.length i = row i := hq
    rw [e1] at hh
    show (⟨(Rn.cpuColP i HD).val, (Rn.cpuColP i STK).val, (Rn.cpuColP i CTR).val⟩ : Air.Row) = row i
    rw [Rn.colP_hd, Rn.colP_stk, Rn.colP_ctr, hq]
    rw [val_ofN (by show (row i).hd < P; have : (row i).hd < (row i).ctr := hh; omega),
      val_ofN (by omega), val_ofN (by omega)]

set_option maxRecDepth 100000 in
/-- **One verifier in the frame calls the jet once**, so the level table of
    `compPG_complete_log` is the published `idxPub 1`. -/
theorem runP_calls_one {ρ : Nat → Bool} {region : List Cell} {V : OTerm} {G U : OTerm → Prop}
    (hp : P2Once.Part ComposedPText.JP2 G U) {g : OTerm} (hg : G g) (hV : V = .S ⬝ₒ (.K ⬝ₒ .K) ⬝ₒ g)
    (hrl : region.length = 1)
    (hr : ∀ i c, region[i]? = some c → Wit.cellOK (BT.nleaves ComposedPText.shpP + 3 + i) c = true)
    {A : List Cell} {e : Nat → Nat} {row : Nat → Air.Row}
    (hA : AcceptsCP A (cMachineO ρ ComposedPText.shpP region [V]) [] [] ComposedPText.JP2 ComposedPText.rootP
      (cHeapO ρ ComposedPText.shpP region [V]).2 (cHeapO ρ ComposedPText.shpP region [V]).1.length 1 e row)
    {K : Nat} (hK : e 0 < K) :
    (runP ρ region [V] A e row).calls K = 1 := by
  obtain ⟨hb0, ho0⟩ := comb_heap ρ region [V]
  have hroot : ComposedPText.rootP = combRoot ρ (combBT 496) region :=
    combRoot_public (fun _ => false) ρ ComposedPText.shpP (by rw [hrl]; rfl)
  rw [← hroot] at ho0
  exact P2Run.calls_one (R := runP ρ region [V] A e row) hp hg hV hb0 ho0 hr rfl rfl hA hK

set_option maxRecDepth 100000 in
open Stmt Wit ComposedPText in
/-- **Completeness of the circuit for `p2pre h`**: `compPG_complete_log`
    for its verifier, the level table the published `idxPub 1`. -/
theorem compP_complete_log {h R Lm LI LO LP : Nat} (hR : R ≤ 20) (hLm : Lm ≤ 20) (hLI : LI ≤ 20)
    (hLO : LO ≤ 20) (hLP : LP ≤ 20) {Rs : List AirD}
    (hs : sameAirsB Rs (compPAirs h) = true)
    {ρ : Nat → Bool} {region : List Cell} (hrl : region.length = 1)
    (hr : ∀ i c, region[i]? = some c → cellOK (BT.nleaves shpP + 3 + i) c = true)
    {A : List Cell} {e : Nat → Nat} {row : Nat → Air.Row}
    (hA : AcceptsCP A (cMachineO ρ shpP region (VsP h)) [] [] JP2 rootP (cHeapO ρ shpP region (VsP h)).2
      (cHeapO ρ shpP region (VsP h)).1.length (VsP h).length e row)
    (hfit : Fits A) (hlen : A.length = 2 ^ Lm) (hK : e 0 < 2 ^ R)
    (hHI : ((runP ρ region (VsP h) A e row).pinRows (2 ^ R)).length ≤ 2 ^ LI)
    (hHO : ((runP ρ region (VsP h) A e row).poutRows (2 ^ R)).length ≤ 2 ^ LO)
    (hHP : ((runP ρ region (VsP h) A e row).p2Rows (2 ^ R)).length ≤ 2 ^ LP) :
    ∃ C Mm Pg Wt Sg Pi Po Pp, AcceptedP Rs [C, Mm, Pg, Wt, Sg, Pi, Po, Pp, idxPub 1] ∧
      C = (runP ρ region (VsP h) A e row).cpuTableP (2 ^ R) ∧
      Wt = witTableP A (BT.nleaves shpP) 1 ∧
      Pi = (runP ρ region (VsP h) A e row).pinTable (2 ^ R) (2 ^ LI) ∧
      Po = (runP ρ region (VsP h) A e row).poutTable (2 ^ R) (2 ^ LO) ∧
      Pp = (runP ρ region (VsP h) A e row).p2Table (2 ^ R) (2 ^ LP) ∧
      Pg = progTableC (blankMO shpP 1 (VsP h)).heap (BT.nleaves shpP) 1 ∧
      Sg = segsPub (blankRootsO shpP 1 (VsP h)) ∧
      C.h = 2 ^ R ∧ Mm.h = 2 ^ Lm ∧ memOf Mm = A ∧ ∀ i, i ≤ e 0 → rowOf C i = row i := by
  obtain ⟨C, Mm, Pg, Wt, Sg, Pi, Po, Pp, Px, hacc, hC, _, hWt, hPi, hPo, hPp, hPg, hSg, hPx, hCh, hMh, _, _, _, _,
    hmem, hrow⟩ := compPG_complete_log hR hLm hLI hLO hLP hs hrl hr hA hfit hlen hK hHI hHO hHP
  have hV : verifierO h = .S ⬝ₒ (.K ⬝ₒ .K) ⬝ₒ (.var JP2 ⬝ₒ checkO h) := P2Once.verifierO_eq h
  have h1 := runP_calls_one (G := P2Once.GP JP2) (U := P2Once.UP JP2) (P2Once.partP JP2)
    ⟨checkO h, P2Once.checkO_free h JP2, rfl⟩ hV hrl hr hA hK
  rw [hPx, show (runP ρ region (VsP h) A e row).calls (2 ^ R) = 1 from h1] at hacc
  exact ⟨C, Mm, Pg, Wt, Sg, Pi, Po, Pp, hacc, hC, hWt, hPi, hPo, hPp, hPg, hSg, hCh, hMh, hmem, hrow⟩

set_option maxRecDepth 100000 in
open Stmt Wit ComposedPText in
/-- **Completeness of the circuit for `p2commit c pat`**: `compPG_complete_log`
    for its verifier, the level table the published `idxPub 1`. -/
theorem compPC_complete_log {c : List Nat} {pat : List (Option Bool)} {R Lm LI LO LP : Nat} (hR : R ≤ 20)
    (hLm : Lm ≤ 20) (hLI : LI ≤ 20) (hLO : LO ≤ 20) (hLP : LP ≤ 20) {Rs : List AirD}
    (hs : sameAirsB Rs (compPAirsG [verifierC c pat]) = true)
    {ρ : Nat → Bool} {region : List Cell} (hrl : region.length = 1)
    (hr : ∀ i c, region[i]? = some c → cellOK (BT.nleaves shpP + 3 + i) c = true)
    {A : List Cell} {e : Nat → Nat} {row : Nat → Air.Row}
    (hA : AcceptsCP A (cMachineO ρ shpP region [verifierC c pat]) [] [] JP2 rootP
      (cHeapO ρ shpP region [verifierC c pat]).2 (cHeapO ρ shpP region [verifierC c pat]).1.length 1 e row)
    (hfit : Fits A) (hlen : A.length = 2 ^ Lm) (hK : e 0 < 2 ^ R)
    (hHI : ((runP ρ region [verifierC c pat] A e row).pinRows (2 ^ R)).length ≤ 2 ^ LI)
    (hHO : ((runP ρ region [verifierC c pat] A e row).poutRows (2 ^ R)).length ≤ 2 ^ LO)
    (hHP : ((runP ρ region [verifierC c pat] A e row).p2Rows (2 ^ R)).length ≤ 2 ^ LP) :
    ∃ C Mm Pg Wt Sg Pi Po Pp, AcceptedP Rs [C, Mm, Pg, Wt, Sg, Pi, Po, Pp, idxPub 1] ∧
      C = (runP ρ region [verifierC c pat] A e row).cpuTableP (2 ^ R) ∧
      Wt = witTableP A (BT.nleaves shpP) 1 ∧
      Pi = (runP ρ region [verifierC c pat] A e row).pinTable (2 ^ R) (2 ^ LI) ∧
      Po = (runP ρ region [verifierC c pat] A e row).poutTable (2 ^ R) (2 ^ LO) ∧
      Pp = (runP ρ region [verifierC c pat] A e row).p2Table (2 ^ R) (2 ^ LP) ∧
      Pg = progTableC (blankMO shpP 1 [verifierC c pat]).heap (BT.nleaves shpP) 1 ∧
      Sg = segsPub (blankRootsO shpP 1 [verifierC c pat]) ∧
      C.h = 2 ^ R ∧ Mm.h = 2 ^ Lm ∧ memOf Mm = A ∧ ∀ i, i ≤ e 0 → rowOf C i = row i := by
  obtain ⟨C, Mm, Pg, Wt, Sg, Pi, Po, Pp, Px, hacc, hC, _, hWt, hPi, hPo, hPp, hPg, hSg, hPx, hCh, hMh, _, _, _, _,
    hmem, hrow⟩ := compPG_complete_log hR hLm hLI hLO hLP hs hrl hr hA hfit hlen hK hHI hHO hHP
  have hV : verifierC c pat = .S ⬝ₒ (.K ⬝ₒ .K) ⬝ₒ (.S ⬝ₒ (.var JP2 ⬝ₒ checkC c) ⬝ₒ patO pat) :=
    P2Once.verifierC_eq c pat
  have h1 := runP_calls_one (G := P2Once.GC JP2) (U := P2Once.UC JP2) (P2Once.partC JP2)
    ⟨checkC c, patO pat, P2Commit.checkC_closed c JP2, P2Commit.patO_closed JP2 pat, rfl⟩ hV hrl hr hA hK
  rw [hPx, show (runP ρ region [verifierC c pat] A e row).calls (2 ^ R) = 1 from h1] at hacc
  exact ⟨C, Mm, Pg, Wt, Sg, Pi, Po, Pp, hacc, hC, hWt, hPi, hPo, hPp, hPg, hSg, hCh, hMh, hmem, hrow⟩

end Circuit
