import Ski.ZK.CompJ

/-!
# The honest prover's tables meet the transcript theorems' hypotheses

The transcript theorems (`comp_transcript`, `sud_transcript`,
`wit_transcript`, and their `G` forms in `Reject.lean`) take two
hypotheses of the prover's tables before it blinds them: they balance with
the public tables (`Balanced`), and their blinding flags are clear
(`Unblinded`).  The circuits with jets discharge them for the honest
prover (`CRun.honest_zk`, `honest_zkP`); this file does so for the
composed, Sudoku and hidden-term circuits.  The tables are the ones each
completeness theorem's proof builds (`comp_completeG_log`, `sud_complete`,
`wit_complete`), from a subset of its hypotheses: the honest prover's.
The completeness statements keep the tables existential, so the link is
by construction, not a theorem.
-/

namespace Circuit

open ZKF B Air Compose CompM Stmt Mach Wit

/-- **The composed circuit's honest tables meet `comp_transcript`'s
    hypotheses**: from a run `comp_completeG_log` accepts, its CPU,
    memory and witness tables balance with the public program and segment
    tables, and their blinding flags are clear. -/
theorem comp_honest_zk {R Lm : Nat} (hR : R ≤ 20) {shp : BT} {Ps : List Term} {W : Nat}
    {ρ : Nat → Bool} {region : List Cell} (hrl : region.length = W)
    (hr : ∀ i c, region[i]? = some c → cellOK (BT.nleaves shp + 3 + i) c = true)
    {A : List Cell} {e : Nat → Nat} {row : Nat → Air.Row}
    (hA : AcceptsC A (cMachine ρ shp region Ps) (cHeap ρ shp region Ps).2
      (cHeap ρ shp region Ps).1.length Ps.length e row)
    (hlen : A.length = 2 ^ Lm) (hLm : Lm ≤ 20) (hK : e (Ps.length - 1) < 2 ^ R)
    (hNW : BT.nleaves shp + W ≤ 2 ^ 8) :
    let m := blankM shp W Ps
    let roots := blankRoots shp W Ps
    let N := BT.nleaves shp
    let C := cpuTableC A row e Ps.length roots (2 ^ R)
    let Pg := progTableC m.heap N W
    let Wt := witTable A N W
    let Mm := memTableC A (cpuAirC m.hd m.stk m.heap.length roots.length m.stk) (progAirC m.heap N W)
      (witAir N W) C Pg Wt
    Balanced (compTables m.hd m.stk m.heap.length roots.length m.stk m.heap N W roots C Mm Pg Wt
      (segsPub roots)) ∧
    Unblinded WT_BLIND C Mm Wt := by
  intro m roots N C Pg Wt Mm
  have hl : region.length = (List.replicate W Cell.S).length := by rw [List.length_replicate, hrl]
  obtain ⟨_, hstk, hroots, hlenm, htake, hpub⟩ :=
    cMachine_public ρ (fun _ => false) shp region (List.replicate W .S) Ps hl
  have eR : (cHeap ρ shp region Ps).2 = blankRoots shp W Ps := hroots
  have eN : (cHeap ρ shp region Ps).1.length = (blankM shp W Ps).stk := hstk
  rw [eR, eN] at hA
  obtain ⟨m0, hm0⟩ : ∃ m, cMachine ρ shp region Ps = m := ⟨_, rfl⟩
  rw [hm0] at hA htake hpub hlenm
  have hnR : (blankRoots shp W Ps).length = Ps.length := blankRoots_length _ _ _
  -- the memory holds the machine
  have h0 : A.take m0.heap.length = m0.heap := by rw [← hA.ctr0]; exact hA.heap0
  have hmlen : m0.heap.length ≤ A.length := by
    have := congrArg List.length h0; rw [List.length_take] at this; omega
  have hpre : BT.nleaves shp + 3 + W ≤ m0.heap.length := by
    have := congrArg List.length htake
    simp only [List.length_take, List.length_append, slotHeap_length, hrl] at this
    omega
  have hAm : ∀ i, i < m0.heap.length → A.getD i .nil = m0.heap.getD i .nil := by
    intro i hi
    have := congrArg (fun l => l[i]?) h0
    simp only [List.getElem?_take, if_pos hi] at this
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, this]
  have hslot : ∀ k, k < BT.nleaves shp + 3 + W →
      A.getD k .nil = (slotHeap ρ (BT.nleaves shp) ++ region).getD k .nil := by
    intro k hk
    rw [hAm k (by omega)]
    have := congrArg (fun l => l[k]?) htake
    simp only [List.getElem?_take, if_pos (show k < BT.nleaves shp + 3 + region.length by omega)] at this
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, this]
  have hbits : ∀ i, i < BT.nleaves shp → A.getD (3 + i) .nil = .K ∨ A.getD (3 + i) .nil = .app 0 1 := by
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
  have hreg : ∀ i, i < W → cellOK (3 + BT.nleaves shp + i) (A.getD (3 + BT.nleaves shp + i) .nil) = true := by
    intro i hi
    rw [hslot _ (by omega), List.getD_eq_getElem?_getD,
      List.getElem?_append_right (by rw [slotHeap_length]; omega), slotHeap_length,
      show 3 + BT.nleaves shp + i - (BT.nleaves shp + 3) = i by omega]
    have hri : i < region.length := by omega
    rw [List.getElem?_eq_getElem hri, Option.getD_some]
    have := hr i region[i] (List.getElem?_eq_getElem hri)
    rwa [show BT.nleaves shp + 3 + i = 3 + BT.nleaves shp + i by omega] at this
  -- the numbers
  have hPP : P = 2013265921 := rfl
  have hLb : 2 ^ Lm ≤ 1048576 := Nat.pow_le_pow_right (by decide) hLm
  have hRb : 2 ^ R ≤ 1048576 := Nat.pow_le_pow_right (by decide) hR
  have hAl : A.length < P := by rw [hlen, hPP]; omega
  have hn : 0 < Ps.length := hA.npos
  have hnK : Ps.length ≤ 2 ^ R := by
    have := emono_ge hA.emono (Ps.length - 1) (by omega); omega
  have hRlt : (blankRoots shp W Ps).length < P := by rw [hnR]; omega
  have hlenW : 3 + BT.nleaves shp + W ≤ A.length := by omega
  have hbl : (blankM shp W Ps).heap.length = m0.heap.length := hlenm.symm
  have hpubA : ∀ i, i < (blankM shp W Ps).heap.length →
      ¬ (3 ≤ i ∧ i < 3 + BT.nleaves shp + W) →
      i < A.length ∧ A.getD i .nil = (blankM shp W Ps).heap.getD i .nil := by
    intro i hi hp
    have hi' : i < m0.heap.length := by omega
    refine ⟨by omega, ?_⟩
    have hor : i < 3 ∨ BT.nleaves shp + 3 + region.length ≤ i := by
      rcases Nat.lt_or_ge i 3 with h3 | h3
      · exact .inl h3
      · refine .inr ?_
        have := Nat.le_of_not_lt (fun hlt => hp ⟨h3, hlt⟩)
        omega
    rw [hAm i hi', List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, hpub i hor]
    rfl
  refine ⟨?_, ?_⟩
  · rw [← segs_honest (hA.runC hK) m.hd m.stk m.heap.length roots.length m.stk hnR (by rw [← hnR]; exact hRlt)]
    exact balancedC hAl hRlt (by rw [hnR]; exact hn) (cpuC_honest (hA.runC hK)) (cpuC_segsHonest (hA.runC hK) hnR)
      (cpuC_blindZero (hA.runC hK)) (progC_honest hpubA) (witT_honest (a0 := 3) (fun _ => by decide) hbits hreg hlenW)
      witT_blindZero
  · exact {
      hw := by show 0 < (witRows N W).length; rw [witRows_len hNW]; exact Nat.two_pow_pos 9
      hc := Nat.two_pow_pos R
      hm := by show 0 < A.length; rw [hlen]; exact Nat.two_pow_pos Lm
      zw := fun r _ => witT_flag r
      za := fun r _ => cpuColC_blind (A := A) (row := row) (e := e) (n := Ps.length) (roots := roots) r (.inl rfl)
      zb := fun r _ => cpuColC_blind (A := A) (row := row) (e := e) (n := Ps.length) (roots := roots) r (.inr rfl)
      zm := fun _ _ => rfl }

section
open Sudoku SudokuText

/-- **The Sudoku circuit's honest tables meet `sud_transcript`'s
    hypotheses**: from a run `sud_complete` accepts, its CPU, memory and
    witness tables balance with the public program table, and their
    blinding flags are clear. -/
theorem sud_honest_zk {puzzle : List Nat} (hc : CluesOK (cluesOf puzzle)) {ρ : Nat → Bool}
    {A : List Cell} {k : Nat} {row : Nat → Air.Row}
    (hA : AcceptsFrom A (stmtMachine ρ 729 (sudokuExpr (cluesOf puzzle)) ACC REJ) k row)
    (hlen : A.length = 2 ^ 16) (hk : k ≤ 2 ^ 16) :
    let blank := stmtMachine (fun _ => false) 729 (sudokuExpr (cluesOf puzzle)) ACC REJ
    let C := cpuTableW A row k (2 ^ 16)
    let Pg := progTableS blank.heap
    let Wt := witTableS A
    let Mm := memTableC A (cpuAirS blank.hd blank.stk blank.heap.length ACC) (progAirS blank.heap) witAirS C Pg Wt
    Balanced (sudTables blank.hd blank.stk blank.heap.length blank.heap C Mm Pg Wt) ∧ Unblinded 1 C Mm Wt := by
  intro blank C Pg Wt Mm
  have hb := bounded_sudoku hc
  obtain ⟨_, _, hlenm, hpub⟩ :=
    stmtMachine_public ρ (fun _ => false) 729 (sudokuExpr (cluesOf puzzle)) ACC REJ
  have htk := stmt_take ρ 729 (sudokuExpr (cluesOf puzzle)) ACC REJ
  obtain ⟨_, _, _, b732⟩ := stmt_fitsB (ρ := ρ) hb
  obtain ⟨m0, hm0⟩ : ∃ m, stmtMachine ρ 729 (sudokuExpr (cluesOf puzzle)) ACC REJ = m := ⟨_, rfl⟩
  rw [hm0] at hA hlenm hpub htk b732
  have h0 : A.take m0.heap.length = m0.heap := by rw [← hA.ctr0]; exact hA.heap0
  have hmlen : m0.heap.length ≤ A.length := by
    have := congrArg List.length h0; rw [List.length_take] at this; omega
  have hAm : ∀ i, i < m0.heap.length → A.getD i .nil = m0.heap.getD i .nil := by
    intro i hi
    have := congrArg (fun l => l[i]?) h0
    simp only [List.getElem?_take, if_pos hi] at this
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, this]
  have hin : ∀ n, n < 729 → 3 + n < A.length ∧ (A.getD (3 + n) .nil = .K ∨ A.getD (3 + n) .nil = .app 0 1) := by
    intro n hn
    have hn' : 3 + n < m0.heap.length := by omega
    refine ⟨by omega, ?_⟩
    rw [hAm _ hn']
    have := congrArg (fun l => l[3 + n]?) htk
    simp only [List.getElem?_take, if_pos (show 3 + n < 729 + 3 by omega)] at this
    rw [slot_get hn] at this
    rw [List.getD_eq_getElem?_getD, this]
    cases ρ n
    · exact .inr rfl
    · exact .inl rfl
  have hpubA : ∀ i, i < blank.heap.length → ¬ (3 ≤ i ∧ i < 3 + 729) →
      i < A.length ∧ A.getD i .nil = blank.heap.getD i .nil := by
    intro i hi hp
    have hi' : i < m0.heap.length := by rw [hlenm]; exact hi
    have hor : i < 3 ∨ 729 + 3 ≤ i := by
      rcases Nat.lt_or_ge i 3 with h3 | h3
      · exact .inl h3
      · exact .inr (Nat.le_of_not_lt (fun hlt => hp ⟨h3, by omega⟩))
    refine ⟨by omega, ?_⟩
    rw [hAm i hi', List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, hpub i hor]
  have hPP : P = 2013265921 := rfl
  refine ⟨balanced4 (by omega) (cpuW_honest hA hk) cpuW_blindZero (progS_honest hpubA) (progS_nobus _)
    (witS_honest hin) (witS_nobus A), ?_⟩
  exact {
    hw := by show 0 < 2 ^ 10; decide
    hc := by show 0 < 2 ^ 16; decide
    hm := by show 0 < A.length; rw [hlen]; decide
    zw := fun _ _ => rfl
    za := fun r _ => by show cpuColW A row k r (BLA + 4) = 0; unfold cpuColW; rw [if_neg (by decide)]
    zb := fun r _ => by show cpuColW A row k r (BLB + 4) = 0; unfold cpuColW; rw [if_neg (by decide)]
    zm := fun _ _ => rfl }

end

/-- **The hidden-term circuit's honest tables meet `wit_transcript`'s
    hypotheses**: from a run `wit_complete` accepts, its CPU, memory and
    witness tables balance with the public program table, and their
    blinding flags are clear. -/
theorem wit_honest_zk {V x : Term} {W : Nat} {ws : List Cell} (hwf : WF ws) (hwl : ws.length = W)
    (hW8 : W ≤ 2 ^ 8) {A : List Cell} {k : Nat} {row : Nat → Air.Row}
    (hA : AcceptsFrom A (wMachine ws (V ⬝ x)) k row) (hlen : A.length = 2 ^ 10) (hk : k ≤ 2 ^ 10) :
    let blank := wMachine (List.replicate W .S) (V ⬝ x)
    let C := cpuTableW A row k (2 ^ 10)
    let Pg := progTableW blank.heap W
    let Wt := witTableG 0 A 0 W
    let Mm := memTableC A (cpuAirW blank.hd blank.stk blank.heap.length) (progAirW blank.heap W) (witAirW W) C Pg Wt
    Balanced (witTables blank.hd blank.stk blank.heap.length blank.heap W C Mm Pg Wt) ∧
    Unblinded WT_BLIND C Mm Wt := by
  intro blank C Pg Wt Mm
  have hl : ws.length = (List.replicate W Cell.S).length := by rw [List.length_replicate, hwl]
  obtain ⟨_, _, hlenm, htake, hpub⟩ := wMachine_public ws (List.replicate W .S) (V ⬝ x) hl
  obtain ⟨m0, hm0⟩ : ∃ m, wMachine ws (V ⬝ x) = m := ⟨_, rfl⟩
  rw [hm0] at hA hlenm htake hpub
  have h0 : A.take m0.heap.length = m0.heap := by rw [← hA.ctr0]; exact hA.heap0
  have hmlen : m0.heap.length ≤ A.length := by
    have := congrArg List.length h0; rw [List.length_take] at this; omega
  have hWl : W ≤ m0.heap.length := by
    have := congrArg List.length htake; rw [List.length_take, hwl] at this; omega
  have hAm : ∀ i, i < m0.heap.length → A.getD i .nil = m0.heap.getD i .nil := by
    intro i hi
    have := congrArg (fun l => l[i]?) h0
    simp only [List.getElem?_take, if_pos hi] at this
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, this]
  have hreg : ∀ i, i < W → cellOK (0 + 0 + i) (A.getD (0 + 0 + i) .nil) = true := by
    intro i hi
    simp only [Nat.zero_add]
    rw [hAm i (by omega)]
    have := congrArg (fun l => l[i]?) htake
    simp only [List.getElem?_take, if_pos (show i < ws.length by omega)] at this
    rw [List.getD_eq_getElem?_getD, this, List.getElem?_eq_getElem (by omega), Option.getD_some]
    exact hwf i _ (List.getElem?_eq_getElem (by omega))
  have hpubA : ∀ i, i < blank.heap.length → W ≤ i → i < A.length ∧ A.getD i .nil = blank.heap.getD i .nil := by
    intro i hi hp
    have hi' : i < m0.heap.length := by rw [hlenm]; exact hi
    refine ⟨by omega, ?_⟩
    rw [hAm i hi', List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, hpub i (by omega)]
  have hPP : P = 2013265921 := rfl
  refine ⟨balancedW (by omega) (cpuW_honest hA hk) cpuW_blindZero (progW_honest hpubA)
    (witT_honest (a0 := 0) (N := 0) (fun h => absurd h (Nat.lt_irrefl 0)) (fun i hi => absurd hi (Nat.not_lt_zero _))
      hreg (by omega)) witT_blindZero, ?_⟩
  exact {
    hw := by show 0 < (witRowsG 0 0 W).length; rw [witRowsG_len (by omega)]; exact Nat.two_pow_pos 9
    hc := by show 0 < 2 ^ 10; decide
    hm := by show 0 < A.length; rw [hlen]; decide
    zw := fun r _ => witT_flag r
    za := fun r _ => by show cpuColW A row k r (BLA + 4) = 0; unfold cpuColW; rw [if_neg (by decide)]
    zb := fun r _ => by show cpuColW A row k r (BLB + 4) = 0; unfold cpuColW; rw [if_neg (by decide)]
    zm := fun _ _ => rfl }

end Circuit
