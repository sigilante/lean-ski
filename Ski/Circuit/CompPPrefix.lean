import Ski.Circuit.CompPJetRow
import Ski.Circuit.CompPrefix
import Ski.Circuit.CompHeap
import Ski.Circuit.SudSound

/-!
# The circuit with the Poseidon2 jet: the memory's prefix

As `Ski/Circuit/CompPrefix.lean` for the composed circuit, over the open
composed machine (`CompM.cMachineO`): its cells' fields are small
(`cMachineO_fitsB`), the program table's lookups pin its public cells, the
witness table's the bit cells and the region's, so the memory's prefix is
the open machine of the bits and region it holds (`CompPOK.heap0`).
-/

namespace Circuit

open B Compose CompM Stmt Mach Wit

/-- `addStmtsO` keeps the fields small, and its roots point into the heap. -/
theorem addStmtsO_fitsB (Bd pe wr : Nat) : ∀ (Vs : List OTerm) (h : List Cell), FitsB Bd h →
    pe < h.length → wr < h.length → (∀ V ∈ Vs, ∀ x, Occ x V → x < Bd) →
    FitsB Bd (addStmtsO pe wr h Vs).1 ∧ (∀ r ∈ (addStmtsO pe wr h Vs).2, r < (addStmtsO pe wr h Vs).1.length) ∧
      h.length ≤ (addStmtsO pe wr h Vs).1.length
  | [], h, hf, _, _, _ => by
    simp only [addStmtsO]
    exact ⟨hf, (fun _ h' => nomatch h'), Nat.le_refl _⟩
  | P :: Vs, h, hf, hpe, hwr, hv => by
    have hob := obuild_pbuild P h
    obtain ⟨f2, p2, l2⟩ := pbuild_fitsB 0 Bd P h hf
      (fun x hx => ⟨fun h0 => absurd h0 (Nat.not_lt_zero _), fun _ => hv P List.mem_cons_self x hx⟩)
    rw [← hob] at f2 p2 l2
    have a1 : (cellFields (Cell.app (obuild h P).2 pe)).1 < max ((obuild h P).1.length + 1) Bd ∧
        (cellFields (Cell.app (obuild h P).2 pe)).2 < max ((obuild h P).1.length + 1) Bd := by
      simp only [cellFields]; exact ⟨lt_max_left (by omega), lt_max_left (by omega)⟩
    have g1 := fitsB_push f2 a1
    have a2 : (cellFields (Cell.app (obuild h P).1.length wr)).1 <
          max (((obuild h P).1 ++ [Cell.app (obuild h P).2 pe]).length + 1) Bd ∧
        (cellFields (Cell.app (obuild h P).1.length wr)).2 <
          max (((obuild h P).1 ++ [Cell.app (obuild h P).2 pe]).length + 1) Bd := by
      simp only [cellFields, List.length_append, List.length_singleton]
      exact ⟨lt_max_left (by omega), lt_max_left (by omega)⟩
    have g2 := fitsB_push g1 a2
    have hl : ((obuild h P).1 ++ [Cell.app (obuild h P).2 pe] ++ [Cell.app (obuild h P).1.length wr]).length =
        (obuild h P).1.length + 2 := by simp
    obtain ⟨i1, i2, i3⟩ := addStmtsO_fitsB Bd pe wr Vs _ g2 (by rw [hl]; omega) (by rw [hl]; omega)
      (fun V hV => hv V (List.mem_cons_of_mem _ hV))
    have e : (obuild h P).1 ++ [Cell.app (obuild h P).2 pe, Cell.app (obuild h P).1.length wr] =
        (obuild h P).1 ++ [Cell.app (obuild h P).2 pe] ++ [Cell.app (obuild h P).1.length wr] := by simp
    show FitsB Bd (addStmtsO pe wr ((obuild h P).1 ++ [Cell.app (obuild h P).2 pe, Cell.app (obuild h P).1.length wr]) Vs).1 ∧
      (∀ r ∈ ((obuild h P).1.length + 1) ::
        (addStmtsO pe wr ((obuild h P).1 ++ [Cell.app (obuild h P).2 pe, Cell.app (obuild h P).1.length wr]) Vs).2,
          r < (addStmtsO pe wr ((obuild h P).1 ++ [Cell.app (obuild h P).2 pe, Cell.app (obuild h P).1.length wr]) Vs).1.length) ∧
      h.length ≤ (addStmtsO pe wr ((obuild h P).1 ++ [Cell.app (obuild h P).2 pe, Cell.app (obuild h P).1.length wr]) Vs).1.length
    rw [e]
    refine ⟨i1, fun r hr => ?_, by rw [hl] at i3; omega⟩
    rcases List.mem_cons.1 hr with rfl | hr
    · rw [hl] at i3; omega
    · exact i2 r hr

/-- **The open composed machine's fields are small**, below its length or
    `Bd`, and its roots point into it. -/
theorem cMachineO_fitsB (Bd : Nat) (ρ : Nat → Bool) (shp : BT) (region : List Cell) (Vs : List OTerm)
    (hr : ∀ i c, region[i]? = some c → cellOK (BT.nleaves shp + 3 + i) c = true)
    (hv : ∀ V ∈ Vs, ∀ x, Occ x V → x < Bd) :
    FitsB Bd (cMachineO ρ shp region Vs).heap ∧
      (∀ r ∈ (cHeapO ρ shp region Vs).2, r < (cMachineO ρ shp region Vs).heap.length) ∧
      combRoot ρ shp region < (cMachineO ρ shp region Vs).heap.length := by
  let N := BT.nleaves shp
  let h0 := slotHeap ρ N ++ region
  have hwf := slots_wf ρ N hr
  have hl0 : N + 3 ≤ h0.length := by simp [h0, slotHeap_length]
  have f0 : FitsB Bd h0 := by
    intro c hc
    obtain ⟨i, hi, e⟩ := List.getElem_of_mem hc
    have := hwf i c (by rw [List.getElem?_eq_getElem hi, e])
    cases c with
    | app a b =>
      simp only [cellOK, Bool.and_eq_true, decide_eq_true_eq] at this
      exact ⟨lt_max_left (by simp only [cellFields]; omega), lt_max_left (by simp only [cellFields]; omega)⟩
    | S | K | I => exact ⟨lt_max_left (by simp only [cellFields]; omega), lt_max_left (by simp only [cellFields]; omega)⟩
    | nil | cons _ _ | atom _ => simp [cellOK] at this
  have hv0 : ∀ x, Occ x (encO shp 0) → (x < N + 2 → slotPtr x < h0.length) ∧ (¬ x < N + 2 → x < Bd) := by
    intro x hx
    have := encO_occ shp 0 x hx
    have hN : BT.nleaves shp = N := rfl
    rw [hN] at this
    refine ⟨fun _ => ?_, fun hn => absurd (by omega) hn⟩
    rcases x with _ | _ | x
    · show 0 < h0.length; omega
    · show 2 < h0.length; omega
    · show x + 3 < h0.length; omega
  obtain ⟨f1, p1, l1⟩ := pbuild_fitsB (N + 2) Bd (encO shp 0) h0 f0 hv0
  obtain ⟨f2, rts, l2⟩ := addStmtsO_fitsB Bd (pbuild (N + 2) h0 (encO shp 0)).2 (h0.length - 1) Vs _ f1 p1
    (by omega) hv
  refine ⟨fitsB_push f2 ⟨lt_max_left (by simp only [cellFields]; omega), lt_max_left (by simp only [cellFields]; omega)⟩,
    fun r hr => ?_, ?_⟩
  · have := rts r hr
    show r < ((cHeapO ρ shp region Vs).1 ++ [Cell.nil]).length
    rw [List.length_append, List.length_singleton]
    exact Nat.lt_succ_of_lt this
  · have e : (cHeapO ρ shp region Vs).1 =
        (addStmtsO (pbuild (N + 2) h0 (encO shp 0)).2 (h0.length - 1) (pbuild (N + 2) h0 (encO shp 0)).1 Vs).1 := rfl
    show (pbuild (N + 2) h0 (encO shp 0)).2 < ((cHeapO ρ shp region Vs).1 ++ [Cell.nil]).length
    rw [List.length_append, List.length_singleton, e]
    omega


theorem witRowsP_get {N W q : Nat} (hq : q < N + W) :
    (witRowsP N W).getD q [] = [ofN (3 + q), ofN 1, ofN (if q < N then 1 else 0)] := by
  unfold witRowsP
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp; omega)]
  by_cases hN : q < N
  · rw [List.getElem?_append_left (by simp; omega), List.getElem?_map, List.getElem?_range hN]
    simp [hN]
  · rw [List.getElem?_append_right (by simp; omega), List.getElem?_map,
      List.getElem?_range (by simp; omega)]
    simp only [List.length_map, List.length_range, Option.map_some, Option.getD_some, if_neg hN]
    rw [show 3 + N + (q - N) = 3 + q by omega]

theorem witRowsP_length (N W : Nat) : N + W ≤ (witRowsP N W).length := by unfold witRowsP; simp

/-- The open composed machine with the bits clear and the region blank. -/
def blankMO (shp : BT) (W : Nat) (Vs : List OTerm) : Mach := cMachineO (fun _ => false) shp (List.replicate W .S) Vs

def blankRootsO (shp : BT) (W : Nat) (Vs : List OTerm) : List Nat :=
  (cHeapO (fun _ => false) shp (List.replicate W .S) Vs).2

theorem blankO_prefix (shp : BT) (W : Nat) (Vs : List OTerm) :
    3 + BT.nleaves shp + W ≤ (blankMO shp W Vs).heap.length := by
  have := (cMachineO_public (fun _ => false) (fun _ => false) shp (List.replicate W .S) (List.replicate W .S) Vs
    rfl).2.2.2.2.1
  have hl := congrArg List.length this
  simp only [List.length_take, List.length_append, slotHeap_length, List.length_replicate] at hl
  have : min (BT.nleaves shp + 3 + W) (blankMO shp W Vs).heap.length = BT.nleaves shp + 3 + W := hl
  show _ ≤ (cMachineO (fun _ => false) shp (List.replicate W .S) Vs).heap.length
  omega

section

variable {shp : BT} {W : Nat} {Vs : List OTerm} {J root : Nat} {C Mm Pg Wt Sg Pi Po Pp Px : Table}
  (h : CompPOK (blankMO shp W Vs).hd (blankMO shp W Vs).stk (blankMO shp W Vs).heap.length
    (blankRootsO shp W Vs).length (blankMO shp W Vs).stk J root (blankMO shp W Vs).heap (BT.nleaves shp) W
    (blankRootsO shp W Vs) C Mm Pg Wt Sg Pi Po Pp Px)
include h

theorem CompPOK.pg_h : Pg.h ≤ 2 ^ 27 := h.two (progAirC (blankMO shp W Vs).heap (BT.nleaves shp) W, Pg) (by simp [compPTables])
theorem CompPOK.wt_h : Wt.h ≤ 2 ^ 27 := h.two (witAirP (BT.nleaves shp) W, Wt) (by simp [compPTables])

/-- The blank heap is small: its public cells are program rows, its private
    ones witness rows. -/
theorem CompPOK.heap_le : (blankMO shp W Vs).heap.length ≤ 2 ^ 28 := by
  have e := public_length (blankMO shp W Vs).heap (BT.nleaves shp) W (blankO_prefix shp W Vs)
  have p1 := progRowsC_length (blankMO shp W Vs).heap (BT.nleaves shp) W
  have p2 := witRowsP_length (BT.nleaves shp) W
  have hp := h.pgpre.1
  have hw := h.wtpre.1
  have a := h.pg_h
  have b := h.wt_h
  simp only [progAirC, witAirP] at hp hw
  have : (2 : Nat) ^ 28 = 2 ^ 27 + 2 ^ 27 := by decide
  omega

theorem CompPOK.heap_lt : (blankMO shp W Vs).heap.length < P :=
  Nat.lt_of_le_of_lt h.heap_le (by decide)

theorem CompPOK.memW {c : E} (hc : c ∈ witCons) {q : Nat} (hq : q < Wt.h) : c.eval (Wt.env q) = 0 :=
  h.wit.2 c hc q hq

theorem CompPOK.witCell {q : Nat} (hq : q < Wt.h) (hact : Wt.pre q 1 = 1) :
    ∃ cell, (Wt.pre q 0).val < Mm.h ∧ (memOf Mm)[(Wt.pre q 0).val]? = some cell ∧
      cellOK (Wt.pre q 0).val cell = true ∧ (Wt.pre q 2 = 1 → cell = .K ∨ cell = .app 0 1) :=
  witCellG (fun c hc q hq => h.memW hc hq)
    (fun q hq hc => h.memHit ⟨(witAirP (BT.nleaves shp) W, Wt), by simp [compPTables], rfl, q, hq, _,
      List.mem_cons_self, rfl, rfl, hc⟩)
    (mem_addrC h.mem) h.mem_h hq hact

/-- **A public cell is in memory.** -/
theorem CompPOK.pubCell {Bd : Nat} (hBd : Bd < P) (hfit : FitsB Bd (blankMO shp W Vs).heap)
    {i : Nat} (hi : i < (blankMO shp W Vs).heap.length) (hp : ¬ (3 ≤ i ∧ i < 3 + BT.nleaves shp + W)) :
    i < Mm.h ∧ (memOf Mm)[i]? = (blankMO shp W Vs).heap[i]? := by
  obtain ⟨q, hq, e⟩ := progRowsC_has (N := BT.nleaves shp) (W := W) hi hp
  have hqP : q < Pg.h := by rw [h.pgpre.1]; exact hq
  have pv : ∀ j, j < 5 → (prec j).eval (Pg.env q) =
      ((progRowsC (blankMO shp W Vs).heap (BT.nleaves shp) W).getD q []).getD j 0 :=
    fun j hj => prec_eval h.pgpre hqP hj
  let hp' := (blankMO shp W Vs).heap
  have hit := h.memHit (v := [ofN i, ofN (cellTag hp'[i]), ofN (cellFields hp'[i]).1, ofN (cellFields hp'[i]).2])
    ⟨(progAirC (blankMO shp W Vs).heap (BT.nleaves shp) W, Pg), by simp [compPTables], rfl, q, hqP, _,
      List.mem_cons_self, rfl,
      by simp only [progAirC, List.map_cons, List.map_nil, pv 0 (by decide), pv 1 (by decide), pv 2 (by decide),
        pv 3 (by decide), e]; rfl,
      by show (prec 4).eval _ = 1; rw [pv 4 (by decide), e]; rfl⟩
  obtain ⟨hlt, hget⟩ := h.cell hit
  have hP := h.heap_lt
  have hf := hfit _ (List.getElem_mem hi)
  have hm : max (blankMO shp W Vs).heap.length Bd < P := Nat.max_lt.2 ⟨hP, hBd⟩
  rw [val_ofN (Nat.lt_trans hi hP)] at hlt hget
  rw [cellOf_enc _ (Nat.lt_trans hf.1 hm) (Nat.lt_trans hf.2 hm)] at hget
  exact ⟨hlt, by rw [hget, List.getElem?_eq_getElem hi]⟩

/-- **A private cell is in memory**: in bit mode `K` or `A 0 1`, and well
    formed. -/
theorem CompPOK.privCell {q : Nat} (hq : q < BT.nleaves shp + W) :
    3 + q < Mm.h ∧ ∃ cell, (memOf Mm)[3 + q]? = some cell ∧ cellOK (3 + q) cell = true ∧
      (q < BT.nleaves shp → cell = .K ∨ cell = .app 0 1) := by
  have hqW : q < Wt.h := by
    rw [h.wtpre.1]; exact Nat.lt_of_lt_of_le hq (witRowsP_length _ _)
  have pv : ∀ j, j < 3 → Wt.pre q j = ((witRowsP (BT.nleaves shp) W).getD q []).getD j 0 :=
    fun j hj => h.wtpre.2 q j hqW hj
  have e := witRowsP_get (N := BT.nleaves shp) (W := W) hq
  have hact : Wt.pre q 1 = 1 := by rw [pv 1 (by decide), e]; rfl
  obtain ⟨cell, hlt, hget, hok, hbit⟩ := h.witCell hqW hact
  have ha : (Wt.pre q 0).val = 3 + q := by
    rw [pv 0 (by decide), e]
    exact val_ofN (by have := h.wt_h; have := witRowsP_length (BT.nleaves shp) W; have : P = 2013265921 := rfl; omega)
  rw [ha] at hlt hget hok
  refine ⟨hlt, cell, hget, hok, fun hN => hbit ?_⟩
  rw [pv 2 (by decide), e]
  show ofN (if q < BT.nleaves shp then 1 else 0) = 1
  rw [if_pos hN]; rfl

theorem CompPOK.mem_len : 3 + BT.nleaves shp + W ≤ Mm.h := by
  have := (h.privCell (q := BT.nleaves shp + W - 1) (by have := nleaves_pos shp; omega)).1
  have := nleaves_pos shp
  omega

theorem CompPOK.region_len : (regionM (memOf Mm) (BT.nleaves shp) W).length = W := by
  have := h.mem_len
  simp only [regionM, List.length_take, List.length_drop, memOf_length]
  omega

/-- **The region the memory holds is well formed.** -/
theorem CompPOK.regionWF : ∀ i c, (regionM (memOf Mm) (BT.nleaves shp) W)[i]? = some c →
    cellOK (BT.nleaves shp + 3 + i) c = true := by
  intro i c hc
  have hi : i < W := by
    rcases Nat.lt_or_ge i W with h' | h'
    · exact h'
    · rw [List.getElem?_eq_none (by rw [h.region_len]; exact h')] at hc; cases hc
  obtain ⟨_, cell, hget, hok, _⟩ := h.privCell (q := BT.nleaves shp + i) (by omega)
  simp only [regionM, List.getElem?_take, if_pos hi, List.getElem?_drop] at hc
  rw [show BT.nleaves shp + 3 + i = 3 + (BT.nleaves shp + i) by omega, hget] at hc
  cases hc
  rw [show BT.nleaves shp + 3 + i = 3 + (BT.nleaves shp + i) by omega]
  exact hok

/-- **The memory's prefix is the open composed machine** of the bits and
    the region it holds. -/
theorem CompPOK.heap0 {Bd : Nat} (hBd : Bd < P) (hfit : FitsB Bd (blankMO shp W Vs).heap) :
    (memOf Mm).take (blankMO shp W Vs).heap.length =
      (cMachineO (bitsM (memOf Mm)) shp (regionM (memOf Mm) (BT.nleaves shp) W) Vs).heap := by
  let A := memOf Mm
  let N := BT.nleaves shp
  let ρ := bitsM A
  let region := regionM A N W
  have hl : region.length = (List.replicate W Cell.S).length := by rw [List.length_replicate]; exact h.region_len
  obtain ⟨_, _, _, hlen, htake, hpub⟩ := cMachineO_public ρ (fun _ => false) shp region (List.replicate W .S) Vs hl
  have hRL : region.length = W := h.region_len
  have hlen2 : (cMachineO (bitsM (memOf Mm)) shp (regionM (memOf Mm) (BT.nleaves shp) W) Vs).heap.length =
      (blankMO shp W Vs).heap.length := hlen
  apply List.ext_getElem?
  intro i
  rw [List.getElem?_take]
  split
  · next hi =>
    by_cases hp : 3 ≤ i ∧ i < 3 + N + W
    · have ht := congrArg (fun l => l[i]?) htake
      rw [List.getElem?_take, if_pos (show i < N + 3 + region.length by omega)] at ht
      rw [ht]
      by_cases hb : i < 3 + N
      · have h3 : 3 ≤ i := hp.1
        have hN3 : i - 3 < N := Nat.sub_lt_left_of_lt_add h3 hb
        obtain ⟨_, cell, hget, _, hbit⟩ := h.privCell (q := i - 3) (by omega)
        rw [Nat.add_sub_cancel' h3] at hget
        rw [List.getElem?_append_left (by rw [slotHeap_length]; omega)]
        unfold slotHeap
        rw [List.getElem?_append_right (by simp; omega),
          show ([Cell.K, Cell.I, Cell.app 0 1] : List Cell).length = 3 from rfl, List.getElem?_map,
          List.getElem?_range hN3, Option.map_some]
        show A[i]? = some (if bitsM A (i - 3) then Cell.K else Cell.app 0 1)
        unfold bitsM
        rw [Nat.sub_add_cancel h3, hget]
        rcases hbit hN3 with rfl | rfl
        · rfl
        · rfl
      · rw [List.getElem?_append_right (by rw [slotHeap_length]; omega), slotHeap_length]
        show A[i]? = (regionM A N W)[i - (N + 3)]?
        simp only [regionM, List.getElem?_take, if_pos (show i - (N + 3) < W by omega), List.getElem?_drop]
        rw [show N + 3 + (i - (N + 3)) = i by omega]
    · have hor : i < 3 ∨ N + 3 + region.length ≤ i := by
        rcases Nat.lt_or_ge i 3 with h3 | h3
        · exact .inl h3
        · refine .inr ?_
          have := Nat.le_of_not_lt (fun hlt => hp ⟨h3, hlt⟩)
          omega
      rw [(h.pubCell hBd hfit (by omega) hp).2, hpub i hor]
      rfl
  · next hi =>
    rw [List.getElem?_eq_none (by omega)]

end

end Circuit
