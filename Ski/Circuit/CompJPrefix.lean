import Ski.Circuit.CompJCore
import Ski.Circuit.CompPrefix

/-!
# The composed circuit with jets: its memory's prefix

As without jets (`Ski/Circuit/CompPrefix.lean`): the program table's
lookups pin the public cells, the witness table's the bit cells (`K` or
`A 0 1`) and the region's (well formed).  So the memory, up to the first
counter, is the composed machine of the bits and region it holds
(`CJOK.heap0`), that region is well formed (`CJOK.regionWF`), and the
blank heap fits in memory (`CJOK.blank_le`).
-/

namespace Circuit

open B Compose CompM Stmt Mach Wit

section

variable {shp : BT} {W : Nat} {Ps : List Term} {roots : List (Nat × Nat)} {jets : List Air.Jet}
  {C Mm Pg Wt Sg Rt Hd Tm Po Iw : Table}
  (h : CJOK (blankM shp W Ps).hd (blankM shp W Ps).stk (blankM shp W Ps).heap.length
    (blankRoots shp W Ps).length (blankM shp W Ps).stk (blankM shp W Ps).heap (BT.nleaves shp) W
    (blankRoots shp W Ps) roots jets C Mm Pg Wt Sg Rt Hd Tm Po Iw)
include h

theorem CJOK.pg_h : Pg.h ≤ 2 ^ 27 := h.two (progAirC (blankM shp W Ps).heap (BT.nleaves shp) W, Pg) (by simp [compJTables])
theorem CJOK.wt_h : Wt.h ≤ 2 ^ 27 := h.two (witAir (BT.nleaves shp) W, Wt) (by simp [compJTables])

/-- The blank heap is small: its public cells are program rows, its private
    ones witness rows. -/
theorem CJOK.heap_le : (blankM shp W Ps).heap.length ≤ 2 ^ 28 := by
  have e := public_length (blankM shp W Ps).heap (BT.nleaves shp) W (blank_prefix shp W Ps)
  have p1 := progRowsC_length (blankM shp W Ps).heap (BT.nleaves shp) W
  have p2 := witRows_length (BT.nleaves shp) W
  have hp := h.pgpre.1
  have hw := h.wtpre.1
  have a := h.pg_h
  have b := h.wt_h
  simp only [progAirC, witAir] at hp hw
  have : (2 : Nat) ^ 28 = 2 ^ 27 + 2 ^ 27 := by decide
  omega

theorem CJOK.heap_lt : (blankM shp W Ps).heap.length < P :=
  Nat.lt_of_le_of_lt h.heap_le (by decide)

/-- **An active witness row's cell**: in memory at its address, well
    formed, and in bit mode `K` or `A 0 1`. -/
theorem CJOK.witCell {q : Nat} (hq : q < Wt.h) (hact : Wt.pre q 1 = 1) :
    ∃ cell, (Wt.pre q 0).val < Mm.h ∧ (memOf Mm)[(Wt.pre q 0).val]? = some cell ∧
      cellOK (Wt.pre q 0).val cell = true ∧ (Wt.pre q 2 = 1 → cell = .K ∨ cell = .app 0 1) :=
  witCellG (fun c hc q hq => h.wit.2 c hc q hq)
    (fun q hq hc => h.memHit ⟨(witAir (BT.nleaves shp) W, Wt), by simp [compJTables], rfl, q, hq, _,
      List.mem_cons_self, rfl, rfl, hc⟩)
    (mem_addrC h.mem) h.mem_h hq hact

/-- **A public cell is in memory.** -/
theorem CJOK.pubCell {i : Nat} (hi : i < (blankM shp W Ps).heap.length)
    (hp : ¬ (3 ≤ i ∧ i < 3 + BT.nleaves shp + W)) :
    i < Mm.h ∧ (memOf Mm)[i]? = (blankM shp W Ps).heap[i]? := by
  obtain ⟨q, hq, e⟩ := progRowsC_has (N := BT.nleaves shp) (W := W) hi hp
  have hqP : q < Pg.h := by rw [h.pgpre.1]; exact hq
  have pv : ∀ j, j < 5 → (prec j).eval (Pg.env q) = ((progRowsC (blankM shp W Ps).heap (BT.nleaves shp) W).getD q []).getD j 0 :=
    fun j hj => prec_eval h.pgpre hqP hj
  let hp' := (blankM shp W Ps).heap
  have hit := h.memHit (v := [ofN i, ofN (cellTag hp'[i]), ofN (cellFields hp'[i]).1, ofN (cellFields hp'[i]).2])
    ⟨(progAirC (blankM shp W Ps).heap (BT.nleaves shp) W, Pg), by simp [compJTables], rfl, q, hqP, _, List.mem_cons_self, rfl,
      by simp only [List.map_cons, List.map_nil, pv 0 (by decide), pv 1 (by decide), pv 2 (by decide),
        pv 3 (by decide), e]; rfl,
      by show (prec 4).eval _ = 1; rw [pv 4 (by decide), e]; rfl⟩
  obtain ⟨hlt, hget⟩ := h.cell hit
  have hP := h.heap_lt
  have hf := (blank_fits shp W Ps).1 _ (List.getElem_mem hi)
  rw [val_ofN (Nat.lt_trans hi hP)] at hlt hget
  rw [cellOf_enc _ (Nat.lt_trans hf.1 hP) (Nat.lt_trans hf.2 hP)] at hget
  exact ⟨hlt, by rw [hget, List.getElem?_eq_getElem hi]⟩

/-- **A private cell is in memory**: in bit mode `K` or `A 0 1`, and well
    formed. -/
theorem CJOK.privCell {q : Nat} (hq : q < BT.nleaves shp + W) :
    3 + q < Mm.h ∧ ∃ cell, (memOf Mm)[3 + q]? = some cell ∧ cellOK (3 + q) cell = true ∧
      (q < BT.nleaves shp → cell = .K ∨ cell = .app 0 1) := by
  have hqW : q < Wt.h := by
    rw [h.wtpre.1]; exact Nat.lt_of_lt_of_le hq (witRows_length _ _)
  have pv : ∀ j, j < 3 → Wt.pre q j = ((witRows (BT.nleaves shp) W).getD q []).getD j 0 :=
    fun j hj => h.wtpre.2 q j hqW hj
  have e := witRows_get (N := BT.nleaves shp) (W := W) hq
  have hact : Wt.pre q 1 = 1 := by rw [pv 1 (by decide), e]; rfl
  obtain ⟨cell, hlt, hget, hok, hbit⟩ := h.witCell hqW hact
  have ha : (Wt.pre q 0).val = 3 + q := by
    rw [pv 0 (by decide), e]
    exact val_ofN (by have := h.wt_h; have : P = 2013265921 := rfl; omega)
  rw [ha] at hlt hget hok
  refine ⟨hlt, cell, hget, hok, fun hN => hbit ?_⟩
  rw [pv 2 (by decide), e]
  show ofN (if q < BT.nleaves shp then 1 else 0) = 1
  rw [if_pos hN]; rfl

theorem CJOK.mem_len : 3 + BT.nleaves shp + W ≤ Mm.h := by
  have := (h.privCell (q := BT.nleaves shp + W - 1) (by have := nleaves_pos shp; omega)).1
  have := nleaves_pos shp
  omega

theorem CJOK.region_len : (regionM (memOf Mm) (BT.nleaves shp) W).length = W := by
  have := h.mem_len
  simp only [regionM, List.length_take, List.length_drop, memOf_length]
  omega

/-- **The region the memory holds is well formed.** -/
theorem CJOK.regionWF : ∀ i c, (regionM (memOf Mm) (BT.nleaves shp) W)[i]? = some c →
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

/-- **The memory's prefix is the composed machine** of the bits and the
    region it holds. -/
theorem CJOK.heap0 :
    (memOf Mm).take (blankM shp W Ps).heap.length =
      (cMachine (bitsM (memOf Mm)) shp (regionM (memOf Mm) (BT.nleaves shp) W) Ps).heap := by
  let A := memOf Mm
  let N := BT.nleaves shp
  let ρ := bitsM A
  let region := regionM A N W
  have hl : region.length = (List.replicate W Cell.S).length := by rw [List.length_replicate]; exact h.region_len
  obtain ⟨_, _, _, hlen, htake, hpub⟩ := cMachine_public ρ (fun _ => false) shp region (List.replicate W .S) Ps hl
  have hlen' : (cMachine ρ shp region Ps).heap.length = (blankM shp W Ps).heap.length := hlen
  have hRL : region.length = W := h.region_len
  have hlen2 : (cMachine (bitsM (memOf Mm)) shp (regionM (memOf Mm) (BT.nleaves shp) W) Ps).heap.length =
      (blankM shp W Ps).heap.length := hlen
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
      · -- a bit cell
        have h3 : 3 ≤ i := hp.1
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
      · -- a region cell
        rw [List.getElem?_append_right (by rw [slotHeap_length]; omega), slotHeap_length]
        show A[i]? = (regionM A N W)[i - (N + 3)]?
        simp only [regionM, List.getElem?_take, if_pos (show i - (N + 3) < W by omega), List.getElem?_drop]
        rw [show N + 3 + (i - (N + 3)) = i by omega]
    · -- a public cell
      have hor : i < 3 ∨ N + 3 + region.length ≤ i := by
        rcases Nat.lt_or_ge i 3 with h3 | h3
        · exact .inl h3
        · refine .inr ?_
          have := Nat.le_of_not_lt (fun hlt => hp ⟨h3, hlt⟩)
          omega
      rw [(h.pubCell (by omega) hp).2, hpub i hor]
      rfl
  · next hi =>
    rw [List.getElem?_eq_none (by omega)]

/-- **The blank heap fits in memory**, so in `2^27` cells. -/
theorem CJOK.blank_le : (blankM shp W Ps).heap.length ≤ Mm.h := by
  have e := congrArg List.length h.heap0
  have hl := (cMachine_public (bitsM (memOf Mm)) (fun _ => false) shp (regionM (memOf Mm) (BT.nleaves shp) W)
    (List.replicate W .S) Ps (by rw [List.length_replicate]; exact h.region_len)).2.2.2.1
  rw [List.length_take, memOf_length, hl] at e
  show (cMachine (fun _ => false) shp (List.replicate W .S) Ps).heap.length ≤ Mm.h
  omega

end

end Circuit
