import Ski.Circuit.CompWit

/-!
# The composed memory's prefix is the composed machine

The program table's lookups pin the public cells, the witness table's the
bit cells (`K` or `A 0 1`) and the region's (well formed).  So the memory,
up to the first counter, is the composed machine of the bits and region it
holds (`CompOK.heap0`), and that region is well formed (`CompOK.regionWF`).
-/

namespace Circuit

open B Compose CompM Stmt Mach Wit

theorem filter_nil' {α : Type} {p : α → Bool} : ∀ {l : List α}, (∀ a ∈ l, p a = false) → l.filter p = []
  | [], _ => rfl
  | a :: l, h => by
    rw [List.filter_cons, h a List.mem_cons_self]
    exact filter_nil' (fun b hb => h b (List.mem_cons_of_mem _ hb))

/-- The public cells of a heap with a private range, counted. -/
theorem public_length (heap : List Cell) (N W : Nat) (hl : 3 + N + W ≤ heap.length) :
    (heap.zipIdx.filter fun x => !(3 ≤ x.2 && x.2 < 3 + N + W)).length + (N + W) = heap.length := by
  have e : heap = heap.take 3 ++ (heap.drop 3).take (N + W) ++ (heap.drop 3).drop (N + W) := by
    rw [List.append_assoc, List.take_append_drop, List.take_append_drop]
  have l1 : (heap.take 3).length = 3 := by rw [List.length_take]; omega
  have l2 : ((heap.drop 3).take (N + W)).length = N + W := by rw [List.length_take, List.length_drop]; omega
  rw [e, List.zipIdx_append, List.zipIdx_append, List.filter_append, List.filter_append]
  rw [List.filter_eq_self.2 (fun x hx => by
      obtain ⟨b1, b2, -⟩ := List.mem_zipIdx hx
      simp only [List.length_append, l1, l2] at b1 b2
      simp only [Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not]
      exact .inl (by omega))]
  rw [filter_nil' (fun x hx => by
      obtain ⟨b1, b2, -⟩ := List.mem_zipIdx hx
      simp only [List.length_append, l1, l2] at b1 b2
      simp only [Bool.not_eq_false', Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨by omega, by omega⟩)]
  rw [List.filter_eq_self.2 (fun x hx => by
      obtain ⟨b1, b2, -⟩ := List.mem_zipIdx hx
      simp only [List.length_append, l1, l2] at b1 b2
      simp only [Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not]
      exact .inr (by omega))]
  simp only [List.length_append, List.length_zipIdx, List.length_nil, List.length_take, List.length_drop, l1, l2]
  omega

/-- A public cell has a program row. -/
theorem progRowsC_has {heap : List Cell} {N W i : Nat} (hi : i < heap.length) (hp : ¬ (3 ≤ i ∧ i < 3 + N + W)) :
    ∃ q, q < (progRowsC heap N W).length ∧ (progRowsC heap N W).getD q [] =
      [ofN i, ofN (cellTag heap[i]), ofN (cellFields heap[i]).1, ofN (cellFields heap[i]).2, ofN 1] := by
  let pub := heap.zipIdx.filter fun x => !(3 ≤ x.2 && x.2 < 3 + N + W)
  have hm : (heap[i], i) ∈ pub := by
    refine List.mem_filter.2 ⟨?_, ?_⟩
    · have hz : i < heap.zipIdx.length := by rw [List.length_zipIdx]; exact hi
      have := List.getElem_mem hz
      rw [List.getElem_zipIdx] at this
      simpa using this
    · simp only [Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not]
      by_cases h3 : 3 ≤ i
      · exact .inr (fun h' => hp ⟨h3, h'⟩)
      · exact .inl h3
  let rows := pub.map fun x => [ofN x.2, ofN (cellTag x.1), ofN (cellFields x.1).1, ofN (cellFields x.1).2, ofN 1]
  have hr : [ofN i, ofN (cellTag heap[i]), ofN (cellFields heap[i]).1, ofN (cellFields heap[i]).2, ofN 1] ∈ rows :=
    List.mem_map.2 ⟨_, hm, rfl⟩
  obtain ⟨q, hq, e⟩ := List.getElem_of_mem hr
  have hlen : rows.length ≤ (progRowsC heap N W).length := by
    show rows.length ≤ (rows ++ _).length
    simp
  refine ⟨q, Nat.lt_of_lt_of_le hq hlen, ?_⟩
  show (rows ++ _).getD q [] = _
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hq, List.getElem?_eq_getElem hq, e]
  rfl

theorem progRowsC_length (heap : List Cell) (N W : Nat) :
    (heap.zipIdx.filter fun x => !(3 ≤ x.2 && x.2 < 3 + N + W)).length ≤ (progRowsC heap N W).length := by
  unfold progRowsC; simp

theorem witRowsG_get {a0 N W q : Nat} (hq : q < N + W) :
    (witRowsG a0 N W).getD q [] = [ofN (a0 + q), ofN 1, ofN (if q < N then 1 else 0)] := by
  unfold witRowsG
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp; omega)]
  by_cases hN : q < N
  · rw [List.getElem?_append_left (by simp; omega), List.getElem?_map, List.getElem?_range hN]
    simp [hN]
  · rw [List.getElem?_append_right (by simp; omega), List.getElem?_map,
      List.getElem?_range (by simp; omega)]
    simp only [List.length_map, List.length_range, Option.map_some, Option.getD_some, if_neg hN]
    rw [show a0 + N + (q - N) = a0 + q by omega]

theorem witRows_get {N W q : Nat} (hq : q < N + W) :
    (witRows N W).getD q [] = [ofN (3 + q), ofN 1, ofN (if q < N then 1 else 0)] := witRowsG_get hq

theorem witRowsG_length (a0 N W : Nat) : N + W ≤ (witRowsG a0 N W).length := by unfold witRowsG; simp

theorem witRows_length (N W : Nat) : N + W ≤ (witRows N W).length := witRowsG_length 3 N W

/-- The composed machine with the bits clear and the region blank: what
    the verifier holds. -/
def blankM (shp : BT) (W : Nat) (Ps : List Term) : Mach := cMachine (fun _ => false) shp (List.replicate W .S) Ps

def blankRoots (shp : BT) (W : Nat) (Ps : List Term) : List Nat :=
  (cHeap (fun _ => false) shp (List.replicate W .S) Ps).2

theorem blank_region (W : Nat) : ∀ (i : Nat) (c : Cell), (List.replicate W Cell.S)[i]? = some c → ∀ k, cellOK k c = true := by
  intro i c h k
  rw [List.getElem?_replicate] at h
  split at h
  · cases h; rfl
  · cases h

theorem blank_fits (shp : BT) (W : Nat) (Ps : List Term) :
    Fits (blankM shp W Ps).heap ∧ ∀ r ∈ blankRoots shp W Ps, r < (blankM shp W Ps).heap.length :=
  cMachine_fits _ shp _ Ps (fun i c h => blank_region W i c h _)

theorem blank_prefix (shp : BT) (W : Nat) (Ps : List Term) :
    3 + BT.nleaves shp + W ≤ (blankM shp W Ps).heap.length := by
  have := (cMachine_public (fun _ => false) (fun _ => false) shp (List.replicate W .S) (List.replicate W .S) Ps rfl).2.2.2.2.1
  have hl := congrArg List.length this
  simp only [List.length_take, List.length_append, slotHeap_length, List.length_replicate] at hl
  have : min (BT.nleaves shp + 3 + W) (blankM shp W Ps).heap.length = BT.nleaves shp + 3 + W := hl
  show _ ≤ (cMachine (fun _ => false) shp (List.replicate W .S) Ps).heap.length
  omega

theorem nleaves_pos : ∀ t : BT, 0 < BT.nleaves t
  | .leaf _ => Nat.one_pos
  | .node l _ => Nat.lt_of_lt_of_le (nleaves_pos l) (Nat.le_add_right _ _)

section

variable {shp : BT} {W : Nat} {Ps : List Term} {C Mm Pg Wt Sg : Table}
  (h : CompOK (blankM shp W Ps).hd (blankM shp W Ps).stk (blankM shp W Ps).heap.length
    (blankRoots shp W Ps).length (blankM shp W Ps).stk (blankM shp W Ps).heap (BT.nleaves shp) W
    (blankRoots shp W Ps) C Mm Pg Wt Sg)
include h

theorem CompOK.pg_h : Pg.h ≤ 2 ^ 27 := h.two (progAirC (blankM shp W Ps).heap (BT.nleaves shp) W, Pg) (by simp [compTables])
theorem CompOK.wt_h : Wt.h ≤ 2 ^ 27 := h.two (witAir (BT.nleaves shp) W, Wt) (by simp [compTables])

/-- The blank heap is small: its public cells are program rows, its private
    ones witness rows. -/
theorem CompOK.heap_le : (blankM shp W Ps).heap.length ≤ 2 ^ 28 := by
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

theorem CompOK.heap_lt : (blankM shp W Ps).heap.length < P :=
  Nat.lt_of_le_of_lt h.heap_le (by decide)

/-- **A public cell is in memory.** -/
theorem CompOK.pubCell {i : Nat} (hi : i < (blankM shp W Ps).heap.length)
    (hp : ¬ (3 ≤ i ∧ i < 3 + BT.nleaves shp + W)) :
    i < Mm.h ∧ (memOf Mm)[i]? = (blankM shp W Ps).heap[i]? := by
  obtain ⟨q, hq, e⟩ := progRowsC_has (N := BT.nleaves shp) (W := W) hi hp
  have hqP : q < Pg.h := by rw [h.pgpre.1]; exact hq
  have pv : ∀ j, j < 5 → (prec j).eval (Pg.env q) = ((progRowsC (blankM shp W Ps).heap (BT.nleaves shp) W).getD q []).getD j 0 :=
    fun j hj => prec_eval h.pgpre hqP hj
  let hp' := (blankM shp W Ps).heap
  have hit := h.memHit (v := [ofN i, ofN (cellTag hp'[i]), ofN (cellFields hp'[i]).1, ofN (cellFields hp'[i]).2])
    ⟨(progAirC (blankM shp W Ps).heap (BT.nleaves shp) W, Pg), by simp [compTables], rfl, q, hqP, _, List.mem_cons_self, rfl,
      by simp only [progAirC, List.map_cons, List.map_nil, pv 0 (by decide), pv 1 (by decide), pv 2 (by decide),
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
theorem CompOK.privCell {q : Nat} (hq : q < BT.nleaves shp + W) :
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

/-- The memory's bits: bit `i` set when its cell is `K`. -/
def bitsM (A : List Cell) (i : Nat) : Bool := A[i + 3]? == some .K

/-- The memory's region: the `W` cells after the bits. -/
def regionM (A : List Cell) (N W : Nat) : List Cell := (A.drop (N + 3)).take W

theorem CompOK.mem_len : 3 + BT.nleaves shp + W ≤ Mm.h := by
  have := (h.privCell (q := BT.nleaves shp + W - 1) (by have := nleaves_pos shp; omega)).1
  have := nleaves_pos shp
  omega

theorem CompOK.region_len : (regionM (memOf Mm) (BT.nleaves shp) W).length = W := by
  have := h.mem_len
  simp only [regionM, List.length_take, List.length_drop, memOf_length]
  omega

/-- **The region the memory holds is well formed.** -/
theorem CompOK.regionWF : ∀ i c, (regionM (memOf Mm) (BT.nleaves shp) W)[i]? = some c →
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
theorem CompOK.heap0 :
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

end

end Circuit
