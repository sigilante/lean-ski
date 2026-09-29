import Ski.Circuit.WitAir
import Ski.Circuit.RowSound
import Ski.Circuit.CompPrefix
import Ski.Circuit.CompWitT

/-!
# Soundness of the hidden-term circuit

Tables accepted for the witness circuit of an atom `V x` and a region size
`W` hold, in their memory's first `W` cells, a well-formed region whose
witness realizes the atom (`witExport_sound`, by `Wit.wit_realizes`).
-/

namespace Circuit

open B Air Wit Mach

/-- The witness circuit's four tables. -/
def witTables (hd0 stk0 ctr0 : Nat) (heap : List Cell) (W : Nat) (C Mm Pg Wt : Table) : List (AirD × Table) :=
  [(cpuAirW hd0 stk0 ctr0, C), (memAirC, Mm), (progAirW heap W, Pg), (witAirW W, Wt)]

/-- **What an accepted proof of the witness circuit gives.** -/
structure WitOK (hd0 stk0 ctr0 : Nat) (heap : List Cell) (W : Nat) (C Mm Pg Wt : Table) : Prop where
  cpu : Sat (cpuAirW hd0 stk0 ctr0) C
  mem : Sat memAirC Mm
  wit : Sat (witAirW W) Wt
  pgpre : PreIs (progAirW heap W) Pg
  wtpre : PreIs (witAirW W) Wt
  bal : Balanced (witTables hd0 stk0 ctr0 heap W C Mm Pg Wt)
  hts : HeightsOK (witTables hd0 stk0 ctr0 heap W C Mm Pg Wt)
  two : TwoAdic (witTables hd0 stk0 ctr0 heap W C Mm Pg Wt)

/-- The witness CPU satisfies the corpus CPU's constraints. -/
theorem sat_base_of_W {hd0 stk0 ctr0 : Nat} {C : Table} (h : Sat (cpuAirW hd0 stk0 ctr0) C) :
    Sat (cpuAir hd0 stk0 ctr0) C :=
  ⟨h.1, fun c hc r hr => h.2 c (List.mem_append_left _ hc) r hr⟩

theorem progRowsW_row (heap : List Cell) (W i : Nat) :
    ((progRowsW heap W).getD i []).getD 4 0 = ofN 1 ∨ ((progRowsW heap W).getD i []).getD 4 0 = ofN 0 := by
  rcases Nat.lt_or_ge i (progRowsW heap W).length with h | h
  · rw [List.getD_eq_getElem?_getD (l := progRowsW heap W), List.getElem?_eq_getElem h, Option.getD_some]
    have hm := List.getElem_mem h
    generalize (progRowsW heap W)[i] = row at hm ⊢
    unfold progRowsW at hm
    rcases List.mem_append.1 hm with hm | hm
    · obtain ⟨⟨c, j⟩, _, e⟩ := List.mem_map.1 hm
      rw [← e]; exact .inl rfl
    · rw [List.eq_of_mem_replicate hm]; exact .inr rfl
  · rw [List.getD_eq_getElem?_getD (l := progRowsW heap W), List.getElem?_eq_none h]; exact .inr rfl

theorem witRowsW_row (W i : Nat) :
    ((witRowsW W).getD i []).getD 1 0 = ofN 1 ∨ ((witRowsW W).getD i []).getD 1 0 = ofN 0 := by
  rcases Nat.lt_or_ge i (witRowsW W).length with h | h
  · rw [List.getD_eq_getElem?_getD (l := witRowsW W), List.getElem?_eq_getElem h, Option.getD_some]
    have hm := List.getElem_mem h
    generalize (witRowsW W)[i] = row at hm ⊢
    unfold witRowsW witRowsG at hm
    simp only [List.mem_append, List.mem_map, List.mem_range] at hm
    rcases hm with (⟨j, _, e⟩ | ⟨j, _, e⟩) | hm
    · rw [← e]; exact .inl rfl
    · rw [← e]; exact .inl rfl
    · rw [List.eq_of_mem_replicate hm]; exact .inr rfl
  · rw [List.getD_eq_getElem?_getD (l := witRowsW W), List.getElem?_eq_none h]; exact .inr rfl

/-- A well-formed region's cells point into it. -/
theorem fits_of_WF {ws : List Cell} (hwf : WF ws) : Fits ws := by
  intro c hc
  obtain ⟨i, hi, e⟩ := List.getElem_of_mem hc
  have := hwf i c (by rw [List.getElem?_eq_getElem hi, e])
  rcases cellOK_cases this with rfl | rfl | rfl | ⟨x, y, rfl, hx, hy⟩
  all_goals first
    | exact ⟨by simp only [cellFields]; omega, by simp only [cellFields]; omega⟩
    | exact ⟨Nat.lt_trans hx hi, Nat.lt_trans hy hi⟩

/-- **The witness machine points into its heap.** -/
theorem wMachine_fits {ws : List Cell} (P : Term) (hwf : WF ws) (hne : 0 < ws.length) :
    Fits (wMachine ws P).heap ∧ (wMachine ws P).hd < (wMachine ws P).heap.length ∧
      (wMachine ws P).stk < (wMachine ws P).heap.length := by
  obtain ⟨f1, p1, l1⟩ := build_fits P ws (fits_of_WF hwf)
  show Fits ((build ws P).1 ++ [Cell.app (build ws P).2 (ws.length - 1), Cell.nil]) ∧
    (build ws P).1.length < ((build ws P).1 ++ [Cell.app (build ws P).2 (ws.length - 1), Cell.nil]).length ∧
    (build ws P).1.length + 1 < ((build ws P).1 ++ [Cell.app (build ws P).2 (ws.length - 1), Cell.nil]).length
  have e : (build ws P).1 ++ [Cell.app (build ws P).2 (ws.length - 1), Cell.nil] =
      (build ws P).1 ++ [Cell.app (build ws P).2 (ws.length - 1)] ++ [Cell.nil] := by simp
  rw [e]
  have a1 : (cellFields (Cell.app (build ws P).2 (ws.length - 1))).1 < (build ws P).1.length + 1 ∧
      (cellFields (Cell.app (build ws P).2 (ws.length - 1))).2 < (build ws P).1.length + 1 := by
    simp only [cellFields]; exact ⟨by omega, by omega⟩
  have g1 := fits_push f1 a1
  have a2 : (cellFields Cell.nil).1 < ((build ws P).1 ++ [Cell.app (build ws P).2 (ws.length - 1)]).length + 1 ∧
      (cellFields Cell.nil).2 < ((build ws P).1 ++ [Cell.app (build ws P).2 (ws.length - 1)]).length + 1 := by
    simp only [cellFields]; exact ⟨by omega, by omega⟩
  refine ⟨fits_push g1 a2, ?_, ?_⟩ <;> simp only [List.length_append, List.length_singleton] <;> omega

theorem blank_WF (W : Nat) : WF (List.replicate W Cell.S) := by
  intro i c h
  rw [List.getElem?_replicate] at h
  split at h
  · cases h; rfl
  · cases h

/-- The public cells of a heap past a region, counted. -/
theorem publicW_length (heap : List Cell) (W : Nat) (hl : W ≤ heap.length) :
    (heap.zipIdx.filter fun x => !(x.2 < W)).length + W = heap.length := by
  have e : heap = heap.take W ++ heap.drop W := (List.take_append_drop W heap).symm
  have l1 : (heap.take W).length = W := by rw [List.length_take]; omega
  rw [e, List.zipIdx_append, List.filter_append]
  rw [filter_nil' (fun x hx => by
      obtain ⟨b1, b2, -⟩ := List.mem_zipIdx hx
      simp only [l1] at b1 b2
      simp only [Bool.not_eq_false', decide_eq_true_eq]
      omega)]
  rw [List.filter_eq_self.2 (fun x hx => by
      obtain ⟨b1, b2, -⟩ := List.mem_zipIdx hx
      simp only [l1] at b1 b2
      simp only [Bool.not_eq_true', decide_eq_false_iff_not]
      omega)]
  simp only [List.length_append, List.length_zipIdx, List.length_nil, List.length_take, List.length_drop, l1]
  omega

theorem progRowsW_has {heap : List Cell} {W i : Nat} (hi : i < heap.length) (hp : W ≤ i) :
    ∃ q, q < (progRowsW heap W).length ∧ (progRowsW heap W).getD q [] =
      [ofN i, ofN (cellTag heap[i]), ofN (cellFields heap[i]).1, ofN (cellFields heap[i]).2, ofN 1] := by
  let pub := heap.zipIdx.filter fun x => !(x.2 < W)
  have hm : (heap[i], i) ∈ pub := by
    refine List.mem_filter.2 ⟨?_, ?_⟩
    · have hz : i < heap.zipIdx.length := by rw [List.length_zipIdx]; exact hi
      have := List.getElem_mem hz
      rw [List.getElem_zipIdx] at this
      simpa using this
    · simp only [Bool.not_eq_true', decide_eq_false_iff_not]; omega
  let rows := pub.map fun x => [ofN x.2, ofN (cellTag x.1), ofN (cellFields x.1).1, ofN (cellFields x.1).2, ofN 1]
  have hr : [ofN i, ofN (cellTag heap[i]), ofN (cellFields heap[i]).1, ofN (cellFields heap[i]).2, ofN 1] ∈ rows :=
    List.mem_map.2 ⟨_, hm, rfl⟩
  obtain ⟨q, hq, e⟩ := List.getElem_of_mem hr
  have hlen : rows.length ≤ (progRowsW heap W).length := by
    show rows.length ≤ (rows ++ _).length
    simp
  refine ⟨q, Nat.lt_of_lt_of_le hq hlen, ?_⟩
  show (rows ++ _).getD q [] = _
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hq, List.getElem?_eq_getElem hq, e]
  rfl

theorem progRowsW_length (heap : List Cell) (W : Nat) :
    (heap.zipIdx.filter fun x => !(x.2 < W)).length ≤ (progRowsW heap W).length := by
  unfold progRowsW; simp

theorem witRowsW_get {W q : Nat} (hq : q < W) : (witRowsW W).getD q [] = [ofN q, ofN 1, ofN 0] := by
  have := witRowsG_get (a0 := 0) (N := 0) (W := W) (q := q) (by omega)
  rw [Nat.zero_add, if_neg (by omega)] at this
  exact this

theorem witRowsW_length (W : Nat) : W ≤ (witRowsW W).length := by
  have := witRowsG_length 0 0 W; rw [Nat.zero_add] at this; exact this

section

variable {hd0 stk0 ctr0 : Nat} {heap : List Cell} {W : Nat} {C Mm Pg Wt : Table}
  (h : WitOK hd0 stk0 ctr0 heap W C Mm Pg Wt)
include h

theorem WitOK.senders : ∀ p ∈ witTables hd0 stk0 ctr0 heap W C Mm Pg Wt,
    (p.1.name == "mem") = false → Sender "mem" p := by
  intro p hp hpr
  simp only [witTables, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl
  · refine ⟨fun I hI => ?_, fun r hr I hI hbus => ?_⟩
    · have : cpuIntersW.all (fun I => decide (1 ≤ I.weight)) = true := rfl
      exact of_decide_eq_true (List.all_eq_true.1 this I hI)
    · have hI' : I ∈ cpuInters ∨ I ∈ [⟨"blind_a", 1, .neg (col (BLA + 4)), blindFields BLA⟩,
          ⟨"blind_b", 1, col (BLB + 4), blindFields BLB⟩] := List.mem_append.1 hI
      rcases hI' with hI' | hI'
      · exact cpu_countR ((sat_base_of_W h.cpu).row hr) hr I hI'
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hI'
        rcases hI' with rfl | rfl <;> exact absurd hbus (by decide)
  · exact nomatch hpr
  · refine ⟨fun I hI => by simp only [progAirW, List.mem_cons, List.not_mem_nil, or_false] at hI; rw [hI]; decide,
      fun r hr I hI _ => ?_⟩
    simp only [progAirW, List.mem_cons, List.not_mem_nil, or_false] at hI
    subst hI
    show ((prec 4).eval _).val ≤ 1
    rw [prec_eval h.pgpre hr (by show 4 < 5; decide)]
    rcases progRowsW_row heap W r with e | e <;> rw [show (progAirW heap W).pretrace = progRowsW heap W from rfl, e] <;>
      decide
  · refine ⟨fun I hI => by
        simp only [witAirW, witInters, List.mem_cons, List.not_mem_nil, or_false] at hI
        rcases hI with rfl | rfl <;> decide,
      fun r hr I hI hbus => ?_⟩
    simp only [witAirW, witInters, List.mem_cons, List.not_mem_nil, or_false] at hI
    rcases hI with rfl | rfl
    · show ((prec 1).eval _).val ≤ 1
      rw [prec_eval h.wtpre hr (by show 1 < 3; decide)]
      rcases witRowsW_row W r with e | e <;> rw [show (witAirW W).pretrace = witRowsW W from rfl, e] <;> decide
    · exact absurd hbus (by decide)

/-- **A `mem` message with count `1` is a memory row.** -/
theorem WitOK.memHit {v : List F}
    (hit : ∃ p ∈ witTables hd0 stk0 ctr0 heap W C Mm Pg Wt, (p.1.name == "mem") = false ∧
      ∃ r, r < p.2.h ∧ ∃ I ∈ p.1.inters, I.bus = "mem" ∧
        I.fields.map (fun e => e.eval (p.2.env r)) = v ∧ I.count.eval (p.2.env r) = 1) :
    ∃ m, m < Mm.h ∧ [Mm.main m 0, Mm.main m 1, Mm.main m 2, Mm.main m 3] = v := by
  obtain ⟨p, hp, hpr, m, hm, hne⟩ := bus_hit h.bal h.hts (fun p => p.1.name == "mem") h.senders hit
  simp only [witTables, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl
  · exact nomatch hpr
  · refine ⟨m, hm, ?_⟩
    have hm' : m < Mm.h := hm
    apply Decidable.byContradiction
    intro hv
    apply hne
    simp only [rowSends, memAirC, List.foldr_cons, List.foldr_nil, List.map_cons, List.map_nil, B.col,
      E.eval, env_main0 hm']
    rw [if_neg (fun h' => hv h'.2), if_neg (fun h' => absurd h'.1 (by decide)), add_zero', add_zero']
  · exact nomatch hpr
  · exact nomatch hpr

theorem WitOK.mem_h : Mm.h ≤ 2 ^ 27 := h.two (memAirC, Mm) (by simp [witTables])

/-- **The CPU and memory are a corpus-CPU circuit's.** -/
theorem WitOK.row : RowOK hd0 stk0 ctr0 C Mm :=
  ⟨h.cpu.1, fun _ hr _ => (sat_base_of_W h.cpu).row hr, mem_addrC h.mem, h.mem_h, fun r hr I hI hbus hc =>
    h.memHit ⟨(cpuAirW hd0 stk0 ctr0, C), by simp [witTables], rfl, r, hr, I, List.mem_append_left _ hI, hbus,
      rfl, hc⟩⟩

end

section

variable {V x : Term} {W : Nat} {C Mm Pg Wt : Table}
  (h : WitOK (wMachine (List.replicate W .S) (V ⬝ x)).hd (wMachine (List.replicate W .S) (V ⬝ x)).stk
    (wMachine (List.replicate W .S) (V ⬝ x)).heap.length (wMachine (List.replicate W .S) (V ⬝ x)).heap W C Mm Pg Wt)
  (hW : 0 < W)
include h hW

theorem WitOK.blank_fits : Fits (wMachine (List.replicate W .S) (V ⬝ x)).heap ∧
    (wMachine (List.replicate W .S) (V ⬝ x)).hd < (wMachine (List.replicate W .S) (V ⬝ x)).heap.length ∧
    (wMachine (List.replicate W .S) (V ⬝ x)).stk < (wMachine (List.replicate W .S) (V ⬝ x)).heap.length :=
  wMachine_fits _ (blank_WF W) (by rw [List.length_replicate]; exact hW)

theorem WitOK.blank_len : W ≤ (wMachine (List.replicate W .S) (V ⬝ x)).heap.length := by
  have := (wMachine_public (List.replicate W .S) (List.replicate W .S) (V ⬝ x) rfl).2.2.2.1
  have hl := congrArg List.length this
  rw [List.length_take, List.length_replicate] at hl
  omega

theorem WitOK.heap_lt : (wMachine (List.replicate W .S) (V ⬝ x)).heap.length < P := by
  have e := publicW_length (wMachine (List.replicate W .S) (V ⬝ x)).heap W (h.blank_len hW)
  have p1 := progRowsW_length (wMachine (List.replicate W .S) (V ⬝ x)).heap W
  have p2 := witRowsW_length W
  have hp := h.pgpre.1
  have hw := h.wtpre.1
  have a : Pg.h ≤ 2 ^ 27 := h.two (progAirW (wMachine (List.replicate W .S) (V ⬝ x)).heap W, Pg) (by simp [witTables])
  have b : Wt.h ≤ 2 ^ 27 := h.two (witAirW W, Wt) (by simp [witTables])
  simp only [progAirW, witAirW] at hp hw
  have : P = 2013265921 := rfl
  omega

/-- **A public cell is in memory.** -/
theorem WitOK.pubCell {i : Nat} (hi : i < (wMachine (List.replicate W .S) (V ⬝ x)).heap.length) (hp : W ≤ i) :
    i < Mm.h ∧ (memOf Mm)[i]? = (wMachine (List.replicate W .S) (V ⬝ x)).heap[i]? := by
  obtain ⟨q, hq, e⟩ := progRowsW_has hi hp
  have hqP : q < Pg.h := by rw [h.pgpre.1]; exact hq
  have pv : ∀ j, j < 5 → (prec j).eval (Pg.env q) =
      ((progRowsW (wMachine (List.replicate W .S) (V ⬝ x)).heap W).getD q []).getD j 0 :=
    fun j hj => prec_eval h.pgpre hqP hj
  let hp' := (wMachine (List.replicate W .S) (V ⬝ x)).heap
  have hit := h.memHit (v := [ofN i, ofN (cellTag hp'[i]), ofN (cellFields hp'[i]).1, ofN (cellFields hp'[i]).2])
    ⟨(progAirW (wMachine (List.replicate W .S) (V ⬝ x)).heap W, Pg), by simp [witTables], rfl, q, hqP, _,
      List.mem_cons_self, rfl,
      by simp only [progAirW, List.map_cons, List.map_nil, pv 0 (by decide), pv 1 (by decide), pv 2 (by decide),
        pv 3 (by decide), e]; rfl,
      by show (prec 4).eval _ = 1; rw [pv 4 (by decide), e]; rfl⟩
  obtain ⟨hlt, hget⟩ := h.row.cell hit
  have hP := h.heap_lt hW
  have hf := (h.blank_fits hW).1 _ (List.getElem_mem hi)
  rw [val_ofN (Nat.lt_trans hi hP)] at hlt hget
  rw [cellOf_enc _ (Nat.lt_trans hf.1 hP) (Nat.lt_trans hf.2 hP)] at hget
  exact ⟨hlt, by rw [hget, List.getElem?_eq_getElem hi]⟩

/-- **A region cell is in memory**, well formed. -/
theorem WitOK.regCell {q : Nat} (hq : q < W) :
    q < Mm.h ∧ ∃ cell, (memOf Mm)[q]? = some cell ∧ cellOK q cell = true := by
  have hqW : q < Wt.h := by rw [h.wtpre.1]; exact Nat.lt_of_lt_of_le hq (witRowsW_length W)
  have pv : ∀ j, j < 3 → Wt.pre q j = ((witRowsW W).getD q []).getD j 0 := fun j hj => h.wtpre.2 q j hqW hj
  have e := witRowsW_get hq
  have hact : Wt.pre q 1 = 1 := by rw [pv 1 (by decide), e]; rfl
  obtain ⟨cell, hlt, hget, hok, _⟩ := witCellG (fun c hc q hq => h.wit.cons hc hq)
    (fun q hq hc => h.memHit ⟨(witAirW W, Wt), by simp [witTables], rfl, q, hq, _, List.mem_cons_self, rfl, rfl, hc⟩)
    (mem_addrC h.mem) h.mem_h hqW hact
  have ha : (Wt.pre q 0).val = q := by
    rw [pv 0 (by decide), e]
    have b : Wt.h ≤ 2 ^ 27 := h.two (witAirW W, Wt) (by simp [witTables])
    exact val_ofN (by have : P = 2013265921 := rfl; omega)
  rw [ha] at hlt hget hok
  exact ⟨hlt, cell, hget, hok⟩

theorem WitOK.region_len : ((memOf Mm).take W).length = W := by
  have := (h.regCell (q := W - 1) hW (by omega)).1
  rw [List.length_take, memOf_length]; omega

theorem WitOK.regionWF : WF ((memOf Mm).take W) := by
  intro i c hc
  have hi : i < W := by
    rcases Nat.lt_or_ge i W with h' | h'
    · exact h'
    · rw [List.getElem?_eq_none (by rw [h.region_len hW]; exact h')] at hc; cases hc
  obtain ⟨_, cell, hget, hok⟩ := h.regCell hW hi
  rw [List.getElem?_take, if_pos hi, hget] at hc
  cases hc
  exact hok

/-- **The memory's prefix is the witness machine** of the region it holds. -/
theorem WitOK.heap0 :
    (memOf Mm).take (wMachine (List.replicate W .S) (V ⬝ x)).heap.length =
      (wMachine ((memOf Mm).take W) (V ⬝ x)).heap := by
  have hl : ((memOf Mm).take W).length = (List.replicate W Cell.S).length := by
    rw [List.length_replicate]; exact h.region_len hW
  obtain ⟨_, _, hlen, htake, hpub⟩ := wMachine_public ((memOf Mm).take W) (List.replicate W .S) (V ⬝ x) hl
  apply List.ext_getElem?
  intro i
  rw [List.getElem?_take]
  split
  · next hi =>
    rcases Nat.lt_or_ge i W with hr | hr
    · have ht := congrArg (fun l => l[i]?) htake
      simp only [List.getElem?_take, if_pos (show i < ((memOf Mm).take W).length by rw [h.region_len hW]; exact hr)] at ht
      rw [ht]
      first | rw [if_pos hr] | rw [List.getElem?_take, if_pos hr]
    · rw [(h.pubCell hW hi hr).2, hpub i (by rw [h.region_len hW]; exact hr)]
  · next hi =>
    rw [List.getElem?_eq_none (by rw [hlen]; omega)]

/-- **Soundness of the hidden-term circuit**, over its tables: the region
    the memory holds is well formed and its witness realizes the atom. -/
theorem WitOK.sound : ∃ w, witnessOf ((memOf Mm).take W) = some w ∧ Real (.atom V x) w := by
  have hl : ((memOf Mm).take W).length = (List.replicate W Cell.S).length := by
    rw [List.length_replicate]; exact h.region_len hW
  obtain ⟨hhd, hstk, hlen, _, _⟩ := wMachine_public ((memOf Mm).take W) (List.replicate W .S) (V ⬝ x) hl
  obtain ⟨_, bhd, bstk⟩ := h.blank_fits hW
  have hP := h.heap_lt hW
  have hA := h.row.acceptsFrom (fun r hr => inst_zero ((sat_base_of_W h.cpu).row hr) hr) (m0 := wMachine ((memOf Mm).take W) (V ⬝ x)) (h.heap0 hW) hhd hstk hlen
    ⟨by omega, by omega, hP⟩
  -- the last row is `HK1`: `K` at the head over a nil
  have h0 : 0 < C.h := h.cpu.1
  have hl' : C.h - 1 < C.h := by omega
  obtain ⟨k, hk, hsel⟩ := kind_of ((sat_base_of_W h.cpu).row hl') hl'
  have hK : IsKind C (C.h - 1) k := ⟨hk, hsel⟩
  have hla : C.env (C.h - 1) .last = 1 := by simp [env_last]; omega
  have h1 := h.cpu.2 (whenLast (eq sHK1 one)) (by simp [cpuAirW, cpuConsW]) (C.h - 1) hl'
  simp only [B.whenLast, B.eq, E.eval, hla, one_mul', B.one, B.c, ofN_one, sHK1, B.col, env_main0 hl'] at h1
  have hk5 : k = 5 := by
    have := hsel 5 (by decide)
    rw [sub_eq_zero h1] at this
    by_cases e5 : 5 = k
    · exact e5.symm
    · rw [if_neg e5] at this; exact absurd this (by decide)
  subst hk5
  have r0 : rd (memOf Mm) (C.main (C.h - 1) CTR).val (C.main (C.h - 1) HD).val = some .K :=
    h.row.read hl' hK (j := 0) (by decide) rfl
  have r1 : rd (memOf Mm) (C.main (C.h - 1) CTR).val (C.main (C.h - 1) STK).val = some .nil :=
    h.row.read hl' hK (j := 1) (by decide) rfl
  exact wit_realizes (h.regionWF hW) (by rw [h.region_len hW]; exact hW) hA r0 r1

end

/-- The witness circuit is guarded, for every statement. -/
theorem wit_guarded (V x : Term) (W : Nat) : ∀ A ∈ witAirs V x W, A.cons.all E.guarded = true := by
  intro A hA
  simp only [witAirs, List.mem_cons, List.not_mem_nil, or_false] at hA
  rcases hA with rfl | rfl | rfl | rfl <;> rfl

/-- Acceptance of the witness circuit's data is `WitOK`. -/
theorem witOK_of {V x : Term} {W : Nat} {ts : List Table} (h : Accepted (witAirs V x W) ts) :
    ∃ C Mm Pg Wt, ts = [C, Mm, Pg, Wt] ∧
      WitOK (wMachine (List.replicate W .S) (V ⬝ x)).hd (wMachine (List.replicate W .S) (V ⬝ x)).stk
        (wMachine (List.replicate W .S) (V ⬝ x)).heap.length (wMachine (List.replicate W .S) (V ⬝ x)).heap W
        C Mm Pg Wt := by
  obtain ⟨hl, hsat, hbal, hht, htwo⟩ := h
  match ts, hl with
  | [C, Mm, Pg, Wt], _ =>
    have mem : ∀ A T, (A, T) ∈ (witAirs V x W).zip [C, Mm, Pg, Wt] →
        Sat A T ∧ (A.pre = 0 ∨ PreIs A T) := fun A T hm => hsat (A, T) hm
    have z : (witAirs V x W).zip [C, Mm, Pg, Wt] =
        witTables (wMachine (List.replicate W .S) (V ⬝ x)).hd (wMachine (List.replicate W .S) (V ⬝ x)).stk
          (wMachine (List.replicate W .S) (V ⬝ x)).heap.length (wMachine (List.replicate W .S) (V ⬝ x)).heap W
          C Mm Pg Wt := rfl
    rw [z] at mem hbal hht htwo
    have pre : ∀ A T, (A, T) ∈ witTables (wMachine (List.replicate W .S) (V ⬝ x)).hd
          (wMachine (List.replicate W .S) (V ⬝ x)).stk (wMachine (List.replicate W .S) (V ⬝ x)).heap.length
          (wMachine (List.replicate W .S) (V ⬝ x)).heap W C Mm Pg Wt → A.pre ≠ 0 → PreIs A T := by
      intro A T hm hp
      rcases (mem A T hm).2 with h0 | h0
      · exact absurd h0 hp
      · exact h0
    refine ⟨C, Mm, Pg, Wt, rfl, ⟨(mem _ _ (by simp [witTables])).1, (mem _ _ (by simp [witTables])).1,
      (mem _ _ (by simp [witTables])).1,
      pre _ _ (by simp [witTables]) (by show (5 : Nat) ≠ 0; decide),
      pre _ _ (by simp [witTables]) (by show (3 : Nat) ≠ 0; decide), hbal, hht, htwo⟩⟩

/-- **Soundness of the hidden-term circuit**: an accepted proof's memory
    holds, in its first `W` cells, a region whose witness realizes the
    atom `V x`. -/
theorem witExport_sound {V x : Term} {W : Nat} (hW : 0 < W) {Rs : List AirD} {ts : List Table}
    (hs : sameAirsB Rs (witAirs V x W) = true) (h : AcceptedP Rs ts) :
    ∃ C Mm Pg Wt, ts = [C, Mm, Pg, Wt] ∧ ∃ w, witnessOf ((memOf Mm).take W) = some w ∧ Real (.atom V x) w := by
  have hacc := accepted_transfer hs ((acceptedP_iff_of (wit_guarded V x W) hs ts).1 h)
  obtain ⟨C, Mm, Pg, Wt, rfl, hok⟩ := witOK_of hacc
  exact ⟨C, Mm, Pg, Wt, rfl, hok.sound hW⟩

end Circuit
