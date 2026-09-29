import Ski.Circuit.SudAir
import Ski.Circuit.WitComplete

/-!
# Soundness of the Sudoku circuit

Tables accepted for the Sudoku circuit of a puzzle with well-formed clues
hold, at the input addresses of their memory, a grid that solves the
puzzle (`sudExport_sound`, by `Sudoku.sudoku_sound`).
-/

namespace Circuit

open B Air Stmt Mach Sudoku SudokuText

-- ---------------------------------------------------------------------------
-- The statement machine's fields are small
-- ---------------------------------------------------------------------------

/-- Every cell's fields below the heap's length or a bound `Bd` (the
    markers' atoms). -/
def FitsB (Bd : Nat) (h : List Cell) : Prop :=
  ∀ c ∈ h, (cellFields c).1 < max h.length Bd ∧ (cellFields c).2 < max h.length Bd

theorem fitsB_push {Bd : Nat} {h : List Cell} {c : Cell} (hh : FitsB Bd h)
    (hc : (cellFields c).1 < max (h.length + 1) Bd ∧ (cellFields c).2 < max (h.length + 1) Bd) :
    FitsB Bd (h ++ [c]) := by
  intro c' hc'
  rw [List.length_append, List.length_singleton]
  rcases List.mem_append.1 hc' with hc' | hc'
  · have := hh c' hc'
    have m : max h.length Bd ≤ max (h.length + 1) Bd :=
      Nat.max_le.2 ⟨Nat.le_trans (Nat.le_succ _) (Nat.le_max_left _ _), Nat.le_max_right _ _⟩
    exact ⟨Nat.lt_of_lt_of_le this.1 m, Nat.lt_of_lt_of_le this.2 m⟩
  · rw [List.mem_singleton.1 hc']; exact hc

theorem lt_max_left {a b c : Nat} (h : a < b) : a < max b c := Nat.lt_of_lt_of_le h (Nat.le_max_left _ _)
theorem lt_max_right {a b c : Nat} (h : a < c) : a < max b c := Nat.lt_of_lt_of_le h (Nat.le_max_right _ _)

theorem pbuild_fitsB (bound Bd : Nat) : ∀ (t : OTerm) (h : List Cell), FitsB Bd h →
    (∀ x, Occ x t → (x < bound → slotPtr x < h.length) ∧ (¬ x < bound → x < Bd)) →
    FitsB Bd (pbuild bound h t).1 ∧ (pbuild bound h t).2 < (pbuild bound h t).1.length ∧
      h.length ≤ (pbuild bound h t).1.length
  | .S, h, hf, _ => ⟨fitsB_push hf ⟨lt_max_left (Nat.succ_pos _), lt_max_left (Nat.succ_pos _)⟩,
      by simp [pbuild, alloc], by simp [pbuild, alloc]⟩
  | .K, h, hf, _ => ⟨fitsB_push hf ⟨lt_max_left (Nat.succ_pos _), lt_max_left (Nat.succ_pos _)⟩,
      by simp [pbuild, alloc], by simp [pbuild, alloc]⟩
  | .I, h, hf, _ => ⟨fitsB_push hf ⟨lt_max_left (Nat.succ_pos _), lt_max_left (Nat.succ_pos _)⟩,
      by simp [pbuild, alloc], by simp [pbuild, alloc]⟩
  | .var x, h, hf, hv => by
    have := hv x (.var x)
    by_cases hx : x < bound
    · simp only [pbuild, if_pos hx]
      exact ⟨hf, this.1 hx, Nat.le_refl _⟩
    · simp only [pbuild, if_neg hx, alloc]
      refine ⟨fitsB_push hf ⟨lt_max_right (this.2 hx), lt_max_left (Nat.succ_pos _)⟩, ?_, ?_⟩ <;>
        simp
  | .app f a, h, hf, hv => by
    obtain ⟨f1, p1, l1⟩ := pbuild_fitsB bound Bd f h hf (fun x hx => hv x (.left _ hx))
    obtain ⟨f2, p2, l2⟩ := pbuild_fitsB bound Bd a (pbuild bound h f).1 f1
      (fun x hx => ⟨fun hb => Nat.lt_of_lt_of_le ((hv x (.right _ hx)).1 hb) l1, (hv x (.right _ hx)).2⟩)
    show FitsB Bd ((pbuild bound (pbuild bound h f).1 a).1 ++
        [.app (pbuild bound h f).2 (pbuild bound (pbuild bound h f).1 a).2]) ∧
      (pbuild bound (pbuild bound h f).1 a).1.length <
        ((pbuild bound (pbuild bound h f).1 a).1 ++ [_]).length ∧
      h.length ≤ ((pbuild bound (pbuild bound h f).1 a).1 ++ [_]).length
    rw [List.length_append, List.length_singleton]
    refine ⟨fitsB_push f2 ⟨lt_max_left ?_, lt_max_left ?_⟩, Nat.lt_succ_self _, ?_⟩
    · show (pbuild bound h f).2 < _; omega
    · show (pbuild bound (pbuild bound h f).1 a).2 < _; omega
    · omega

/-- **The statement machine's fields are small**: below its heap's length
    or `733`, the markers' bound. -/
theorem stmt_fitsB {ρ : Nat → Bool} {e : BExpr} (hb : Bounded 729 e) :
    FitsB 733 (stmtMachine ρ 729 e ACC REJ).heap ∧
      (stmtMachine ρ 729 e ACC REJ).hd < (stmtMachine ρ 729 e ACC REJ).heap.length ∧
      (stmtMachine ρ 729 e ACC REJ).stk < (stmtMachine ρ 729 e ACC REJ).heap.length ∧
      732 ≤ (stmtMachine ρ 729 e ACC REJ).heap.length := by
  have hs : FitsB 733 (slotHeap ρ 729) := by
    intro c hc
    rw [slotHeap_length]
    unfold slotHeap at hc
    rcases List.mem_append.1 hc with hc | hc
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl <;> exact ⟨by simp [cellFields], by simp [cellFields]⟩
    · obtain ⟨n, _, rfl⟩ := List.mem_map.1 hc
      cases ρ n <;> exact ⟨by simp [cellFields], by simp [cellFields]⟩
  have hv : ∀ x, Occ x (probeTerm e ACC REJ) → (x < 729 + 2 → slotPtr x < (slotHeap ρ 729).length) ∧
      (¬ x < 729 + 2 → x < 733) := by
    intro x hx
    rw [slotHeap_length]
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rcases x with _ | _ | x
      · show 0 < _; omega
      · show 2 < _; omega
      · show x + 3 < _; omega
    · unfold probeTerm at hx
      cases hx with
      | left _ h1 =>
        cases h1 with
        | left _ h2 => exact absurd (compile_occ hb x h2) h
        | right _ h2 => cases h2; decide
      | right _ h1 => cases h1; decide
  obtain ⟨f1, p1, l1⟩ := pbuild_fitsB (729 + 2) 733 _ _ hs hv
  rw [slotHeap_length] at l1
  show FitsB 733 ((pbuild (729 + 2) (slotHeap ρ 729) (probeTerm e ACC REJ)).1 ++ [Cell.nil]) ∧
    (pbuild (729 + 2) (slotHeap ρ 729) (probeTerm e ACC REJ)).2 <
      ((pbuild (729 + 2) (slotHeap ρ 729) (probeTerm e ACC REJ)).1 ++ [Cell.nil]).length ∧
    (pbuild (729 + 2) (slotHeap ρ 729) (probeTerm e ACC REJ)).1.length <
      ((pbuild (729 + 2) (slotHeap ρ 729) (probeTerm e ACC REJ)).1 ++ [Cell.nil]).length ∧
    732 ≤ ((pbuild (729 + 2) (slotHeap ρ 729) (probeTerm e ACC REJ)).1 ++ [Cell.nil]).length
  rw [List.length_append, List.length_singleton]
  refine ⟨fitsB_push f1 ⟨lt_max_left (by simp [cellFields]), lt_max_left (by simp [cellFields])⟩, by omega,
    by omega, by omega⟩

/-- The statement machine begins with its slots. -/
theorem stmt_take (ρ : Nat → Bool) (N : Nat) (e : BExpr) (acc rej : Nat) :
    (stmtMachine ρ N e acc rej).heap.take (N + 3) = slotHeap ρ N := by
  obtain ⟨cs, p, e1, _⟩ := pbuild_shape (N + 2) (probeTerm e acc rej) (slotHeap ρ N) (slotHeap ρ N) rfl
  show ((pbuild (N + 2) (slotHeap ρ N) (probeTerm e acc rej)).1 ++ [Cell.nil]).take (N + 3) = _
  rw [e1, List.append_assoc, ← slotHeap_length ρ N, List.take_left']
  rfl

/-- The Sudoku circuit's four tables. -/
def sudTables (hd0 stk0 ctr0 : Nat) (heap : List Cell) (C Mm Pg Wt : Table) : List (AirD × Table) :=
  [(cpuAirS hd0 stk0 ctr0 ACC, C), (memAirC, Mm), (progAirS heap, Pg), (witAirS, Wt)]

/-- **What an accepted proof of the Sudoku circuit gives.** -/
structure SudOK (hd0 stk0 ctr0 : Nat) (heap : List Cell) (C Mm Pg Wt : Table) : Prop where
  cpu : Sat (cpuAirS hd0 stk0 ctr0 ACC) C
  mem : Sat memAirC Mm
  wit : Sat witAirS Wt
  pgpre : PreIs (progAirS heap) Pg
  wtpre : PreIs witAirS Wt
  bal : Balanced (sudTables hd0 stk0 ctr0 heap C Mm Pg Wt)
  hts : HeightsOK (sudTables hd0 stk0 ctr0 heap C Mm Pg Wt)
  two : TwoAdic (sudTables hd0 stk0 ctr0 heap C Mm Pg Wt)

theorem sat_base_of_S {hd0 stk0 ctr0 : Nat} {C : Table} (h : Sat (cpuAirS hd0 stk0 ctr0 ACC) C) :
    Sat (cpuAir hd0 stk0 ctr0) C :=
  ⟨h.1, fun c hc r hr => h.2 c (List.mem_append_left _ hc) r hr⟩

theorem progRowsS_row (heap : List Cell) (i : Nat) :
    ((progRowsS heap).getD i []).getD 4 0 = ofN 1 ∨ ((progRowsS heap).getD i []).getD 4 0 = ofN 0 := by
  rcases Nat.lt_or_ge i (progRowsS heap).length with h | h
  · rw [List.getD_eq_getElem?_getD (l := progRowsS heap), List.getElem?_eq_getElem h, Option.getD_some]
    have hm := List.getElem_mem h
    generalize (progRowsS heap)[i] = row at hm ⊢
    unfold progRowsS at hm
    rcases List.mem_append.1 hm with hm | hm
    · obtain ⟨⟨c, j⟩, _, e⟩ := List.mem_map.1 hm
      rw [← e]; exact .inl rfl
    · rw [List.eq_of_mem_replicate hm]; exact .inr rfl
  · rw [List.getD_eq_getElem?_getD (l := progRowsS heap), List.getElem?_eq_none h]; exact .inr rfl

theorem witRowsS_get {n : Nat} (hn : n < 729) : witRowsS.getD n [] = [ofN (3 + n), ofN 1] := by
  unfold witRowsS
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp; omega), List.getElem?_map,
    List.getElem?_range hn]
  rfl

theorem witRowsS_row (i : Nat) : (witRowsS.getD i []).getD 1 0 = ofN 1 ∨ (witRowsS.getD i []).getD 1 0 = ofN 0 := by
  rcases Nat.lt_or_ge i 729 with h | h
  · rw [witRowsS_get h]; exact .inl rfl
  · rcases Nat.lt_or_ge i witRowsS.length with h' | h'
    · unfold witRowsS at *
      rw [List.getD_eq_getElem?_getD (a := ([] : List F)), List.getElem?_append_right (by simp; omega),
        List.getElem?_replicate]
      simp only [List.length_append, List.length_map, List.length_range, List.length_replicate] at h' ⊢
      rw [if_pos (by omega)]; exact .inr rfl
    · rw [List.getD_eq_getElem?_getD (a := ([] : List F)), List.getElem?_eq_none h']; exact .inr rfl

section

variable {hd0 stk0 ctr0 : Nat} {heap : List Cell} {C Mm Pg Wt : Table}
  (h : SudOK hd0 stk0 ctr0 heap C Mm Pg Wt)
include h

theorem SudOK.senders : ∀ p ∈ sudTables hd0 stk0 ctr0 heap C Mm Pg Wt,
    (p.1.name == "mem") = false → Sender "mem" p := by
  intro p hp hpr
  simp only [sudTables, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl
  · refine ⟨fun I hI => ?_, fun r hr I hI hbus => ?_⟩
    · have : cpuIntersW.all (fun I => decide (1 ≤ I.weight)) = true := rfl
      exact of_decide_eq_true (List.all_eq_true.1 this I hI)
    · rcases List.mem_append.1 hI with hI' | hI'
      · exact cpu_countR ((sat_base_of_S h.cpu).row hr) hr I hI'
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hI'
        rcases hI' with rfl | rfl <;> exact absurd hbus (by decide)
  · exact nomatch hpr
  · refine ⟨fun I hI => by simp only [progAirS, List.mem_cons, List.not_mem_nil, or_false] at hI; rw [hI]; decide,
      fun r hr I hI _ => ?_⟩
    simp only [progAirS, List.mem_cons, List.not_mem_nil, or_false] at hI
    subst hI
    show ((prec 4).eval _).val ≤ 1
    rw [prec_eval h.pgpre hr (by show 4 < 5; decide)]
    rcases progRowsS_row heap r with e | e <;> rw [show (progAirS heap).pretrace = progRowsS heap from rfl, e] <;>
      decide
  · refine ⟨fun I hI => by
        simp only [witAirS, witIntersS, List.mem_cons, List.not_mem_nil, or_false] at hI
        rcases hI with rfl | rfl <;> decide,
      fun r hr I hI hbus => ?_⟩
    simp only [witAirS, witIntersS, List.mem_cons, List.not_mem_nil, or_false] at hI
    rcases hI with rfl | rfl
    · exact absurd hbus (by decide)
    · show ((prec 1).eval _).val ≤ 1
      rw [prec_eval h.wtpre hr (by show 1 < 2; decide)]
      rcases witRowsS_row r with e | e <;> rw [show witAirS.pretrace = witRowsS from rfl, e] <;> decide

/-- **A `mem` message with count `1` is a memory row.** -/
theorem SudOK.memHit {v : List F}
    (hit : ∃ p ∈ sudTables hd0 stk0 ctr0 heap C Mm Pg Wt, (p.1.name == "mem") = false ∧
      ∃ r, r < p.2.h ∧ ∃ I ∈ p.1.inters, I.bus = "mem" ∧
        I.fields.map (fun e => e.eval (p.2.env r)) = v ∧ I.count.eval (p.2.env r) = 1) :
    ∃ m, m < Mm.h ∧ [Mm.main m 0, Mm.main m 1, Mm.main m 2, Mm.main m 3] = v := by
  obtain ⟨p, hp, hpr, m, hm, hne⟩ := bus_hit h.bal h.hts (fun p => p.1.name == "mem") h.senders hit
  simp only [sudTables, List.mem_cons, List.not_mem_nil, or_false] at hp
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

theorem SudOK.mem_h : Mm.h ≤ 2 ^ 27 := h.two (memAirC, Mm) (by simp [sudTables])

theorem SudOK.row : RowOK hd0 stk0 ctr0 C Mm :=
  ⟨h.cpu.1, fun _ hr _ => (sat_base_of_S h.cpu).row hr, mem_addrC h.mem, h.mem_h, fun r hr I hI hbus hc =>
    h.memHit ⟨(cpuAirS hd0 stk0 ctr0 ACC, C), by simp [sudTables], rfl, r, hr, I, List.mem_append_left _ hI, hbus,
      rfl, hc⟩⟩

/-- **An input is a Scott Boolean in memory.** -/
theorem SudOK.input {n : Nat} (hn : n < 729) :
    3 + n < Mm.h ∧ ((memOf Mm)[3 + n]? = some .K ∨ (memOf Mm)[3 + n]? = some (.app 0 1)) := by
  have hnW : n < Wt.h := by
    rw [h.wtpre.1]; show n < witRowsS.length; unfold witRowsS
    simp only [List.length_append, List.length_map, List.length_range, List.length_replicate]; omega
  have pv : ∀ j, j < 2 → (prec j).eval (Wt.env n) = (witRowsS.getD n []).getD j 0 :=
    fun j hj => prec_eval h.wtpre hnW hj
  have e := witRowsS_get hn
  have ev : ∀ c, (col c).eval (Wt.env n) = Wt.main n c := fun c => env_main0 hnW
  -- the bit is a bit
  have hb := h.wit.2 (B.bool (col 0)) (List.mem_cons_of_mem _ List.mem_cons_self) n hnW
  simp only [B.bool, E.eval, ev, B.one, B.c, ofN_one] at hb
  have hit := h.memHit (v := [ofN (3 + n), ofN 3 - Wt.main n 0 * ofN 2, ofN 0, 1 - Wt.main n 0])
    ⟨(witAirS, Wt), by simp [sudTables], rfl, n, hnW, _, List.mem_cons_of_mem _ List.mem_cons_self, rfl,
      by simp only [witIntersS, List.map_cons, List.map_nil, E.eval, pv 0 (by decide), e, ev, B.c, B.zero, B.one, ofN_one]
         rfl,
      by show (prec 1).eval _ = 1; rw [pv 1 (by decide), e]; rfl⟩
  obtain ⟨hlt, hget⟩ := h.row.cell hit
  have hP : 3 + n < P := Nat.lt_of_lt_of_le (Nat.add_lt_add_left hn 3) (by decide)
  rw [val_ofN hP] at hlt hget
  refine ⟨hlt, ?_⟩
  rcases bit_of hb with hb | hb <;> rw [hb] at hget
  · right; rw [hget]; rfl
  · left; rw [hget]; rfl

end

theorem progRowsS_has {heap : List Cell} {i : Nat} (hi : i < heap.length) (hp : ¬ (3 ≤ i ∧ i < 3 + 729)) :
    ∃ q, q < (progRowsS heap).length ∧ (progRowsS heap).getD q [] =
      [ofN i, ofN (cellTag heap[i]), ofN (cellFields heap[i]).1, ofN (cellFields heap[i]).2, ofN 1] := by
  let pub := heap.zipIdx.filter fun x => !(3 ≤ x.2 && x.2 < 3 + 729)
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
  have hlen : rows.length ≤ (progRowsS heap).length := by
    show rows.length ≤ (rows ++ _).length
    simp
  refine ⟨q, Nat.lt_of_lt_of_le hq hlen, ?_⟩
  show (rows ++ _).getD q [] = _
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hq, List.getElem?_eq_getElem hq, e]
  rfl

theorem progRowsS_length (heap : List Cell) :
    (heap.zipIdx.filter fun x => !(3 ≤ x.2 && x.2 < 3 + 729)).length ≤ (progRowsS heap).length := by
  unfold progRowsS; simp

section

variable {e : BExpr} {C Mm Pg Wt : Table}
  (h : SudOK (stmtMachine (fun _ => false) 729 e ACC REJ).hd (stmtMachine (fun _ => false) 729 e ACC REJ).stk
    (stmtMachine (fun _ => false) 729 e ACC REJ).heap.length (stmtMachine (fun _ => false) 729 e ACC REJ).heap
    C Mm Pg Wt) (hb : Bounded 729 e)
include h hb

theorem SudOK.heap_lt : (stmtMachine (fun _ => false) 729 e ACC REJ).heap.length < P := by
  obtain ⟨_, _, _, h732⟩ := stmt_fitsB (ρ := fun _ => false) hb
  have eq := public_length (stmtMachine (fun _ => false) 729 e ACC REJ).heap 729 0 (by omega)
  have p1 := progRowsS_length (stmtMachine (fun _ => false) 729 e ACC REJ).heap
  have hp := h.pgpre.1
  have a : Pg.h ≤ 2 ^ 27 := h.two (progAirS (stmtMachine (fun _ => false) 729 e ACC REJ).heap, Pg) (by simp [sudTables])
  simp only [progAirS] at hp
  have : P = 2013265921 := rfl
  have eq' : ((stmtMachine (fun _ => false) 729 e ACC REJ).heap.zipIdx.filter
      fun x => !(3 ≤ x.2 && x.2 < 3 + 729)).length + 729 = (stmtMachine (fun _ => false) 729 e ACC REJ).heap.length :=
    eq
  omega

/-- **A public cell is in memory.** -/
theorem SudOK.pubCell {i : Nat} (hi : i < (stmtMachine (fun _ => false) 729 e ACC REJ).heap.length)
    (hp : ¬ (3 ≤ i ∧ i < 3 + 729)) :
    i < Mm.h ∧ (memOf Mm)[i]? = (stmtMachine (fun _ => false) 729 e ACC REJ).heap[i]? := by
  obtain ⟨q, hq, e'⟩ := progRowsS_has hi hp
  have hqP : q < Pg.h := by rw [h.pgpre.1]; exact hq
  have pv : ∀ j, j < 5 → (prec j).eval (Pg.env q) =
      ((progRowsS (stmtMachine (fun _ => false) 729 e ACC REJ).heap).getD q []).getD j 0 :=
    fun j hj => prec_eval h.pgpre hqP hj
  let hp' := (stmtMachine (fun _ => false) 729 e ACC REJ).heap
  have hit := h.memHit (v := [ofN i, ofN (cellTag hp'[i]), ofN (cellFields hp'[i]).1, ofN (cellFields hp'[i]).2])
    ⟨(progAirS (stmtMachine (fun _ => false) 729 e ACC REJ).heap, Pg), by simp [sudTables], rfl, q, hqP, _,
      List.mem_cons_self, rfl,
      by simp only [progAirS, List.map_cons, List.map_nil, pv 0 (by decide), pv 1 (by decide), pv 2 (by decide),
        pv 3 (by decide), e']; rfl,
      by show (prec 4).eval _ = 1; rw [pv 4 (by decide), e']; rfl⟩
  obtain ⟨hlt, hget⟩ := h.row.cell hit
  have hP := h.heap_lt hb
  obtain ⟨hf0, _, _, _⟩ := stmt_fitsB (ρ := fun _ => false) hb
  have hf := hf0 _ (List.getElem_mem hi)
  have hmx : max (stmtMachine (fun _ => false) 729 e ACC REJ).heap.length 733 < P :=
    Nat.max_lt.2 ⟨hP, by decide⟩
  rw [val_ofN (Nat.lt_trans hi hP)] at hlt hget
  rw [cellOf_enc _ (Nat.lt_trans hf.1 hmx) (Nat.lt_trans hf.2 hmx)] at hget
  exact ⟨hlt, by rw [hget, List.getElem?_eq_getElem hi]⟩

/-- The inputs the memory holds: input `n` set when its cell is `K`. -/
def bitsS (Mm : Table) (n : Nat) : Bool := (memOf Mm)[3 + n]? == some .K

omit h hb in
theorem slot_get {ρ : Nat → Bool} {n : Nat} (hn : n < 729) :
    (slotHeap ρ 729)[3 + n]? = some (if ρ n then .K else .app 0 1) := by
  unfold slotHeap
  rw [List.getElem?_append_right (by simp), show 3 + n - ([Cell.K, Cell.I, Cell.app 0 1] : List Cell).length = n by simp,
    List.getElem?_map, List.getElem?_range hn]
  rfl

/-- **The memory's prefix is the statement machine** of the inputs it holds. -/
theorem SudOK.heap0 :
    (memOf Mm).take (stmtMachine (fun _ => false) 729 e ACC REJ).heap.length =
      (stmtMachine (bitsS Mm) 729 e ACC REJ).heap := by
  obtain ⟨_, _, hlen, hpub⟩ := stmtMachine_public (bitsS Mm) (fun _ => false) 729 e ACC REJ
  have htk := stmt_take (bitsS Mm) 729 e ACC REJ
  obtain ⟨_, _, _, h732⟩ := stmt_fitsB (ρ := fun _ => false) hb
  apply List.ext_getElem?
  intro i
  rw [List.getElem?_take]
  split
  · next hi =>
    by_cases hp : 3 ≤ i ∧ i < 3 + 729
    · have hn : i - 3 < 729 := by omega
      have e3 : 3 + (i - 3) = i := by omega
      have ht := congrArg (fun l => l[i]?) htk
      simp only [List.getElem?_take, if_pos (show i < 729 + 3 by omega)] at ht
      rw [ht, ← e3, slot_get hn]
      obtain ⟨_, hK⟩ := h.input hn
      unfold bitsS
      rcases hK with hK | hK <;> rw [hK] <;> rfl
    · have hor : i < 3 ∨ 729 + 3 ≤ i := by
        rcases Nat.lt_or_ge i 3 with h3 | h3
        · exact .inl h3
        · exact .inr (Nat.le_of_not_lt (fun hlt => hp ⟨h3, by omega⟩))
      rw [(h.pubCell hb hi hp).2, hpub i hor]
  · next hi =>
    rw [List.getElem?_eq_none (by rw [hlen]; omega)]

/-- **The table runs the statement machine** of the inputs memory holds,
    and its last row reads the accepting marker at the head. -/
theorem SudOK.accepts :
    AcceptsFrom (memOf Mm) (stmtMachine (bitsS Mm) 729 e ACC REJ) C.h (rowOf C) ∧
      rd (memOf Mm) (rowOf C (C.h - 1)).ctr (rowOf C (C.h - 1)).hd = some (.atom ACC) := by
  obtain ⟨hhd, hstk, hlen, _⟩ := stmtMachine_public (bitsS Mm) (fun _ => false) 729 e ACC REJ
  obtain ⟨_, bhd, bstk, _⟩ := stmt_fitsB (ρ := fun _ => false) hb
  have hP := h.heap_lt hb
  have hA := h.row.acceptsFrom (fun r hr => inst_zero ((sat_base_of_S h.cpu).row hr) hr) (m0 := stmtMachine (bitsS Mm) 729 e ACC REJ)
    (h.heap0 hb) hhd hstk hlen
    ⟨Nat.lt_trans bhd hP, Nat.lt_trans bstk hP, hP⟩
  refine ⟨hA, ?_⟩
  -- the last row is `HA`, its head the atom `ACC`
  have h0 : 0 < C.h := h.cpu.1
  have hl' : C.h - 1 < C.h := Nat.sub_lt h0 (by decide)
  obtain ⟨k, hk, hsel⟩ := kind_of ((sat_base_of_S h.cpu).row hl') hl'
  have hK : IsKind C (C.h - 1) k := ⟨hk, hsel⟩
  have hla : C.env (C.h - 1) .last = 1 := by simp [env_last]; omega
  have h1 := h.cpu.2 (whenLast (eq sHA one)) (by simp [cpuAirS, cpuConsS]) (C.h - 1) hl'
  simp only [B.whenLast, B.eq, E.eval, hla, one_mul', B.one, B.c, ofN_one, sHA, B.col, env_main0 hl'] at h1
  have h2 := h.cpu.2 (whenLast (eq (fld 0) (c ACC))) (by simp [cpuAirS, cpuConsS]) (C.h - 1) hl'
  simp only [B.whenLast, B.eq, E.eval, hla, one_mul', B.c, fld, B.col, env_main0 hl'] at h2
  have hk10 : k = 10 := by
    have := hsel 10 (by decide)
    rw [sub_eq_zero h1] at this
    by_cases e10 : 10 = k
    · exact e10.symm
    · rw [if_neg e10] at this; exact absurd this (by decide)
  subst hk10
  have r0 := h.row.read hl' hK (j := 0) (by decide) rfl
  rw [show FLD + 2 * 0 = FLD + 0 from rfl, sub_eq_zero h2] at r0
  exact r0

end

/-- **Soundness of the Sudoku circuit**: an accepted proof's memory holds,
    at addresses `3` to `731`, a grid that solves the puzzle. -/
theorem SudOK.sound {puzzle : List Nat} (hc : CluesOK (cluesOf puzzle)) {C Mm Pg Wt : Table}
    (h : SudOK (stmtMachine (fun _ => false) 729 (sudokuExpr (cluesOf puzzle)) ACC REJ).hd
      (stmtMachine (fun _ => false) 729 (sudokuExpr (cluesOf puzzle)) ACC REJ).stk
      (stmtMachine (fun _ => false) 729 (sudokuExpr (cluesOf puzzle)) ACC REJ).heap.length
      (stmtMachine (fun _ => false) 729 (sudokuExpr (cluesOf puzzle)) ACC REJ).heap C Mm Pg Wt) :
    Solves (cluesOf puzzle) (gridOf (bitsS Mm)) := by
  obtain ⟨hA, hi⟩ := h.accepts (bounded_sudoku hc)
  exact sudoku_sound hc (by decide) (by decide) (by decide) hA hi

/-- The Sudoku circuit's tables are guarded, for every machine. -/
theorem sudS_guarded (hd0 stk0 ctr0 : Nat) (heap : List Cell) :
    ∀ A ∈ [cpuAirS hd0 stk0 ctr0 ACC, memAirC, progAirS heap, witAirS], A.cons.all E.guarded = true := by
  intro A hA
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hA
  rcases hA with rfl | rfl | rfl | rfl <;> rfl

theorem sudAirs_eq (puzzle : List Nat) :
    sudAirs puzzle =
      let m := stmtMachine (fun _ => false) 729 (sudokuExpr (cluesOf puzzle)) ACC REJ
      [cpuAirS m.hd m.stk m.heap.length ACC, memAirC, progAirS m.heap, witAirS] := by
  unfold sudAirs; rw [stmtMachineA_eq]

/-- The Sudoku circuit is guarded, for every puzzle. -/
theorem sud_guarded (puzzle : List Nat) : ∀ A ∈ sudAirs puzzle, A.cons.all E.guarded = true := by
  rw [sudAirs_eq]; exact sudS_guarded _ _ _ _

/-- Acceptance of the Sudoku circuit's data is `SudOK`. -/
theorem sudOK_of {puzzle : List Nat} {ts : List Table} (h : Accepted (sudAirs puzzle) ts) :
    ∃ C Mm Pg Wt, ts = [C, Mm, Pg, Wt] ∧
      SudOK (stmtMachine (fun _ => false) 729 (sudokuExpr (cluesOf puzzle)) ACC REJ).hd
        (stmtMachine (fun _ => false) 729 (sudokuExpr (cluesOf puzzle)) ACC REJ).stk
        (stmtMachine (fun _ => false) 729 (sudokuExpr (cluesOf puzzle)) ACC REJ).heap.length
        (stmtMachine (fun _ => false) 729 (sudokuExpr (cluesOf puzzle)) ACC REJ).heap C Mm Pg Wt := by
  rw [sudAirs_eq] at h
  generalize stmtMachine (fun _ => false) 729 (sudokuExpr (cluesOf puzzle)) ACC REJ = m at h ⊢
  obtain ⟨hl, hsat, hbal, hht, htwo⟩ := h
  match ts, hl with
  | [C, Mm, Pg, Wt], _ =>
    have mem : ∀ A T, (A, T) ∈ sudTables m.hd m.stk m.heap.length m.heap C Mm Pg Wt →
        Sat A T ∧ (A.pre = 0 ∨ PreIs A T) := fun A T hm => hsat (A, T) hm
    have pre : ∀ A T, (A, T) ∈ sudTables m.hd m.stk m.heap.length m.heap C Mm Pg Wt → A.pre ≠ 0 →
        PreIs A T := by
      intro A T hm hp
      rcases (mem A T hm).2 with h0 | h0
      · exact absurd h0 hp
      · exact h0
    exact ⟨C, Mm, Pg, Wt, rfl, ⟨(mem _ _ (by simp [sudTables])).1, (mem _ _ (by simp [sudTables])).1,
      (mem _ _ (by simp [sudTables])).1,
      pre _ _ (by simp [sudTables]) (by show (5 : Nat) ≠ 0; decide),
      pre _ _ (by simp [sudTables]) (by show (2 : Nat) ≠ 0; decide), hbal, hht, htwo⟩⟩

/-- **Soundness of the Sudoku circuit.**  If Plonky3 accepts a proof
    against AIRs the same as the circuit for `puzzle`, and the puzzle's
    clues are well formed, then the proof's memory holds, at addresses `3`
    to `731`, a grid that solves the puzzle.  `compare-sudoku` builds the
    circuit only for a puzzle that passes `cluesOKB`, and `cluesOK_of`
    turns that check into `CluesOK`. -/
theorem sudExport_sound {puzzle : List Nat} (hc : CluesOK (cluesOf puzzle)) {Rs : List AirD}
    {ts : List Table} (hs : sameAirsB Rs (sudAirs puzzle) = true) (h : AcceptedP Rs ts) :
    ∃ C Mm Pg Wt, ts = [C, Mm, Pg, Wt] ∧ Solves (cluesOf puzzle) (gridOf (bitsS Mm)) := by
  have hacc := accepted_transfer hs ((acceptedP_iff_of (sud_guarded puzzle) hs ts).1 h)
  obtain ⟨C, Mm, Pg, Wt, rfl, hok⟩ := sudOK_of hacc
  exact ⟨C, Mm, Pg, Wt, rfl, hok.sound hc⟩

end Circuit
