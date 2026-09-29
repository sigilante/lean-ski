import Ski.Circuit.CompPrefix
import Ski.Circuit.Segments

/-!
# Soundness of the composed circuit

Tables accepted for the composed circuit of a statement decode to a run
the Lean AIR with segments accepts (`CompOK.acceptsC`), from the composed
machine of the bits and the region the memory holds, whose region is well
formed; so every term evaluates to `K` on those bits and that region's
witness (`CompOK.sound`, by `CompM.composed_sound`).
-/

namespace Circuit

open B Air Compose CompM Stmt Mach Wit

theorem addStmts_roots_length (pe wr : Nat) : ∀ (Ps : List Term) (h : List Cell),
    (addStmts pe wr h Ps).2.length = Ps.length
  | [], _ => rfl
  | P :: Ps, h => by
    show ((addStmts pe wr _ Ps).2).length + 1 = Ps.length + 1
    rw [addStmts_roots_length pe wr Ps]

theorem blankRoots_length (shp : BT) (W : Nat) (Ps : List Term) : (blankRoots shp W Ps).length = Ps.length :=
  addStmts_roots_length _ _ _ _

theorem ofN_val (x : F) : ofN x.val = x := Fin.ext (val_ofN x.isLt)

/-- The segment table's rows. -/
theorem segRows_get {roots : List Nat} (hn : 0 < roots.length) {i : Nat} (hi : i < (segRows roots).length) :
    (i < roots.length ∧ (segRows roots).getD i [] = [ofN i, ofN (roots.getD i 0)]) ∨
      (roots.length ≤ i ∧ (segRows roots).getD i [] = [ofN 0, ofN (roots.getD 0 0)]) := by
  unfold segRows at *
  rcases Nat.lt_or_ge i roots.length with h | h
  · refine .inl ⟨h, ?_⟩
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp; exact h), List.getElem?_map,
      List.getElem?_eq_getElem (by simp; exact h), List.getElem_zipIdx]
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  · refine .inr ⟨h, ?_⟩
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp; exact h), List.getElem?_replicate]
    simp only [List.length_map, List.length_zipIdx]
    rw [if_pos (by simp at hi; omega)]
    cases roots with
    | nil => exact absurd hn (by decide)
    | cons r rs => rfl

/-- The restart bits, as numbers. -/
def rsF (C : Table) (r : Nat) : Nat := if r < C.h then (C.main r RS).val else 0

theorem rsF_eq {C : Table} {r : Nat} (hr : r < C.h) : rsF C r = (C.main r RS).val := if_pos hr

section

variable {shp : BT} {W : Nat} {Ps : List Term} {C Mm Pg Wt Sg : Table}
  (h : CompOK (blankM shp W Ps).hd (blankM shp W Ps).stk (blankM shp W Ps).heap.length
    (blankRoots shp W Ps).length (blankM shp W Ps).stk (blankM shp W Ps).heap (BT.nleaves shp) W
    (blankRoots shp W Ps) C Mm Pg Wt Sg)
include h

theorem CompOK.rs_le : ∀ r, rsF C r ≤ 1 := by
  intro r
  unfold rsF
  split
  · next hr =>
    obtain ⟨k, hk⟩ := kind_ofC h.cpu hr
    rw [hk.2.2]
    split <;> decide
  · exact Nat.zero_le _

theorem CompOK.cpu_h : C.h ≤ 2 ^ 27 := h.two (cpuAirC (blankM shp W Ps).hd (blankM shp W Ps).stk
  (blankM shp W Ps).heap.length (blankRoots shp W Ps).length (blankM shp W Ps).stk, C) (by simp [compTables])

theorem CompOK.sg_h : Sg.h ≤ 2 ^ 27 := h.two (segsAir (blankRoots shp W Ps), Sg) (by simp [compTables])

/-- The segment counter counts the restarts before the row. -/
theorem CompOK.cnt : ∀ r, r < C.h → C.main r CNT = ofN (cntS (rsF C) r)
  | 0, h0 => (cnt_rows h.cpu h0).1 rfl
  | r + 1, hr => by
    have hr' : r < C.h := Nat.lt_of_succ_lt hr
    rw [(cnt_rows h.cpu hr').2.1 hr, CompOK.cnt r hr']
    show ofN (cntS (rsF C) r) + C.main r RS = ofN (cntS (rsF C) r + rsF C r)
    rw [ofN_add]
    congr 1
    unfold rsF; rw [if_pos hr', ofN_val]

theorem CompOK.cnt_val {r : Nat} (hr : r < C.h) : (C.main r CNT).val = cntS (rsF C) r := by
  rw [h.cnt r hr]
  exact val_ofN (Nat.lt_of_le_of_lt (cntS_le _ h.rs_le r) (Nat.lt_of_lt_of_le hr
    (Nat.le_trans h.cpu_h (by decide))))

theorem CompOK.roots_le : (blankRoots shp W Ps).length ≤ 2 ^ 27 := by
  have := h.sgpre.1
  have := h.sg_h
  have : (blankRoots shp W Ps).length ≤ (segRows (blankRoots shp W Ps)).length := by unfold segRows; simp
  simp only [segsAir] at *
  omega

/-- The last row has counted every segment but the last. -/
theorem CompOK.cnt_last : cntS (rsF C) (C.h - 1) = (blankRoots shp W Ps).length - 1 := by
  have h0 := h.cpu.1
  have hl : C.h - 1 < C.h := by omega
  have e := (cnt_rows h.cpu hl).2.2 (by omega)
  have := h.cnt_val hl
  rw [e, val_ofN (by have := h.roots_le; have : P = 2013265921 := rfl; omega)] at this
  exact this.symm

theorem CompOK.kind11 {r : Nat} (hr : r < C.h) (hrs : C.main r RS = 1) : IsKindC C r 11 := by
  obtain ⟨k, hk⟩ := kind_ofC h.cpu hr
  have e := hk.2.2
  rw [hrs] at e
  by_cases hk11 : k = 11
  · subst hk11; exact hk
  · rw [if_neg hk11] at e; exact absurd e (by decide)

/-- **A restart jumps** to the next segment's root, over the nil, the
    counter unchanged. -/
theorem CompOK.restart {r j : Nat} (hr : r + 1 < C.h) (hrs : C.main r RS = 1)
    (hc : C.main r CNT = ofN j) (hj : j + 1 < (blankRoots shp W Ps).length) :
    rowOf C (r + 1) = ⟨(blankRoots shp W Ps).getD (j + 1) 0, (blankM shp W Ps).stk, (rowOf C r).ctr⟩ := by
  have hr' : r < C.h := Nat.lt_of_succ_lt hr
  have hk := h.kind11 hr' hrs
  obtain ⟨_, _, _, _, _, _, nh, ns, nc⟩ := kind_factsC hr' hk
  obtain ⟨m1, m2, m3⟩ := next_regsC h.cpu hr' hr
  have z : (nextHdOfC 11).eval (C.env r) = 0 := rfl
  have zs : (nextStkOfC 11).eval (C.env r) = 0 := rfl
  have zc : (nextCtrOfC 11).eval (C.env r) = C.main r CTR := env_main0 hr'
  rw [nh, z, hrs, zero_add', one_mul'] at m1
  rw [ns, zs, hrs, zero_add', one_mul'] at m2
  rw [nc, zc] at m3
  -- the segment table's root
  have hn : 0 < (blankRoots shp W Ps).length := by omega
  have hit := h.segHit (v := [C.main r CNT + 1, C.main r ROOT])
    ⟨(cpuAirC (blankM shp W Ps).hd (blankM shp W Ps).stk (blankM shp W Ps).heap.length
        (blankRoots shp W Ps).length (blankM shp W Ps).stk, C), by simp [compTables], rfl, r, hr',
      ⟨"segs", 1, sRS, [.add (col CNT) one, col ROOT]⟩,
      by show _ ∈ cpuIntersC; rw [cpuIntersC_eq]; simp only [List.mem_cons, true_or, or_true], rfl,
      by simp only [List.map_cons, List.map_nil, E.eval, B.col, B.one, B.c, ofN_one, env_main0 hr'],
      by show (col RS).eval _ = 1; rw [B.col, E.eval, env_main0 hr', hrs]⟩
  obtain ⟨i, hi, e⟩ := hit
  simp only [List.cons.injEq, and_true] at e
  obtain ⟨e0, e1⟩ := e
  have hiS : i < (segRows (blankRoots shp W Ps)).length := by have := h.sgpre.1; simp only [segsAir] at this; omega
  have pv : ∀ k, k < 2 → Sg.pre i k = ((segRows (blankRoots shp W Ps)).getD i []).getD k 0 :=
    fun k hk => h.sgpre.2 i k hi hk
  rw [pv 0 (by decide)] at e0
  rw [pv 1 (by decide)] at e1
  rw [hc, ← ofN_one, ← ofN_add] at e0
  have hP := h.roots_le
  have hPP : P = 2013265921 := rfl
  rcases segRows_get hn hiS with ⟨hin, ge⟩ | ⟨_, ge⟩
  · rw [ge] at e0 e1
    have hij : i = j + 1 := ofN_inj (by omega) (by omega) e0
    subst hij
    have hroot : (blankRoots shp W Ps).getD (j + 1) 0 < (blankM shp W Ps).heap.length := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hin]
      exact (blank_fits shp W Ps).2 _ (List.getElem_mem hin)
    have hstk : (blankM shp W Ps).stk < (blankM shp W Ps).heap.length := by
      show (cHeap _ shp _ Ps).1.length < ((cHeap _ shp _ Ps).1 ++ [Cell.nil]).length
      simp
    have hH := h.heap_lt
    show (⟨(C.main (r + 1) HD).val, (C.main (r + 1) STK).val, (C.main (r + 1) CTR).val⟩ : Row) = _
    rw [m1, m2, m3, ← e1, List.getD_cons_succ, List.getD_cons_zero,
      val_ofN (n := (blankRoots shp W Ps).getD (j + 1) 0) (by omega),
      val_ofN (n := (blankM shp W Ps).stk) (by omega)]
    rfl
  · rw [ge] at e0
    exact absurd (ofN_inj (by omega) (by omega) e0) (by omega)

/-- **A row that is no restart steps or has halted.** -/
theorem CompOK.stepOrHalt {r : Nat} (hr : r + 1 < C.h) (hrs : C.main r RS = 0) :
    stepRow (memOf Mm) (rowOf C r) = some (rowOf C (r + 1)) ∨
      (haltRow (memOf Mm) (rowOf C r) = true ∧ rowOf C (r + 1) = rowOf C r) := by
  have hr' : r < C.h := Nat.lt_of_succ_lt hr
  obtain ⟨k, hk⟩ := kind_ofC h.cpu hr'
  have hk11 : k ≠ 11 := fun e => by
    have := hk.2.2; rw [hrs, if_pos e] at this; exact absurd this (by decide)
  have hk11' : k < 11 := by have := hk.1; omega
  obtain ⟨_, _, _, _, _, _, nh, ns, nc⟩ := kind_factsC hr' hk
  obtain ⟨m1, m2, m3⟩ := next_regsC h.cpu hr' hr
  rw [nh, hrs, zero_mul', add_zero'] at m1
  rw [ns, hrs, zero_mul', add_zero'] at m2
  rw [nc] at m3
  have hnext : rowOf C (r + 1) = ⟨((nextHdOfC k).eval (C.env r)).val, ((nextStkOfC k).eval (C.env r)).val,
      ((nextCtrOfC k).eval (C.env r)).val⟩ := by
    simp only [rowOf, m1, m2, m3]
  rcases Nat.lt_or_ge k 4 with h4 | h4
  · exact .inl (by rw [hnext]; exact h.step hr' hk h4)
  · refine .inr ⟨h.halt hr' hk h4 hk11', ?_⟩
    rw [hnext]
    simp only [nextHdOfC, nextStkOfC, nextCtrOfC, if_neg hk11, nextHdOf_halt h4, nextStkOf_halt h4,
      nextCtrOf_halt h4]
    simp only [rowOf, B.col, E.eval, env_main0 hr']

/-- A segment's end reads `K` at the head over a nil: a restart (`11`) or
    the last row's `HK1` (`5`). -/
theorem CompOK.endReads {r k : Nat} (hr : r < C.h) (hk : IsKindC C r k) (hk5 : k = 11 ∨ k = 5) :
    rd (memOf Mm) (rowOf C r).ctr (rowOf C r).hd = some .K ∧
      rd (memOf Mm) (rowOf C r).ctr (rowOf C r).stk = some .nil := by
  rcases hk5 with rfl | rfl
  · exact ⟨h.read hr hk (j := 0) (by decide) rfl, h.read hr hk (j := 1) (by decide) rfl⟩
  · exact ⟨h.read hr hk (j := 0) (by decide) rfl, h.read hr hk (j := 1) (by decide) rfl⟩

/-- **The decoded run is accepted by the AIR with segments.** -/
theorem CompOK.acceptsC (hPs : 0 < Ps.length) :
    AcceptsC (memOf Mm) (cMachine (bitsM (memOf Mm)) shp (regionM (memOf Mm) (BT.nleaves shp) W) Ps)
      (blankRoots shp W Ps) (blankM shp W Ps).stk Ps.length
      (endRow (rsF C) (C.h - 1) Ps.length) (rowOf C) := by
  have hn : (blankRoots shp W Ps).length = Ps.length := blankRoots_length shp W Ps
  have hc := h.cnt_last
  rw [hn] at hc
  have h0 : 0 < C.h := h.cpu.1
  obtain ⟨r1, r2, r3⟩ := first_regsC h.cpu h0 rfl
  have hH := h.heap_lt
  have hl : (regionM (memOf Mm) (BT.nleaves shp) W).length = (List.replicate W Cell.S).length := by
    rw [List.length_replicate]; exact h.region_len
  obtain ⟨_, _, _, hlen, _, _⟩ := cMachine_public (bitsM (memOf Mm)) (fun _ => false) shp
    (regionM (memOf Mm) (BT.nleaves shp) W) (List.replicate W .S) Ps hl
  have ctr0 : (rowOf C 0).ctr = (blankM shp W Ps).heap.length := by
    show (C.main 0 CTR).val = _; rw [r3, val_ofN hH]
  have hstk : (blankM shp W Ps).stk < (blankM shp W Ps).heap.length := by
    show (cHeap _ shp _ Ps).1.length < ((cHeap _ shp _ Ps).1 ++ [Cell.nil]).length
    simp
  have hhd : (blankM shp W Ps).hd < (blankM shp W Ps).heap.length := by
    show (blankRoots shp W Ps).getD 0 0 < _
    have : 0 < (blankRoots shp W Ps).length := by omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem this]
    exact (blank_fits shp W Ps).2 _ (List.getElem_mem this)
  have hf := h.rs_le
  refine ⟨hPs, ?_, ?_, ?_, ?_, endRow_mono _ hf hc, fun j hj => ?_, fun i hi hne => ?_, fun j hj => ?_⟩
  · rw [ctr0]; exact h.heap0
  · show (C.main 0 HD).val = _; rw [r1, val_ofN (by omega)]; rfl
  · show (C.main 0 STK).val = _; rw [r2, val_ofN (by omega)]
  · rw [ctr0]; exact hlen.symm
  · -- a restart
    obtain ⟨a1, a2, a3⟩ := endRow_spec _ hf hc hj
    have hlt : endRow (rsF C) (C.h - 1) Ps.length j + 1 < C.h := by omega
    have hrs : C.main (endRow (rsF C) (C.h - 1) Ps.length j) RS = 1 := by
      have : rsF C (endRow (rsF C) (C.h - 1) Ps.length j) = 1 := a2
      have hb : endRow (rsF C) (C.h - 1) Ps.length j < C.h := by omega
      rw [rsF_eq hb] at this
      rw [← ofN_val (C.main _ RS), this]; rfl
    have hcnt : C.main (endRow (rsF C) (C.h - 1) Ps.length j) CNT = ofN j := by
      rw [h.cnt _ (by omega), a3]
    exact h.restart hlt hrs hcnt (by omega)
  · -- no restart: a step, or a halt
    rw [endRow_last _ _ _ hPs] at hi
    have hrs : rsF C i = 0 := by
      have := hf i
      rcases Nat.lt_or_ge (rsF C i) 1 with h1 | h1
      · omega
      · obtain ⟨j, hj, e⟩ := endRow_of_one _ hf hc hi (by omega)
        exact absurd e.symm (hne j hj)
    have hrs' : C.main i RS = 0 := by
      have hb : i < C.h := by omega
      rw [rsF_eq hb] at hrs
      rw [← ofN_val (C.main i RS), hrs]; rfl
    exact h.stepOrHalt (by omega) hrs'
  · -- a segment's end
    by_cases hj1 : j + 1 < Ps.length
    · obtain ⟨a1, a2, _⟩ := endRow_spec _ hf hc hj1
      have hrs : C.main (endRow (rsF C) (C.h - 1) Ps.length j) RS = 1 := by
        have : rsF C (endRow (rsF C) (C.h - 1) Ps.length j) = 1 := a2
        have hb : endRow (rsF C) (C.h - 1) Ps.length j < C.h := by omega
        rw [rsF_eq hb] at this
        rw [← ofN_val (C.main _ RS), this]; rfl
      exact h.endReads (by omega) (h.kind11 (by omega) hrs) (.inl rfl)
    · have e : j = Ps.length - 1 := by omega
      rw [e, endRow_last _ _ _ hPs]
      have hl' : C.h - 1 < C.h := by omega
      obtain ⟨k, hk⟩ := kind_ofC h.cpu hl'
      obtain ⟨_, hk1⟩ := last_rowC h.cpu hl' (by omega)
      have hk5 : k = 5 := by
        have := hk.2.1 5 (by decide)
        rw [hk1] at this
        by_cases e5 : 5 = k
        · exact e5.symm
        · rw [if_neg (fun h' => e5 h'.1)] at this; exact absurd this (by decide)
      exact h.endReads hl' hk (.inr hk5)

/-- **Soundness of the composed circuit**: the bits and the region the
    memory holds make every statement term evaluate to `K`. -/
theorem CompOK.sound (hPs : 0 < Ps.length) :
    ∃ w, cWitness (bitsM (memOf Mm)) (BT.nleaves shp) (regionM (memOf Mm) (BT.nleaves shp) W) = some w ∧
      EvalRel (Ps, SameShape shp) (fillB shp (bitsM (memOf Mm)) 0) w := by
  have hl : (regionM (memOf Mm) (BT.nleaves shp) W).length = (List.replicate W Cell.S).length := by
    rw [List.length_replicate]; exact h.region_len
  obtain ⟨_, hstk, hroots, _, _, _⟩ := cMachine_public (bitsM (memOf Mm)) (fun _ => false) shp
    (regionM (memOf Mm) (BT.nleaves shp) W) (List.replicate W .S) Ps hl
  have ha := h.acceptsC hPs
  have e1 : (cHeap (bitsM (memOf Mm)) shp (regionM (memOf Mm) (BT.nleaves shp) W) Ps).2 = blankRoots shp W Ps :=
    hroots
  have e2 : (cHeap (bitsM (memOf Mm)) shp (regionM (memOf Mm) (BT.nleaves shp) W) Ps).1.length =
      (blankM shp W Ps).stk := hstk
  rw [← e1, ← e2] at ha
  exact composed_sound h.regionWF ha

end

end Circuit
