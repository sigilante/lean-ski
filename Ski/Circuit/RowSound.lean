import Ski.Circuit.CompFinal

/-!
# One CPU row is one machine transition, for any corpus-CPU circuit

`RowOK`: a table satisfying the corpus CPU's constraints on every row
that does not instantiate (`RowSat`), a memory table
whose address column is its row index, and a lookup property: every
`mem` message the CPU sends with count `1` is a memory row.  From these
alone, as `Ski/Circuit/BaseStep.lean` proves for the corpus circuit, each
row reads the decoded memory as the rule table does (`RowOK.read`), steps
(`RowOK.step`) or halts (`RowOK.halt`), and a table with no
instantiation is a run of the Lean AIR from its first row
(`RowOK.acceptsFrom`).  The hidden-term and Sudoku circuits discharge
`RowOK` from their own buses; the jet circuit uses it on its corpus rows.
-/

namespace Circuit

open B Air

/-- **What a corpus-CPU circuit gives of its CPU and memory.** -/
structure RowOK (hd0 stk0 ctr0 : Nat) (C Mm : Table) : Prop where
  pos : 0 < C.h
  cpu : ∀ r, r < C.h → C.main r (SEL + 11) = 0 → RowSat hd0 stk0 ctr0 C r
  addr : ∀ m, m < Mm.h → Mm.main m 0 = ofN m
  memh : Mm.h ≤ 2 ^ 27
  look : ∀ r, r < C.h → ∀ I ∈ cpuInters, I.bus = "mem" → I.count.eval (C.env r) = 1 →
    ∃ m, m < Mm.h ∧ [Mm.main m 0, Mm.main m 1, Mm.main m 2, Mm.main m 3] = I.fields.map (fun e => e.eval (C.env r))

section

variable {hd0 stk0 ctr0 : Nat} {C Mm : Table} (h : RowOK hd0 stk0 ctr0 C Mm)
include h

theorem RowOK.mem_h : Mm.h ≤ 2 ^ 27 := h.memh

/-- A row of one of the machine's kinds satisfies the corpus CPU's constraints. -/
theorem RowOK.rowSat {r k : Nat} (hr : r < C.h) (hk : IsKind C r k) : RowSat hd0 stk0 ctr0 C r :=
  h.cpu r hr (by rw [hk.2 11 (by decide), if_neg (Nat.ne_of_gt hk.1)])

theorem RowOK.cell {a t x y : F}
    (hm : ∃ m, m < Mm.h ∧ [Mm.main m 0, Mm.main m 1, Mm.main m 2, Mm.main m 3] = [a, t, x, y]) :
    a.val < Mm.h ∧ (memOf Mm)[a.val]? = some (cellOf t x y) := by
  obtain ⟨m, hm, e⟩ := hm
  simp only [List.cons.injEq, and_true] at e
  obtain ⟨e0, e1, e2, e3⟩ := e
  have hmP : m < P := Nat.lt_of_lt_of_le hm (Nat.le_trans h.mem_h (by decide))
  rw [h.addr m hm] at e0
  rw [← e0, val_ofN hmP, memOf_get hm, e1, e2, e3]
  exact ⟨hm, rfl⟩

theorem RowOK.send {r : Nat} (hr : r < C.h) {I : Inter} (hI : I ∈ cpuInters) (hbus : I.bus = "mem")
    {a t x y : F} (hf : I.fields.map (fun e => e.eval (C.env r)) = [a, t, x, y])
    (hc : I.count.eval (C.env r) = 1) :
    a.val < Mm.h ∧ (memOf Mm)[a.val]? = some (cellOf t x y) := by
  obtain ⟨m, hm, e⟩ := h.look r hr I hI hbus hc
  exact h.cell ⟨m, hm, by rw [e, hf]⟩

omit h in
/-- A range check's value is below `2^24`. -/
theorem rowRangeVal_lt {r : Nat} (hr : r < C.h) (hs : RowSat hd0 stk0 ctr0 C r) {j : Nat} (hj : j < 4) :
    ((rangeVal j).eval (C.env r)).val < 2 ^ 24 := by
  have step : ∀ n, n ≤ RANGE_BITS →
      (((List.range n).foldl (fun v i => E.add v (E.mul (col (BITS + j * RANGE_BITS + i)) (c (2 ^ i)))) zero).eval
        (C.env r)).val < 2 ^ n := by
    intro n
    induction n with
    | zero => intro _; show (0 : Nat) < 1; decide
    | succ n ih =>
      intro hn
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      have ih := ih (Nat.le_of_succ_le hn)
      generalize (List.foldl (fun v i => E.add v (E.mul (col (BITS + j * RANGE_BITS + i)) (c (2 ^ i))))
        zero (List.range n)) = X at ih ⊢
      simp only [E.eval, B.col, B.c, env_main0 hr]
      generalize X.eval (C.env r) = x at ih ⊢
      have hpow : 2 ^ (n + 1) ≤ 2 ^ 24 := Nat.pow_le_pow_right (by decide) hn
      have hP : 2 ^ 24 < P := by decide
      rcases bit_of (range_bit hs hr hj (i := n) hn) with hb | hb <;> rw [hb]
      · rw [zero_mul', add_zero']
        exact Nat.lt_of_lt_of_le ih (Nat.pow_le_pow_right (by decide) (Nat.le_succ n))
      · rw [one_mul', val_add_nat (by rw [Nat.pow_succ] at hpow; omega), Nat.pow_succ]
        omega
  exact step RANGE_BITS (Nat.le_refl _)

/-- **An active read**: the address is below the counter, and the memory
    holds there a cell with the kind's tag and the row's fields. -/
theorem RowOK.read {r k : Nat} (hr : r < C.h) (hk : IsKind C r k) {j : Nat} (hj : j < 4)
    (hact : actOf k j = 1) :
    rd (memOf Mm) (C.main r CTR).val (C.main r (addrCol j)).val =
      some (cellOf (ofN (tagOf k j)) (C.main r (FLD + 2 * j)) (C.main r (FLD + 2 * j + 1))) := by
  obtain ⟨hf, _⟩ := kind_facts hr hk
  obtain ⟨ha, ht⟩ := hf j hj
  rw [hact, ofN_one] at ha
  have hadr : (addrs.getD j zero).eval (C.env r) = C.main r (addrCol j) := by
    rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega) with rfl | rfl | rfl | rfl <;>
      simp [addrs, addrCol, fld, B.col, E.eval, env_main0 hr]
  have hI : readInter j ∈ cpuInters := by
    rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega) with rfl | rfl | rfl | rfl <;> simp [cpuInters]
  obtain ⟨hlt, hget⟩ := h.send hr hI rfl
    (a := C.main r (addrCol j)) (t := ofN (tagOf k j)) (x := C.main r (FLD + 2 * j))
    (y := C.main r (FLD + 2 * j + 1))
    (by simp only [readInter, List.map_cons, List.map_nil, hadr, ht, fld, B.col, E.eval, env_main0 hr]; rfl)
    ha
  -- the range check: counter = address + 1 + value, with no wrap
  have hre := range_eq (h.rowSat hr hk) hr hj
  rw [ha, one_mul', hadr] at hre
  have e := sub_eq_zero hre
  have hctr : C.main r CTR = (C.main r (addrCol j) + 1) + (rangeVal j).eval (C.env r) := by
    rw [← e, add_sub_cancel3]
  have hv := rowRangeVal_lt hr (h.rowSat hr hk) hj
  have hm := h.mem_h
  have hb : (C.main r (addrCol j)).val + 1 + ((rangeVal j).eval (C.env r)).val < P := by
    have : 2 ^ 27 + 2 ^ 24 + 8 < P := P_big
    omega
  have h1 : (C.main r (addrCol j) + 1).val = (C.main r (addrCol j)).val + 1 :=
    val_add_of_lt (by show _ + 1 < P; omega)
  have hval : (C.main r CTR).val = (C.main r (addrCol j)).val + 1 + ((rangeVal j).eval (C.env r)).val := by
    rw [hctr, val_add_of_lt (by rw [h1]; exact hb), h1]
  unfold rd
  rw [if_pos (by omega), hget]

/-- **A stepping row steps**: to the registers its kind computes. -/
theorem RowOK.step {r k : Nat} (hr : r < C.h) (hk : IsKind C r k) (hk4 : k < 4) :
    stepRow (memOf Mm) (rowOf C r) = some ⟨((nextHdOf k).eval (C.env r)).val,
      ((nextStkOf k).eval (C.env r)).val, ((nextCtrOf k).eval (C.env r)).val⟩ := by
  obtain ⟨_, _, hApp, hS, _⟩ := kind_facts hr hk
  have cv := col_eval hr
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 by omega) with rfl | rfl | rfl | rfl
  · -- App: read the head; write the argument's stack cell
    have r0 : rd (memOf Mm) (C.main r CTR).val (C.main r HD).val =
        some (.app (C.main r (FLD + 0)).val (C.main r (FLD + 1)).val) := h.read hr hk (j := 0) (by decide) rfl
    have w0 := h.send hr (I := ⟨"mem", 1, sApp, [col CTR, c 5, fld 1, col STK]⟩)
      (by simp [cpuInters, writeInters]) rfl
      (a := C.main r CTR) (t := ofN 5) (x := C.main r (FLD + 1)) (y := C.main r STK)
      (by simp only [List.map_cons, List.map_nil, fld, cv]; rfl) (by rw [hApp]; rfl)
    rw [cellOf_cons] at w0
    have hc1 : (C.main r CTR + 1).val = (C.main r CTR).val + 1 :=
      val_add_of_lt (by have := w0.1; have := h.mem_h; have := P_big; show _ + 1 < P; omega)
    simp only [stepRow, rowOf, stepG, r0, wrs, w0.2, beq_self_eq_true, Bool.and_true, ↓reduceIte,
      List.length_cons, List.length_nil, Option.some.injEq, Row.mk.injEq]
    refine ⟨?_, ?_, ?_⟩
    · show _ = ((fld 0).eval _).val; rw [fld, cv]
    · show _ = ((col CTR).eval _).val; rw [cv]
    · show _ = ((E.add (col CTR) one).eval _).val
      simp only [E.eval, cv, B.one, B.c, ofN_one, hc1]
  · -- I: read the head and one stack cell
    have r0 : rd (memOf Mm) (C.main r CTR).val (C.main r HD).val = some .I :=
      h.read hr hk (j := 0) (by decide) rfl
    have r1 : rd (memOf Mm) (C.main r CTR).val (C.main r STK).val =
        some (.cons (C.main r (FLD + 2)).val (C.main r (FLD + 3)).val) := h.read hr hk (j := 1) (by decide) rfl
    simp only [stepRow, rowOf, stepG, r0, r1, wrs, ↓reduceIte, List.length_nil, Nat.add_zero,
      Option.some.injEq, Row.mk.injEq]
    refine ⟨?_, ?_, ?_⟩
    · show _ = ((fld 2).eval _).val; rw [fld, cv]
    · show _ = ((fld 3).eval _).val; rw [fld, cv]
    · show _ = ((col CTR).eval _).val; rw [cv]
  · -- K: read the head and two stack cells
    have r0 : rd (memOf Mm) (C.main r CTR).val (C.main r HD).val = some .K :=
      h.read hr hk (j := 0) (by decide) rfl
    have r1 : rd (memOf Mm) (C.main r CTR).val (C.main r STK).val =
        some (.cons (C.main r (FLD + 2)).val (C.main r (FLD + 3)).val) := h.read hr hk (j := 1) (by decide) rfl
    have r2 : rd (memOf Mm) (C.main r CTR).val (C.main r (FLD + 3)).val =
        some (.cons (C.main r (FLD + 4)).val (C.main r (FLD + 5)).val) := h.read hr hk (j := 2) (by decide) rfl
    simp only [stepRow, rowOf, stepG, r0, r1, r2, wrs, ↓reduceIte, List.length_nil, Nat.add_zero,
      Option.some.injEq, Row.mk.injEq]
    refine ⟨?_, ?_, ?_⟩
    · show _ = ((fld 2).eval _).val; rw [fld, cv]
    · show _ = ((fld 5).eval _).val; rw [fld, cv]
    · show _ = ((col CTR).eval _).val; rw [cv]
  · -- S: read the head and three stack cells; write three cells
    have r0 : rd (memOf Mm) (C.main r CTR).val (C.main r HD).val = some .S :=
      h.read hr hk (j := 0) (by decide) rfl
    have r1 : rd (memOf Mm) (C.main r CTR).val (C.main r STK).val =
        some (.cons (C.main r (FLD + 2)).val (C.main r (FLD + 3)).val) := h.read hr hk (j := 1) (by decide) rfl
    have r2 : rd (memOf Mm) (C.main r CTR).val (C.main r (FLD + 3)).val =
        some (.cons (C.main r (FLD + 4)).val (C.main r (FLD + 5)).val) := h.read hr hk (j := 2) (by decide) rfl
    have r3 : rd (memOf Mm) (C.main r CTR).val (C.main r (FLD + 5)).val =
        some (.cons (C.main r (FLD + 6)).val (C.main r (FLD + 7)).val) := h.read hr hk (j := 3) (by decide) rfl
    have hs1 : sS.eval (C.env r) = 1 := by rw [hS]; rfl
    have w1 := h.send hr (I := ⟨"mem", 1, sS, [col CTR, c 3, fld 4, fld 6]⟩)
      (by simp [cpuInters, writeInters]) rfl
      (a := C.main r CTR) (t := ofN 3) (x := C.main r (FLD + 4)) (y := C.main r (FLD + 6))
      (by simp only [List.map_cons, List.map_nil, fld, cv]; rfl) hs1
    rw [cellOf_app] at w1
    have hm := h.mem_h
    have hPb := P_big
    have hc1 : (C.main r CTR + 1).val = (C.main r CTR).val + 1 :=
      val_add_of_lt (by have := w1.1; show _ + 1 < P; omega)
    have hc2 : (C.main r CTR + ofN 2).val = (C.main r CTR).val + 1 + 1 := by
      rw [val_add_nat (by have := w1.1; omega)]
    have hc3 : (C.main r CTR + ofN 3).val = (C.main r CTR).val + 3 := by
      rw [val_add_nat (by have := w1.1; omega)]
    have w2 := h.send hr (I := ⟨"mem", 1, sS, [.add (col CTR) one, c 5, col CTR, fld 7]⟩)
      (by simp [cpuInters, writeInters]) rfl
      (a := C.main r CTR + 1) (t := ofN 5) (x := C.main r CTR) (y := C.main r (FLD + 7))
      (by simp only [List.map_cons, List.map_nil, fld, E.eval, cv, B.one, B.c, ofN_one]) hs1
    rw [cellOf_cons, hc1] at w2
    have w3 := h.send hr (I := ⟨"mem", 1, sS, [.add (col CTR) (c 2), c 5, fld 6, .add (col CTR) one]⟩)
      (by simp [cpuInters, writeInters]) rfl
      (a := C.main r CTR + ofN 2) (t := ofN 5) (x := C.main r (FLD + 6)) (y := C.main r CTR + 1)
      (by simp only [List.map_cons, List.map_nil, fld, E.eval, cv, B.one, B.c, ofN_one]) hs1
    rw [cellOf_cons, hc2, hc1] at w3
    simp only [stepRow, rowOf, stepG, r0, r1, r2, r3, wrs, w1.2, w2.2, w3.2, beq_self_eq_true,
      Bool.and_true, ↓reduceIte, List.length_cons, List.length_nil, Option.some.injEq, Row.mk.injEq]
    refine ⟨?_, ?_, ?_⟩
    · show _ = ((fld 2).eval _).val; rw [fld, cv]
    · show _ = ((E.add (col CTR) (c 2)).eval _).val
      simp only [E.eval, cv, B.c, hc2]
    · show _ = ((E.add (col CTR) (c 3)).eval _).val
      simp only [E.eval, cv, B.c, hc3]

/-- **A halting row halts**: its reads show a combinator short of
    arguments, or an atom. -/
theorem RowOK.halt {r k : Nat} (hr : r < C.h) (hk : IsKind C r k) (hk4 : 4 ≤ k) :
    haltRow (memOf Mm) (rowOf C r) = true := by
  have hk11 := hk.1
  rcases (show k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 by omega)
    with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have r0 : rd (memOf Mm) (C.main r CTR).val (C.main r HD).val = some .I :=
      h.read hr hk (j := 0) (by decide) rfl
    have r1 : rd (memOf Mm) (C.main r CTR).val (C.main r STK).val = some .nil :=
      h.read hr hk (j := 1) (by decide) rfl
    simp only [haltRow, rowOf, r0, short, r1]
  · have r0 : rd (memOf Mm) (C.main r CTR).val (C.main r HD).val = some .K :=
      h.read hr hk (j := 0) (by decide) rfl
    have r1 : rd (memOf Mm) (C.main r CTR).val (C.main r STK).val = some .nil :=
      h.read hr hk (j := 1) (by decide) rfl
    simp only [haltRow, rowOf, r0, short, r1]
  · have r0 : rd (memOf Mm) (C.main r CTR).val (C.main r HD).val = some .K :=
      h.read hr hk (j := 0) (by decide) rfl
    have r1 : rd (memOf Mm) (C.main r CTR).val (C.main r STK).val =
        some (.cons (C.main r (FLD + 2)).val (C.main r (FLD + 3)).val) := h.read hr hk (j := 1) (by decide) rfl
    have r2 : rd (memOf Mm) (C.main r CTR).val (C.main r (FLD + 3)).val = some .nil :=
      h.read hr hk (j := 2) (by decide) rfl
    simp only [haltRow, rowOf, r0, short, r1, r2]
  · have r0 : rd (memOf Mm) (C.main r CTR).val (C.main r HD).val = some .S :=
      h.read hr hk (j := 0) (by decide) rfl
    have r1 : rd (memOf Mm) (C.main r CTR).val (C.main r STK).val = some .nil :=
      h.read hr hk (j := 1) (by decide) rfl
    simp only [haltRow, rowOf, r0, short, r1]
  · have r0 : rd (memOf Mm) (C.main r CTR).val (C.main r HD).val = some .S :=
      h.read hr hk (j := 0) (by decide) rfl
    have r1 : rd (memOf Mm) (C.main r CTR).val (C.main r STK).val =
        some (.cons (C.main r (FLD + 2)).val (C.main r (FLD + 3)).val) := h.read hr hk (j := 1) (by decide) rfl
    have r2 : rd (memOf Mm) (C.main r CTR).val (C.main r (FLD + 3)).val = some .nil :=
      h.read hr hk (j := 2) (by decide) rfl
    simp only [haltRow, rowOf, r0, short, r1, r2]
  · have r0 : rd (memOf Mm) (C.main r CTR).val (C.main r HD).val = some .S :=
      h.read hr hk (j := 0) (by decide) rfl
    have r1 : rd (memOf Mm) (C.main r CTR).val (C.main r STK).val =
        some (.cons (C.main r (FLD + 2)).val (C.main r (FLD + 3)).val) := h.read hr hk (j := 1) (by decide) rfl
    have r2 : rd (memOf Mm) (C.main r CTR).val (C.main r (FLD + 3)).val =
        some (.cons (C.main r (FLD + 4)).val (C.main r (FLD + 5)).val) := h.read hr hk (j := 2) (by decide) rfl
    have r3 : rd (memOf Mm) (C.main r CTR).val (C.main r (FLD + 5)).val = some .nil :=
      h.read hr hk (j := 3) (by decide) rfl
    simp only [haltRow, rowOf, r0, short, r1, r2, r3]
  · have r0 : rd (memOf Mm) (C.main r CTR).val (C.main r HD).val = some (.atom (C.main r (FLD + 0)).val) :=
      h.read hr hk (j := 0) (by decide) rfl
    simp only [haltRow, rowOf, r0]

/-- **A table with no instantiation is a run of the Lean AIR** from the
    machine its first row and the memory's prefix name. -/
theorem RowOK.acceptsFrom (hall : ∀ r, r < C.h → C.main r (SEL + 11) = 0) {m0 : Mach} (hheap : (memOf Mm).take ctr0 = m0.heap) (hhd : m0.hd = hd0)
    (hstk : m0.stk = stk0) (hctr : m0.heap.length = ctr0) (hP : hd0 < P ∧ stk0 < P ∧ ctr0 < P) :
    AcceptsFrom (memOf Mm) m0 C.h (rowOf C) := by
  have h0 : 0 < C.h := h.pos
  obtain ⟨e1, e2, e3⟩ := first_regs (h.cpu 0 h0 (hall 0 h0)) h0 rfl
  have ctr0' : (rowOf C 0).ctr = ctr0 := by show (C.main 0 CTR).val = _; rw [e3, val_ofN hP.2.2]
  refine ⟨h0, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [ctr0']; exact hheap
  · show (C.main 0 HD).val = _; rw [e1, val_ofN hP.1, hhd]
  · show (C.main 0 STK).val = _; rw [e2, val_ofN hP.2.1, hstk]
  · rw [ctr0', hctr]
  · intro i hi
    have hi' : i < C.h := Nat.lt_of_succ_lt hi
    obtain ⟨k, hk, hsel⟩ := kind_of (h.cpu i hi' (hall i hi')) hi'
    have hK : IsKind C i k := ⟨hk, hsel⟩
    obtain ⟨_, _, _, _, n1, n2, n3⟩ := kind_facts hi' hK
    obtain ⟨m1, m2, m3⟩ := next_regs (h.cpu i hi' (hall i hi')) hi' hi
    have hnext : rowOf C (i + 1) = ⟨((nextHdOf k).eval (C.env i)).val,
        ((nextStkOf k).eval (C.env i)).val, ((nextCtrOf k).eval (C.env i)).val⟩ := by
      simp only [rowOf, m1, m2, m3, n1, n2, n3]
    rcases Nat.lt_or_ge k 4 with hk4 | hk4
    · exact .inl (by rw [hnext]; exact h.step hi' hK hk4)
    · refine .inr ⟨h.halt hi' hK hk4, ?_⟩
      rw [hnext, nextHdOf_halt hk4, nextStkOf_halt hk4, nextCtrOf_halt hk4]
      simp only [rowOf, col_eval hi']
  · have hl : C.h - 1 < C.h := Nat.sub_lt h0 (by decide)
    obtain ⟨k, hk, hsel⟩ := kind_of (h.cpu _ hl (hall _ hl)) hl
    have hK : IsKind C (C.h - 1) k := ⟨hk, hsel⟩
    have hh := last_halt (h.cpu _ hl (hall _ hl)) hl (Nat.sub_add_cancel h0)
    obtain ⟨_, hhalt, _⟩ := kind_facts hl hK
    rcases Nat.lt_or_ge k 4 with hk4 | hk4
    · rw [hhalt, if_neg (Nat.not_le_of_lt hk4)] at hh
      exact absurd hh (by decide)
    · exact h.halt hl hK hk4

end

end Circuit
