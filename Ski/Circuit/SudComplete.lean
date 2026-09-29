import Ski.Circuit.SudSound

/-!
# Completeness of the Sudoku circuit

A run the Lean AIR accepts from the statement machine of a puzzle's inputs,
ending at the accepting marker, within the verifier's heights, gives
tables that the Sudoku circuit accepts with Plonky3's selectors
(`sud_complete`).  The CPU is the witness circuit's honest table
(`cpuTableW`); the input table holds a bit per input.
-/

namespace Circuit

open B Air Stmt Mach Sudoku SudokuText

section

variable {A : List Cell} {m0 : Mach} {k : Nat} {row : Nat → Row} (hA : AcceptsFrom A m0 k row)
  {K : Nat} (hkK : k ≤ K) (hK : K ≤ 2 ^ 24) (hlen : A.length ≤ 2 ^ 24)
include hA hkK hK hlen

/-- **The honest Sudoku CPU satisfies its AIR**, when the run ends at the
    atom `acc`. -/
theorem cpuS_sat (hK0 : 0 < K) {acc : Nat}
    (hfin : rd A (row (k - 1)).ctr (row (k - 1)).hd = some (.atom acc)) :
    Sat (cpuAirS (rowQ row k 0).hd (rowQ row k 0).stk (rowQ row k 0).ctr acc) (cpuTableW A row k K) := by
  have hk := hA.pos
  have hb : ∀ i, i < K → (rowQ row k i).ctr ≤ 2 ^ 24 := by
    intro i _
    unfold rowQ; split
    · exact Nat.le_trans ((hA.reach i (by assumption)).1) hlen
    · exact Nat.le_trans ((hA.reach (k - 1) (by omega)).1) hlen
  have hfinQ : haltRow A (rowQ row k (K - 1)) = true := by
    unfold rowQ; split
    · next h => rw [show K - 1 = k - 1 by omega]; exact hA.final
    · exact hA.final
  have base := cpu_sat (M := A) (row := rowQ row k) (k := K) (rowQ_valid hA hkK) (rowQ_trans hA hkK) hfinQ hb hK0
  refine ⟨hK0, fun c hc i (hi : i < K) => ?_⟩
  have cong := E.eval_congr (cpuW_env (A := A) (row := row) (k := k) hi)
  rcases List.mem_append.1 hc with hc | hc
  · rw [cong c (List.all_eq_true.1 (cpuCons_atoms _ _ _) c hc)]
    exact base.2 c hc i hi
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    have cv : ∀ cc, (col cc).eval ((cpuTableW A row k K).env i) = cpuColW A row k i cc := fun cc => by
      show cpuColW A row k ((i + 0) % K) cc = _; rw [Nat.add_zero, Nat.mod_eq_of_lt hi]
    have elast : i + 1 = K → rowQ row k i = row (k - 1) := by
      intro hl
      unfold rowQ; split
      · next h => rw [show i = k - 1 by omega]
      · rfl
    have hkind : kindOf A (row (k - 1)) = 10 := by simp only [kindOf, hfin]
    rcases hc with rfl | rfl | rfl | rfl
    · simp only [B.bool, E.eval, cv, B.one, B.c, ofN_one]
      show (if BLA + 4 < CPU_WIDTH then _ else 0) * ((if BLA + 4 < CPU_WIDTH then _ else 0) - 1) = 0
      rw [if_neg (by decide), zero_mul']
    · simp only [B.bool, E.eval, cv, B.one, B.c, ofN_one]
      show (if BLB + 4 < CPU_WIDTH then _ else 0) * ((if BLB + 4 < CPU_WIDTH then _ else 0) - 1) = 0
      rw [if_neg (by decide), zero_mul']
    · simp only [B.whenLast, B.eq, E.eval, env_last, sHA, B.one, B.c, ofN_one]
      split
      · next hl =>
        rw [cv]
        show 1 * ((if SEL + 10 < CPU_WIDTH then cpuCol A (rowQ row k i) (SEL + 10) else 0) - 1) = 0
        rw [if_pos (by decide), cpuCol_sel _ _ (by decide), elast hl, hkind, if_pos rfl, sub_self', mul_zero']
      · exact zero_mul' _
    · simp only [B.whenLast, B.eq, E.eval, env_last, fld, B.c]
      split
      · next hl =>
        rw [cv]
        show 1 * ((if FLD + 0 < CPU_WIDTH then cpuCol A (rowQ row k i) (FLD + 0) else 0) - ofN acc) = 0
        rw [if_pos (by decide), cpuCol_fld _ _ (by decide), elast hl, if_pos rfl]
        show 1 * (ofN (cellFields ((rd A (row (k - 1)).ctr (row (k - 1)).hd).getD .nil)).1 - ofN acc) = 0
        rw [hfin]
        show 1 * (ofN acc - ofN acc) = 0
        rw [sub_self', mul_zero']
      · exact zero_mul' _

end

-- ---------------------------------------------------------------------------
-- The program table
-- ---------------------------------------------------------------------------

def progTableS (heap : List Cell) : Table :=
  ⟨(progRowsS heap).length, fun _ _ => 0, fun q j => ((progRowsS heap).getD q []).getD j 0⟩

theorem progRowsS_pos (heap : List Cell) : 0 < (progRowsS heap).length := by
  have := pow2From_ge 64 1 ((heap.zipIdx.filter fun x => !(3 ≤ x.2 && x.2 < 3 + 729)).length)
  unfold progRowsS
  simp only [List.length_append, List.length_map, List.length_replicate]
  omega

theorem progRowsS_le {heap : List Cell} (h : heap.length ≤ 2 ^ 24) : (progRowsS heap).length ≤ 2 ^ 24 := by
  have hf := List.length_filter_le (fun x : Cell × Nat => !(3 ≤ x.2 && x.2 < 3 + 729)) heap.zipIdx
  rw [List.length_zipIdx] at hf
  have hp := pow2From_le (n := (heap.zipIdx.filter fun x => !(3 ≤ x.2 && x.2 < 3 + 729)).length) (by omega)
    64 0 (by decide)
  unfold progRowsS
  simp only [List.length_append, List.length_map, List.length_replicate]
  rw [show (2 : Nat) ^ 0 = 1 from rfl] at hp
  omega

theorem progS_sat (heap : List Cell) :
    Sat (progAirS heap) (progTableS heap) ∧ PreIs (progAirS heap) (progTableS heap) := by
  refine ⟨⟨progRowsS_pos heap, fun c hc i hi => ?_⟩, ⟨rfl, fun _ _ _ _ => rfl⟩⟩
  simp only [progAirS, List.mem_cons, List.not_mem_nil, or_false] at hc
  subst hc
  show (progTableS heap).main ((i + 0) % _) 0 = 0
  rfl

/-- **The program table's messages are honest**, given the public cells in memory. -/
theorem progS_honest {A heap : List Cell}
    (hpub : ∀ i, i < heap.length → ¬ (3 ≤ i ∧ i < 3 + 729) → i < A.length ∧ A.getD i .nil = heap.getD i .nil) :
    ∀ r, r < (progTableS heap).h → ∀ I ∈ (progAirS heap).inters, I.bus = "mem" →
      I.count.eval ((progTableS heap).env r) ≠ 0 →
      ∃ m, m < A.length ∧ I.fields.map (fun e => e.eval ((progTableS heap).env r)) = tupleOf A m := by
  intro q hq I hI _ hc
  simp only [progAirS, List.mem_cons, List.not_mem_nil, or_false] at hI
  subst hI
  have pv : ∀ j, (prec j).eval ((progTableS heap).env q) = ((progRowsS heap).getD q []).getD j 0 := by
    intro j; show (progTableS heap).pre ((q + 0) % _) j = _; rw [Nat.add_zero, Nat.mod_eq_of_lt hq]; rfl
  let pub := heap.zipIdx.filter fun x => !(3 ≤ x.2 && x.2 < 3 + 729)
  let rows := pub.map fun (x : Cell × Nat) =>
    [ofN x.2, ofN (cellTag x.1), ofN (cellFields x.1).1, ofN (cellFields x.1).2, ofN 1]
  have hrows : progRowsS heap = rows ++ List.replicate (pow2From 64 1 rows.length - rows.length)
      [ofN 0, ofN 0, ofN 0, ofN 0, ofN 0] := rfl
  rcases Nat.lt_or_ge q rows.length with hl | hl
  · have hg : (progRowsS heap).getD q [] = rows[q] := by
      rw [hrows, List.getD_eq_getElem?_getD, List.getElem?_append_left hl, List.getElem?_eq_getElem hl]; rfl
    have hm : rows[q] ∈ rows := List.getElem_mem hl
    obtain ⟨⟨c, i⟩, hmp, he⟩ := List.mem_map.1 hm
    obtain ⟨hz, hp⟩ := List.mem_filter.1 hmp
    obtain ⟨_, hi, hc'⟩ := List.mem_zipIdx hz
    simp only [Nat.zero_add, Nat.sub_zero] at hi hc'
    have hp' : ¬ (3 ≤ i ∧ i < 3 + 729) := by
      rintro ⟨h1, h2⟩
      simp only [Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not] at hp
      rcases hp with hp | hp
      · exact hp h1
      · exact hp h2
    obtain ⟨hiA, hA⟩ := hpub i hi hp'
    have hcell : heap.getD i .nil = c := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, hc']; rfl
    refine ⟨i, hiA, ?_⟩
    simp only [List.map_cons, List.map_nil, pv, hg, ← he]
    unfold tupleOf
    rw [hA, hcell]
    rfl
  · exfalso; apply hc
    show (prec 4).eval _ = 0
    rw [pv, hrows, List.getD_eq_getElem?_getD (a := ([] : List F))]
    rcases Nat.lt_or_ge q (rows ++ List.replicate (pow2From 64 1 rows.length - rows.length)
        [ofN 0, ofN 0, ofN 0, ofN 0, ofN 0]).length with h' | h'
    · rw [List.getElem?_append_right hl, List.getElem?_replicate]
      simp only [List.length_append, List.length_replicate] at h'
      rw [if_pos (by omega)]; rfl
    · rw [List.getElem?_eq_none h']; rfl

theorem progS_nobus (heap : List Cell) :
    ∀ r, r < (progTableS heap).h → ∀ I ∈ (progAirS heap).inters, I.bus ≠ "mem" →
      I.count.eval ((progTableS heap).env r) = 0 := by
  intro _ _ I hI hb
  simp only [progAirS, List.mem_cons, List.not_mem_nil, or_false] at hI
  subst hI; exact absurd rfl hb

-- ---------------------------------------------------------------------------
-- The input table
-- ---------------------------------------------------------------------------

/-- The input bit at row `i`: `1` when input `i`'s cell is `K`. -/
def inBit (A : List Cell) (i : Nat) : F := if i < 729 ∧ A.getD (3 + i) .nil = .K then 1 else 0

def witTableS (A : List Cell) : Table :=
  ⟨2 ^ 10, fun i col => if col = 0 then inBit A i else 0, fun q j => (witRowsS.getD q []).getD j 0⟩

theorem witRowsS_length : witRowsS.length = 2 ^ 10 := by
  unfold witRowsS; simp only [List.length_append, List.length_map, List.length_range, List.length_replicate]

theorem witS_sat (A : List Cell) : Sat witAirS (witTableS A) ∧ PreIs witAirS (witTableS A) := by
  refine ⟨⟨show 0 < 2 ^ 10 by decide, fun c hc i (hi : i < 2 ^ 10) => ?_⟩, ⟨by show (2 : Nat) ^ 10 = witRowsS.length; exact witRowsS_length.symm,
    fun _ _ _ _ => by dsimp only [witTableS, witAirS]⟩⟩
  simp only [witAirS, witConsS, List.mem_cons, List.not_mem_nil, or_false] at hc
  have cv : ∀ cc, (col cc).eval ((witTableS A).env i) = if cc = 0 then inBit A i else 0 := fun cc => by
    show (if cc = 0 then inBit A ((i + 0) % 2 ^ 10) else 0) = _; rw [Nat.add_zero, Nat.mod_eq_of_lt hi]
  rcases hc with rfl | rfl
  · simp only [B.bool, E.eval, cv, if_neg (show (5 : Nat) ≠ 0 by decide), zero_mul']
  · simp only [B.bool, E.eval, cv, if_pos rfl, B.one, B.c, ofN_one]
    unfold inBit
    by_cases hb : i < 729 ∧ A.getD (3 + i) .nil = .K
    · rw [if_pos hb, if_pos trivial, sub_self', mul_zero']
    · rw [if_neg hb, if_pos trivial, zero_mul']

theorem witRowsS_getP {q : Nat} (hq : q < 2 ^ 10) :
    witRowsS.getD q [] = if q < 729 then [ofN (3 + q), ofN 1] else [ofN 0, ofN 0] := by
  unfold witRowsS
  rw [List.getD_eq_getElem?_getD]
  split
  · next h =>
    rw [List.getElem?_append_left (by simp only [List.length_map, List.length_range]; exact h),
      List.getElem?_map, List.getElem?_range h]; rfl
  · next h =>
    rw [List.getElem?_append_right (by simp only [List.length_map, List.length_range]; omega),
      List.getElem?_replicate]
    simp only [List.length_map, List.length_range]
    rw [if_pos (by omega)]; rfl

/-- **The input table's messages are honest**, given input cells `K` or `A 0 1`. -/
theorem witS_honest {A : List Cell}
    (hin : ∀ n, n < 729 → 3 + n < A.length ∧ (A.getD (3 + n) .nil = .K ∨ A.getD (3 + n) .nil = .app 0 1)) :
    ∀ r, r < (witTableS A).h → ∀ I ∈ witAirS.inters, I.bus = "mem" →
      I.count.eval ((witTableS A).env r) ≠ 0 →
      ∃ m, m < A.length ∧ I.fields.map (fun e => e.eval ((witTableS A).env r)) = tupleOf A m := by
  intro q (hq : q < 2 ^ 10) I hI hb hc
  simp only [witAirS, witIntersS, List.mem_cons, List.not_mem_nil, or_false] at hI
  rcases hI with rfl | rfl
  · exact absurd hb (by decide)
  have pv : ∀ j, (prec j).eval ((witTableS A).env q) = (witRowsS.getD q []).getD j 0 := by
    intro j; show (witTableS A).pre ((q + 0) % 2 ^ 10) j = _; rw [Nat.add_zero, Nat.mod_eq_of_lt hq]
    dsimp only [witTableS]
  have cv : (col 0).eval ((witTableS A).env q) = inBit A q := by
    show (if (0 : Nat) = 0 then inBit A ((q + 0) % 2 ^ 10) else 0) = _
    rw [if_pos rfl, Nat.add_zero, Nat.mod_eq_of_lt hq]
  rcases Nat.lt_or_ge q 729 with hq7 | hq7
  · obtain ⟨hlt, hcell⟩ := hin q hq7
    refine ⟨3 + q, hlt, ?_⟩
    have g : witRowsS.getD q [] = [ofN (3 + q), ofN 1] := by rw [witRowsS_getP hq, if_pos hq7]
    show [(prec 0).eval _, (c 3).eval _ - (col 0).eval _ * (c 2).eval _, (0 : F), (1 : F) - (col 0).eval _] = _
    rw [pv, cv, g]
    unfold tupleOf inBit
    rcases hcell with h | h
    · rw [if_pos ⟨hq7, h⟩, h]; rfl
    · rw [if_neg (fun h' => by rw [h] at h'; exact Cell.noConfusion h'.2), h]; rfl
  · exfalso; apply hc
    show (prec 1).eval _ = 0
    rw [pv, witRowsS_getP hq, if_neg (Nat.not_lt.2 hq7)]; rfl

theorem witS_nobus (A : List Cell) :
    ∀ r, r < (witTableS A).h → ∀ I ∈ witAirS.inters, I.bus ≠ "mem" →
      I.count.eval ((witTableS A).env r) = 0 := by
  intro q (hq : q < 2 ^ 10) I hI hb
  simp only [witAirS, witIntersS, List.mem_cons, List.not_mem_nil, or_false] at hI
  rcases hI with rfl | rfl
  · show (if (5 : Nat) = 0 then inBit A ((q + 0) % 2 ^ 10) else 0) = 0
    rfl
  · exact absurd rfl hb

-- ---------------------------------------------------------------------------
-- Balance
-- ---------------------------------------------------------------------------

/-- **A CPU, memory, program and witness balance** on the honest memory,
    when the other three send on `mem` only tuples of memory, and on no
    other bus. -/
theorem balanced4 {A : List Cell} {cpu prog wit : AirD} {C Pg Wt : Table} (hML : A.length < P)
    (hcM : ∀ r, r < C.h → ∀ I ∈ cpu.inters, I.bus = "mem" → I.count.eval (C.env r) ≠ 0 →
      ∃ m, m < A.length ∧ I.fields.map (fun c => c.eval (C.env r)) = tupleOf A m)
    (hcZ : ∀ r, r < C.h → ∀ I ∈ cpu.inters, I.bus ≠ "mem" → I.count.eval (C.env r) = 0)
    (hpM : ∀ r, r < Pg.h → ∀ I ∈ prog.inters, I.bus = "mem" → I.count.eval (Pg.env r) ≠ 0 →
      ∃ m, m < A.length ∧ I.fields.map (fun c => c.eval (Pg.env r)) = tupleOf A m)
    (hpZ : ∀ r, r < Pg.h → ∀ I ∈ prog.inters, I.bus ≠ "mem" → I.count.eval (Pg.env r) = 0)
    (hwM : ∀ r, r < Wt.h → ∀ I ∈ wit.inters, I.bus = "mem" → I.count.eval (Wt.env r) ≠ 0 →
      ∃ m, m < A.length ∧ I.fields.map (fun c => c.eval (Wt.env r)) = tupleOf A m)
    (hwZ : ∀ r, r < Wt.h → ∀ I ∈ wit.inters, I.bus ≠ "mem" → I.count.eval (Wt.env r) = 0) :
    Balanced [(cpu, C), (memAirC, memTableC A cpu prog wit C Pg Wt), (prog, Pg), (wit, Wt)] := by
  intro B v
  simp only [List.foldr_cons, List.foldr_nil]
  let Mm := memTableC A cpu prog wit C Pg Wt
  have zero_of : ∀ {X : AirD} {T : Table}, (∀ r, r < T.h → ∀ I ∈ X.inters, I.bus ≠ "mem" →
      I.count.eval (T.env r) = 0) → B ≠ "mem" → tableSends X T B v = 0 := by
    intro X T hZ hB
    apply sends_zero_of (Q := fun _ => False) _ id
    intro r hr I hI hb hc
    exact hc (hZ r hr I hI (fun h => hB (hb ▸ h)))
  by_cases hBm : B = "mem"
  · subst hBm
    have hrow : ∀ m, m < A.length → rowSends memAirC Mm "mem" v m =
        if tupleOf A m = v then -(tableSends cpu C "mem" (tupleOf A m) + (tableSends prog Pg "mem"
          (tupleOf A m) + tableSends wit Wt "mem" (tupleOf A m))) else 0 := by
      intro m hm
      have hm' : m < Mm.h := hm
      simp only [rowSends, memAirC, List.foldr_cons, List.foldr_nil, List.map_cons, List.map_nil, B.col, E.eval,
        env_main0 hm']
      have hb : ¬ ("blind_b" = "mem") := by decide
      simp only [hb, false_and, true_and, ↓reduceIte, add_zero']
      rfl
    cases hany : (List.range A.length).any (fun m => decide (tupleOf A m = v)) with
    | true =>
      obtain ⟨m0, hm0, e0⟩ := List.any_eq_true.1 hany
      have hm0 := List.mem_range.1 hm0
      have e0 := of_decide_eq_true e0
      have hmem : tableSends memAirC Mm "mem" v = -(tableSends cpu C "mem" v +
          (tableSends prog Pg "mem" v + tableSends wit Wt "mem" v)) := by
        show List.foldr (fun r acc => rowSends memAirC Mm "mem" v r + acc) 0 (List.range A.length) = _
        rw [fold_range_single _ A.length m0 hm0, hrow m0 hm0, if_pos e0, e0]
        intro b hb hne
        rw [hrow b hb, if_neg]
        intro e
        rw [← e0] at e
        have := congrArg List.head? e
        simp only [tupleOf, List.head?_cons, Option.some.injEq] at this
        exact hne (ofN_inj (Nat.lt_trans hb hML) (Nat.lt_trans hm0 hML) this)
      rw [hmem]
      show _ + (_ + (_ + (_ + 0))) = 0
      have := bal3_identity (tableSends cpu C "mem" v) (tableSends prog Pg "mem" v) (tableSends wit Wt "mem" v)
      rw [zero_add', add_zero'] at this
      rw [add_zero']; exact this
    | false =>
      have hno : ¬ ∃ m, m < A.length ∧ v = tupleOf A m := by
        rintro ⟨m, hm, e⟩
        have := List.any_eq_false.1 hany m (List.mem_range.2 hm)
        exact this (decide_eq_true e.symm)
      have h1 : tableSends cpu C "mem" v = 0 := sends_zero_of (Q := fun w => ∃ m, m < A.length ∧ w = tupleOf A m)
        (fun r hr I hI hb hc => by obtain ⟨m, hm, e⟩ := hcM r hr I hI hb hc; exact ⟨m, hm, e⟩) hno
      have h2 : tableSends prog Pg "mem" v = 0 := sends_zero_of (Q := fun w => ∃ m, m < A.length ∧ w = tupleOf A m)
        (fun r hr I hI hb hc => by obtain ⟨m, hm, e⟩ := hpM r hr I hI hb hc; exact ⟨m, hm, e⟩) hno
      have h3 : tableSends wit Wt "mem" v = 0 := sends_zero_of (Q := fun w => ∃ m, m < A.length ∧ w = tupleOf A m)
        (fun r hr I hI hb hc => by obtain ⟨m, hm, e⟩ := hwM r hr I hI hb hc; exact ⟨m, hm, e⟩) hno
      have h4 : tableSends memAirC Mm "mem" v = 0 := by
        show List.foldr (fun r acc => rowSends memAirC Mm "mem" v r + acc) 0 (List.range A.length) = 0
        apply fold_zero
        intro m hm
        rw [hrow m (List.mem_range.1 hm), if_neg (fun e => hno ⟨m, List.mem_range.1 hm, e.symm⟩)]
      rw [h1, h2, h3, h4]; decide
  · have z_mem : tableSends memAirC Mm B v = 0 := by
      apply sends_zero_of (Q := fun _ => False) _ id
      intro r hr I hI hb hc
      simp only [memAirC, List.mem_cons, List.not_mem_nil, or_false] at hI
      rcases hI with rfl | rfl
      · exact hBm hb.symm
      · apply hc
        show -((col 9).eval (Mm.env r)) = 0
        rw [B.col, E.eval, env_main0 hr]
        show -(0 : F) = 0
        decide
    rw [zero_of hcZ hBm, z_mem, zero_of hpZ hBm, zero_of hwZ hBm]; decide

-- ---------------------------------------------------------------------------
-- Completeness
-- ---------------------------------------------------------------------------

/-- **Completeness of the Sudoku circuit**: a run the Lean AIR accepts
    from the statement machine of inputs `ρ` and a puzzle with well-formed
    clues, ending at the accepting marker, over a memory of `2^16` cells
    whose cells point into it, in at most `2^16` rows (the Sudoku
    verifier's heights), gives tables that AIRs with the Sudoku circuit's
    normal forms accept, with Plonky3's selectors; they decode back to the
    memory and the run. -/
theorem sud_complete {puzzle : List Nat} (hc : CluesOK (cluesOf puzzle)) {Rs : List AirD}
    (hs : sameAirsB Rs (sudAirs puzzle) = true) {ρ : Nat → Bool}
    {A : List Cell} {k : Nat} {row : Nat → Row}
    (hA : AcceptsFrom A (stmtMachine ρ 729 (sudokuExpr (cluesOf puzzle)) ACC REJ) k row)
    (hacc : rd A (row (k - 1)).ctr (row (k - 1)).hd = some (.atom ACC))
    (hfit : Fits A) (hlen : A.length = 2 ^ 16) (hk : k ≤ 2 ^ 16) :
    ∃ C Mm Pg Wt, AcceptedP Rs [C, Mm, Pg, Wt] ∧ C.h = 2 ^ 16 ∧ Mm.h = 2 ^ 16 ∧ Wt.h = 2 ^ 10 ∧
      memOf Mm = A ∧ ∀ i, i < k → rowOf C i = row i := by
  have hb := bounded_sudoku hc
  obtain ⟨hhd, hstk, hlenm, hpub⟩ :=
    stmtMachine_public ρ (fun _ => false) 729 (sudokuExpr (cluesOf puzzle)) ACC REJ
  have htk := stmt_take ρ 729 (sudokuExpr (cluesOf puzzle)) ACC REJ
  obtain ⟨_, bhd, bstk, b732⟩ := stmt_fitsB (ρ := ρ) hb
  obtain ⟨m0, hm0⟩ : ∃ m, stmtMachine ρ 729 (sudokuExpr (cluesOf puzzle)) ACC REJ = m := ⟨_, rfl⟩
  obtain ⟨blank, hbl⟩ : ∃ m, stmtMachine (fun _ => false) 729 (sudokuExpr (cluesOf puzzle)) ACC REJ = m :=
    ⟨_, rfl⟩
  have hsa : sudAirs puzzle = [cpuAirS blank.hd blank.stk blank.heap.length ACC, memAirC, progAirS blank.heap,
      witAirS] := by rw [← hbl]; exact sudAirs_eq puzzle
  rw [hm0] at hA hhd hstk hlenm hpub htk bhd bstk b732
  rw [hbl] at hhd hstk hlenm hpub
  have hk0 := hA.pos
  have h0 : A.take m0.heap.length = m0.heap := by rw [← hA.ctr0]; exact hA.heap0
  have hmlen : m0.heap.length ≤ A.length := by
    have := congrArg List.length h0; rw [List.length_take] at this; omega
  have hAm : ∀ i, i < m0.heap.length → A.getD i .nil = m0.heap.getD i .nil := by
    intro i hi
    have := congrArg (fun l => l[i]?) h0
    simp only [List.getElem?_take, if_pos hi] at this
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, this]
  -- the input cells are `K` or `A 0 1`
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
  -- the tables
  let C := cpuTableW A row k (2 ^ 16)
  let cpu := cpuAirS blank.hd blank.stk blank.heap.length ACC
  let Pg := progTableS blank.heap
  let Wt := witTableS A
  let Mm := memTableC A cpu (progAirS blank.heap) witAirS C Pg Wt
  have hPP : P = 2013265921 := rfl
  have hcpu : Sat cpu C := by
    have := cpuS_sat hA hk (by decide) (by omega) (by decide) hacc
    have e0 : rowQ row k 0 = row 0 := by unfold rowQ; rw [if_pos hk0]
    rw [e0, hA.hd0, hA.stk0, hA.ctr0, hhd, hstk, hlenm] at this
    exact this
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
  have hacc' : Accepted (sudAirs puzzle) [C, Mm, Pg, Wt] := by
    rw [hsa]
    have z : [cpu, memAirC, progAirS blank.heap, witAirS].zip [C, Mm, Pg, Wt] =
        sudTables blank.hd blank.stk blank.heap.length blank.heap C Mm Pg Wt := rfl
    have hPg : Pg.h ≤ 2 ^ 24 := progRowsS_le (by rw [← hlenm]; omega)
    refine ⟨rfl, ?_, ?_, ?_, ?_⟩
    · rw [z]
      intro p hp
      simp only [sudTables, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl
      · exact ⟨hcpu, .inl rfl⟩
      · exact ⟨memC_sat A _ _ _ _ _ _ (by omega), .inl rfl⟩
      · exact ⟨(progS_sat _).1, .inr (progS_sat _).2⟩
      · exact ⟨(witS_sat A).1, .inr (witS_sat A).2⟩
    · rw [z]
      exact balanced4 (by omega) (cpuW_honest hA hk) cpuW_blindZero (progS_honest hpubA) (progS_nobus _)
        (witS_honest hin) (witS_nobus A)
    · rw [z]
      unfold HeightsOK sudTables
      simp only [List.foldr_cons, List.foldr_nil]
      have hC : C.h = 2 ^ 16 := rfl
      have hMm : Mm.h = 2 ^ 16 := hlen
      have hW : Wt.h = 2 ^ 10 := rfl
      show 10 * C.h + (1 * Mm.h + (1 * Pg.h + (2 * Wt.h + 0))) < P
      omega
    · rw [z]
      intro p hp
      simp only [sudTables, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl
      · show 2 ^ 16 ≤ 2 ^ 27; decide
      · show A.length ≤ 2 ^ 27; omega
      · show Pg.h ≤ 2 ^ 27; omega
      · show 2 ^ 10 ≤ 2 ^ 27; decide
  have hRs : AcceptedP Rs [C, Mm, Pg, Wt] :=
    (acceptedP_iff_of (sud_guarded puzzle) hs _).2 (accepted_transfer (sameAirsB_symm hs) hacc')
  refine ⟨C, Mm, Pg, Wt, hRs, rfl, hlen, rfl, ?_, ?_⟩
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
    have e1 : rowQ row k i = row i := by unfold rowQ; rw [if_pos hi]
    have hc' := (hA.reach i hi).1
    have hs' := AcceptsFrom.stk_le' hA hfit (by omega) i hi
    have hS := shape (rowQ_valid hA hk i (by omega))
    obtain ⟨cell, hrd, _⟩ := hS.reads 0 (by decide) rfl
    have hh := (rd_get hrd).1
    rw [e1] at hh
    show (⟨(cpuColW A row k i HD).val, (cpuColW A row k i STK).val, (cpuColW A row k i CTR).val⟩ : Row) = row i
    show (⟨(cpuCol A (rowQ row k i) HD).val, (cpuCol A (rowQ row k i) STK).val,
      (cpuCol A (rowQ row k i) CTR).val⟩ : Row) = row i
    rw [e1]
    show (⟨(ofN (row i).hd).val, (ofN (row i).stk).val, (ofN (row i).ctr).val⟩ : Row) = row i
    rw [val_ofN (by show (row i).hd < P; have : (row i).hd < (row i).ctr := hh; omega),
      val_ofN (by omega), val_ofN (by omega)]

end Circuit
