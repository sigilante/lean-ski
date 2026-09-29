import Ski.Circuit.CompKind

/-!
# The composed circuit's tables, and what their buses force

`CompOK`: what an accepted proof of the composed circuit gives, over its
five tables.  The CPU, program and witness tables send on the `mem` bus
with counts `0` or `1`, the CPU on the `segs` bus; the memory and segment
tables provide (`memHitC`, `segHitC`).
-/

namespace Circuit

open B Air

/-- The composed circuit's five tables. -/
def compTables (hd0 stk0 ctr0 n nilA : Nat) (heap : List Cell) (N W : Nat) (roots : List Nat)
    (C Mm Pg Wt Sg : Table) : List (AirD × Table) :=
  [(cpuAirC hd0 stk0 ctr0 n nilA, C), (memAirC, Mm), (progAirC heap N W, Pg), (witAir N W, Wt),
   (segsAir roots, Sg)]

/-- **What an accepted proof of the composed circuit gives.** -/
structure CompOK (hd0 stk0 ctr0 n nilA : Nat) (heap : List Cell) (N W : Nat) (roots : List Nat)
    (C Mm Pg Wt Sg : Table) : Prop where
  cpu : Sat (cpuAirC hd0 stk0 ctr0 n nilA) C
  mem : Sat memAirC Mm
  prog : Sat (progAirC heap N W) Pg
  wit : Sat (witAir N W) Wt
  pgpre : PreIs (progAirC heap N W) Pg
  wtpre : PreIs (witAir N W) Wt
  sgpre : PreIs (segsAir roots) Sg
  bal : Balanced (compTables hd0 stk0 ctr0 n nilA heap N W roots C Mm Pg Wt Sg)
  hts : HeightsOK (compTables hd0 stk0 ctr0 n nilA heap N W roots C Mm Pg Wt Sg)
  two : TwoAdic (compTables hd0 stk0 ctr0 n nilA heap N W roots C Mm Pg Wt Sg)

/-- The providers: the memory and segment tables. -/
def provC (p : AirD × Table) : Bool := p.1.name == "mem" || p.1.name == "segs"

theorem bool_ne {x : Bool} (h : x = false) (h' : x = true) : False := nomatch h.symm.trans h'

theorem ofN_le_one {n : Nat} (h : n ≤ 1) : (ofN n).val ≤ 1 := by
  rw [val_ofN (Nat.lt_of_le_of_lt h (by decide))]; exact h

theorem ite_le_one (p : Prop) [Decidable p] : (ofN (if p then 1 else 0)).val ≤ 1 :=
  ofN_le_one (by split <;> decide)

theorem actOfC_le (k j : Nat) : actOfC k j ≤ 1 := by
  unfold actOfC; split
  · split <;> decide
  · exact actOf_le k j

theorem cpuIntersC_weight : ∀ I ∈ cpuIntersC, 1 ≤ I.weight := by
  intro I hI
  have : cpuIntersC.all (fun I => decide (1 ≤ I.weight)) = true := rfl
  exact of_decide_eq_true (List.all_eq_true.1 this I hI)

theorem cpuIntersC_eq : cpuIntersC =
    [readInterC 0, readInterC 1, readInterC 2, readInterC 3,
     ⟨"mem", 1, sApp, [col CTR, c 5, fld 1, col STK]⟩,
     ⟨"mem", 1, sS, [col CTR, c 3, fld 4, fld 6]⟩,
     ⟨"mem", 1, sS, [.add (col CTR) one, c 5, col CTR, fld 7]⟩,
     ⟨"mem", 1, sS, [.add (col CTR) (c 2), c 5, fld 6, .add (col CTR) one]⟩,
     ⟨"segs", 1, sRS, [.add (col CNT) one, col ROOT]⟩,
     ⟨"blind_a", 1, .neg (col (BLA + 4)), blindFields BLA⟩,
     ⟨"blind_b", 1, col (BLB + 4), blindFields BLB⟩] := rfl

section

variable {hd0 stk0 ctr0 n nilA : Nat} {heap : List Cell} {N W : Nat} {roots : List Nat}
  {C Mm Pg Wt Sg : Table}

/-- The CPU sends on `B`, for `B` the `mem` or `segs` bus. -/
theorem cpu_senderC (hs : Sat (cpuAirC hd0 stk0 ctr0 n nilA) C) {B : String} (hB : B = "mem" ∨ B = "segs") :
    Sender B (cpuAirC hd0 stk0 ctr0 n nilA, C) := by
  refine ⟨cpuIntersC_weight, fun r hr I hI hbus => ?_⟩
  obtain ⟨k, hk⟩ := kind_ofC hs hr
  obtain ⟨hf, _, hApp, hS, _, hRS, _⟩ := kind_factsC hr hk
  have act : ∀ j, j < 4 → ((acts.getD j zero).eval (C.env r)).val ≤ 1 := fun j hj => by
    rw [(hf j hj).1]; exact ofN_le_one (actOfC_le k j)
  change I ∈ cpuIntersC at hI
  rw [cpuIntersC_eq] at hI
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hI
  rcases hI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact act 0 (by decide)
  · exact act 1 (by decide)
  · exact act 2 (by decide)
  · exact act 3 (by decide)
  · show (sApp.eval _).val ≤ 1; rw [hApp]; exact ite_le_one _
  · show (sS.eval _).val ≤ 1; rw [hS]; exact ite_le_one _
  · show (sS.eval _).val ≤ 1; rw [hS]; exact ite_le_one _
  · show (sS.eval _).val ≤ 1; rw [hS]; exact ite_le_one _
  · show (sRS.eval _).val ≤ 1; rw [hRS]; exact ite_le_one _
  · rcases hB with rfl | rfl <;> exact absurd hbus (by decide)
  · rcases hB with rfl | rfl <;> exact absurd hbus (by decide)

theorem progRowsC_row (heap : List Cell) (N W i : Nat) :
    ((progRowsC heap N W).getD i []).getD 4 0 = ofN 1 ∨ ((progRowsC heap N W).getD i []).getD 4 0 = ofN 0 := by
  rcases Nat.lt_or_ge i (progRowsC heap N W).length with h | h
  · rw [List.getD_eq_getElem?_getD (l := progRowsC heap N W), List.getElem?_eq_getElem h, Option.getD_some]
    have hm := List.getElem_mem h
    generalize (progRowsC heap N W)[i] = row at hm ⊢
    unfold progRowsC at hm
    rcases List.mem_append.1 hm with hm | hm
    · obtain ⟨⟨c, j⟩, _, e⟩ := List.mem_map.1 hm
      rw [← e]; exact .inl rfl
    · rw [List.eq_of_mem_replicate hm]; exact .inr rfl
  · rw [List.getD_eq_getElem?_getD (l := progRowsC heap N W), List.getElem?_eq_none h]; exact .inr rfl

theorem prec_eval {A : AirD} {T : Table} (hp : PreIs A T) {i j : Nat} (hi : i < T.h) (hj : j < A.pre) :
    (prec j).eval (T.env i) = (A.pretrace.getD i []).getD j 0 := by
  show T.pre ((i + 0) % T.h) j = _
  rw [Nat.add_zero, Nat.mod_eq_of_lt hi, hp.2 i j hi hj]

theorem prog_senderC (hp : PreIs (progAirC heap N W) Pg) (B : String) : Sender B (progAirC heap N W, Pg) := by
  refine ⟨fun I hI => by simp only [progAirC, List.mem_cons, List.not_mem_nil, or_false] at hI; rw [hI]; decide,
    fun r hr I hI _ => ?_⟩
  simp only [progAirC, List.mem_cons, List.not_mem_nil, or_false] at hI
  subst hI
  show ((prec 4).eval _).val ≤ 1
  rw [prec_eval hp hr (by show 4 < 5; decide)]
  rcases progRowsC_row heap N W r with h | h <;> rw [show (progAirC heap N W).pretrace = progRowsC heap N W from rfl, h] <;> decide

theorem witRows_row (N W i : Nat) :
    ((witRows N W).getD i []).getD 1 0 = ofN 1 ∨ ((witRows N W).getD i []).getD 1 0 = ofN 0 := by
  rcases Nat.lt_or_ge i (witRows N W).length with h | h
  · rw [List.getD_eq_getElem?_getD (l := witRows N W), List.getElem?_eq_getElem h, Option.getD_some]
    have hm := List.getElem_mem h
    generalize (witRows N W)[i] = row at hm ⊢
    unfold witRows witRowsG at hm
    simp only [List.mem_append, List.mem_map, List.mem_range] at hm
    rcases hm with (⟨j, _, e⟩ | ⟨j, _, e⟩) | hm
    · rw [← e]; exact .inl rfl
    · rw [← e]; exact .inl rfl
    · rw [List.eq_of_mem_replicate hm]; exact .inr rfl
  · rw [List.getD_eq_getElem?_getD (l := witRows N W), List.getElem?_eq_none h]; exact .inr rfl

theorem wit_senderC (hp : PreIs (witAir N W) Wt) {B : String} (hB : B = "mem" ∨ B = "segs") :
    Sender B (witAir N W, Wt) := by
  refine ⟨fun I hI => by
      simp only [witAir, witInters, List.mem_cons, List.not_mem_nil, or_false] at hI
      rcases hI with rfl | rfl <;> decide,
    fun r hr I hI hbus => ?_⟩
  simp only [witAir, witInters, List.mem_cons, List.not_mem_nil, or_false] at hI
  rcases hI with rfl | rfl
  · rcases hB with rfl | hB
    · show ((prec 1).eval _).val ≤ 1
      rw [prec_eval hp hr (by show 1 < 3; decide)]
      rcases witRows_row N W r with h | h <;> rw [show (witAir N W).pretrace = witRows N W from rfl, h] <;> decide
    · subst hB; exact absurd hbus (by decide)
  · rcases hB with rfl | rfl <;> exact absurd hbus (by decide)

/-- The memory's address column is the row index. -/
theorem mem_addrC {Mm : Table} (hM : Sat memAirC Mm) : ∀ m, m < Mm.h → Mm.main m 0 = ofN m
  | 0, h0 => by
    have := hM.2 _ (List.mem_cons_self) 0 h0
    simp only [B.whenFirst, B.col, E.eval, env_first, env_main0 h0, ↓reduceIte, one_mul'] at this
    exact this
  | m + 1, hm => by
    have hm' : m < Mm.h := Nat.lt_of_succ_lt hm
    have := hM.2 _ (List.mem_cons_of_mem _ List.mem_cons_self) m hm'
    have ht : Mm.env m .trans = 1 := by
      rw [env_trans, if_neg (Nat.ne_of_lt hm)]
    simp only [B.whenTrans, B.eq, B.nxt, B.col, B.one, B.c, E.eval, ht, one_mul', env_main1,
      env_main0 hm', Nat.mod_eq_of_lt hm, ofN_one] at this
    rw [sub_eq_zero this, mem_addrC hM m hm', ofN_succ]

variable (h : CompOK hd0 stk0 ctr0 n nilA heap N W roots C Mm Pg Wt Sg)
include h

theorem CompOK.senders {B : String} (hB : B = "mem" ∨ B = "segs") :
    ∀ p ∈ compTables hd0 stk0 ctr0 n nilA heap N W roots C Mm Pg Wt Sg, provC p = false → Sender B p := by
  intro p hp hpr
  simp only [compTables, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl
  · exact cpu_senderC h.cpu hB
  · exact nomatch hpr
  · exact prog_senderC h.pgpre B
  · exact wit_senderC h.wtpre hB
  · exact nomatch hpr

/-- **A `mem` message with count `1` is a memory row.** -/
theorem CompOK.memHit {v : List F}
    (hit : ∃ p ∈ compTables hd0 stk0 ctr0 n nilA heap N W roots C Mm Pg Wt Sg, provC p = false ∧
      ∃ r, r < p.2.h ∧ ∃ I ∈ p.1.inters, I.bus = "mem" ∧
        I.fields.map (fun e => e.eval (p.2.env r)) = v ∧ I.count.eval (p.2.env r) = 1) :
    ∃ m, m < Mm.h ∧ [Mm.main m 0, Mm.main m 1, Mm.main m 2, Mm.main m 3] = v := by
  obtain ⟨p, hp, hpr, m, hm, hne⟩ := bus_hit h.bal h.hts provC (h.senders (.inl rfl)) hit
  simp only [compTables, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl
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
  · exact absurd (by
      show (if "segs" = "mem" ∧ _ then _ else 0) + 0 = 0
      rw [if_neg (fun h' => absurd h'.1 (by decide)), add_zero']) hne

/-- **A `segs` message with count `1` is a segment row.** -/
theorem CompOK.segHit {v : List F}
    (hit : ∃ p ∈ compTables hd0 stk0 ctr0 n nilA heap N W roots C Mm Pg Wt Sg, provC p = false ∧
      ∃ r, r < p.2.h ∧ ∃ I ∈ p.1.inters, I.bus = "segs" ∧
        I.fields.map (fun e => e.eval (p.2.env r)) = v ∧ I.count.eval (p.2.env r) = 1) :
    ∃ i, i < Sg.h ∧ [Sg.pre i 0, Sg.pre i 1] = v := by
  obtain ⟨p, hp, hpr, m, hm, hne⟩ := bus_hit h.bal h.hts provC (h.senders (.inr rfl)) hit
  simp only [compTables, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl
  · exact nomatch hpr
  · exact absurd (by
      show (if "mem" = "segs" ∧ _ then _ else 0) + ((if "blind_b" = "segs" ∧ _ then _ else 0) + 0) = 0
      rw [if_neg (fun h' => absurd h'.1 (by decide)), if_neg (fun h' => absurd h'.1 (by decide)),
        add_zero', add_zero']) hne
  · exact nomatch hpr
  · exact nomatch hpr
  · refine ⟨m, hm, ?_⟩
    have hm' : m < Sg.h := hm
    apply Decidable.byContradiction
    intro hv
    apply hne
    show (if "segs" = "segs" ∧ [(prec 0).eval (Sg.env m), (prec 1).eval (Sg.env m)] = v then _ else 0) + 0 = 0
    have e0 : (prec 0).eval (Sg.env m) = Sg.pre m 0 := by
      show Sg.pre ((m + 0) % Sg.h) 0 = _; rw [Nat.add_zero, Nat.mod_eq_of_lt hm']
    have e1 : (prec 1).eval (Sg.env m) = Sg.pre m 1 := by
      show Sg.pre ((m + 0) % Sg.h) 1 = _; rw [Nat.add_zero, Nat.mod_eq_of_lt hm']
    rw [e0, e1, if_neg (fun h' => hv h'.2), add_zero']

theorem CompOK.mem_h : Mm.h ≤ 2 ^ 27 := h.two (memAirC, Mm) (by simp [compTables])

theorem CompOK.cell {a t x y : F}
    (hm : ∃ m, m < Mm.h ∧ [Mm.main m 0, Mm.main m 1, Mm.main m 2, Mm.main m 3] = [a, t, x, y]) :
    a.val < Mm.h ∧ (memOf Mm)[a.val]? = some (cellOf t x y) := by
  obtain ⟨m, hm, e⟩ := hm
  simp only [List.cons.injEq, and_true] at e
  obtain ⟨e0, e1, e2, e3⟩ := e
  have hmP : m < P := Nat.lt_of_lt_of_le hm (Nat.le_trans h.mem_h (by decide))
  rw [mem_addrC h.mem m hm] at e0
  rw [← e0, val_ofN hmP, memOf_get hm, e1, e2, e3]
  exact ⟨hm, rfl⟩

/-- A CPU `mem` message with count `1` is a memory cell. -/
theorem CompOK.sendC {r : Nat} (hr : r < C.h) {I : Inter} (hI : I ∈ cpuIntersC) (hbus : I.bus = "mem")
    {a t x y : F} (hf : I.fields.map (fun e => e.eval (C.env r)) = [a, t, x, y])
    (hc : I.count.eval (C.env r) = 1) :
    a.val < Mm.h ∧ (memOf Mm)[a.val]? = some (cellOf t x y) :=
  h.cell (h.memHit ⟨_, List.mem_cons_self, rfl, r, hr, I, hI, hbus, hf, hc⟩)

/-- A range check's value is below `2^24`. -/
theorem rangeVal_ltC {r : Nat} (hr : r < C.h) {j : Nat} (hj : j < 4) :
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
      rcases bit_of (range_bitC h.cpu hr hj (i := n) hn) with hb | hb <;> rw [hb]
      · rw [zero_mul', add_zero']
        exact Nat.lt_of_lt_of_le ih (Nat.pow_le_pow_right (by decide) (Nat.le_succ n))
      · rw [one_mul', val_add_nat (by rw [Nat.pow_succ] at hpow; omega), Nat.pow_succ]
        omega
  exact step RANGE_BITS (Nat.le_refl _)

/-- **An active read**: the address is below the counter, and the memory
    holds there a cell with the kind's tag and the row's fields. -/
theorem CompOK.read {r k : Nat} (hr : r < C.h) (hk : IsKindC C r k) {j : Nat} (hj : j < 4)
    (hact : actOfC k j = 1) :
    rd (memOf Mm) (C.main r CTR).val (C.main r (addrCol j)).val =
      some (cellOf (ofN (tagOfC k j)) (C.main r (FLD + 2 * j)) (C.main r (FLD + 2 * j + 1))) := by
  obtain ⟨hf, _⟩ := kind_factsC hr hk
  obtain ⟨ha, ht⟩ := hf j hj
  rw [hact, ofN_one] at ha
  have hadr : (addrs.getD j zero).eval (C.env r) = C.main r (addrCol j) := by
    rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega) with rfl | rfl | rfl | rfl <;>
      simp [addrs, addrCol, fld, B.col, E.eval, env_main0 hr]
  have hI : readInterC j ∈ cpuIntersC := by
    rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega) with rfl | rfl | rfl | rfl <;>
      (rw [cpuIntersC_eq]; simp only [List.mem_cons, true_or, or_true])
  obtain ⟨hlt, hget⟩ := h.sendC hr hI rfl
    (a := C.main r (addrCol j)) (t := ofN (tagOfC k j)) (x := C.main r (FLD + 2 * j))
    (y := C.main r (FLD + 2 * j + 1))
    (by simp only [readInterC, List.map_cons, List.map_nil, hadr, ht, fld, B.col, E.eval, env_main0 hr]; rfl)
    ha
  -- the range check: counter = address + 1 + value, with no wrap
  have hre := range_eqC h.cpu hr hj
  rw [ha, one_mul', hadr] at hre
  have e := sub_eq_zero hre
  have hctr : C.main r CTR = (C.main r (addrCol j) + 1) + (rangeVal j).eval (C.env r) := by
    rw [← e, add_sub_cancel3]
  have hv := rangeVal_ltC h hr hj
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
theorem CompOK.step {r k : Nat} (hr : r < C.h) (hk : IsKindC C r k) (hk4 : k < 4) :
    stepRow (memOf Mm) (rowOf C r) = some ⟨((nextHdOfC k).eval (C.env r)).val,
      ((nextStkOfC k).eval (C.env r)).val, ((nextCtrOfC k).eval (C.env r)).val⟩ := by
  obtain ⟨_, _, hApp, hS, _⟩ := kind_factsC hr hk
  have cv := col_eval hr
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 by omega) with rfl | rfl | rfl | rfl
  · -- App: read the head; write the argument's stack cell
    have r0 : rd (memOf Mm) (C.main r CTR).val (C.main r HD).val =
        some (.app (C.main r (FLD + 0)).val (C.main r (FLD + 1)).val) := h.read hr hk (j := 0) (by decide) rfl
    have w0 := h.sendC hr (I := ⟨"mem", 1, sApp, [col CTR, c 5, fld 1, col STK]⟩)
      (by rw [cpuIntersC_eq]; simp only [List.mem_cons, true_or, or_true]) rfl
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
    have w1 := h.sendC hr (I := ⟨"mem", 1, sS, [col CTR, c 3, fld 4, fld 6]⟩)
      (by rw [cpuIntersC_eq]; simp only [List.mem_cons, true_or, or_true]) rfl
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
    have w2 := h.sendC hr (I := ⟨"mem", 1, sS, [.add (col CTR) one, c 5, col CTR, fld 7]⟩)
      (by rw [cpuIntersC_eq]; simp only [List.mem_cons, true_or, or_true]) rfl
      (a := C.main r CTR + 1) (t := ofN 5) (x := C.main r CTR) (y := C.main r (FLD + 7))
      (by simp only [List.map_cons, List.map_nil, fld, E.eval, cv, B.one, B.c, ofN_one]) hs1
    rw [cellOf_cons, hc1] at w2
    have w3 := h.sendC hr (I := ⟨"mem", 1, sS, [.add (col CTR) (c 2), c 5, fld 6, .add (col CTR) one]⟩)
      (by rw [cpuIntersC_eq]; simp only [List.mem_cons, true_or, or_true]) rfl
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
theorem CompOK.halt {r k : Nat} (hr : r < C.h) (hk : IsKindC C r k) (hk4 : 4 ≤ k) (hk11 : k < 11) :
    haltRow (memOf Mm) (rowOf C r) = true := by
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

end

end Circuit

#print axioms Circuit.CompOK.memHit
#print axioms Circuit.CompOK.segHit
#print axioms Circuit.CompOK.read
#print axioms Circuit.CompOK.step
#print axioms Circuit.CompOK.halt
