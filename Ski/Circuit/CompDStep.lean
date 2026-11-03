import Ski.Circuit.CompDKind
import Ski.Circuit.CompDDec
import Ski.Circuit.BusMatch
import Ski.Circuit.CompPStep

/-!
# The circuit with the `dec` jet: its tables, and what the lookups force

`CompDOK`: what an accepted proof of the circuit with the `dec` jet gives,
over its six tables.  The memory and segment tables provide; every other
table sends on the `mem` and `segs` buses with counts `0` or `1`
(`CompDOK.memHit`, `segHit`).  A CPU row that is not the jet's reads, steps
and halts as the composed CPU's does (`CompDOK.read`, `step`, `halt`, as
`Ski/Circuit/CompPStep.lean`'s); a DEC row's active slot reads the memory
below its key (`CompDOK.slotRead`), and its writes are in the memory
(`CompDOK.decWrite`).
-/

namespace Circuit

open B Air

/-- The circuit's six tables. -/
def compDTables (hd0 stk0 ctr0 n nilA J : Nat) (heap : List Cell) (N W : Nat) (roots : List Nat)
    (C Mm Pg Wt Sg D : Table) : List (AirD × Table) :=
  [(cpuAirDec hd0 stk0 ctr0 n nilA J, C), (memAirC, Mm), (progAirC heap N W, Pg), (witAir N W, Wt),
   (segsAir roots, Sg), (decAirB, D)]

/-- **What an accepted proof of the circuit with the `dec` jet gives.** -/
structure CompDOK (hd0 stk0 ctr0 n nilA J : Nat) (heap : List Cell) (N W : Nat) (roots : List Nat)
    (C Mm Pg Wt Sg D : Table) : Prop where
  cpu : Sat (cpuAirDec hd0 stk0 ctr0 n nilA J) C
  mem : Sat memAirC Mm
  prog : Sat (progAirC heap N W) Pg
  wit : Sat (witAir N W) Wt
  dec : Sat Dec.decAir D
  pgpre : PreIs (progAirC heap N W) Pg
  wtpre : PreIs (witAir N W) Wt
  sgpre : PreIs (segsAir roots) Sg
  bal : Balanced (compDTables hd0 stk0 ctr0 n nilA J heap N W roots C Mm Pg Wt Sg D)
  hts : HeightsOK (compDTables hd0 stk0 ctr0 n nilA J heap N W roots C Mm Pg Wt Sg D)
  two : TwoAdic (compDTables hd0 stk0 ctr0 n nilA J heap N W roots C Mm Pg Wt Sg D)

theorem actOfD_le (k j : Nat) : actOfD k j ≤ 1 := by
  unfold actOfD; split
  · split <;> decide
  · exact actOfC_le k j

theorem cpuIntersD_eq : cpuIntersD =
    [readInterD 0, readInterD 1, readInterD 2, readInterD 3,
     ⟨"mem", 1, sApp, [col CTR, c 5, fld 1, col STK]⟩,
     ⟨"mem", 1, sS, [col CTR, c 3, fld 4, fld 6]⟩,
     ⟨"mem", 1, sS, [.add (col CTR) one, c 5, col CTR, fld 7]⟩,
     ⟨"mem", 1, sS, [.add (col CTR) (c 2), c 5, fld 6, .add (col CTR) one]⟩,
     ⟨"segs", 1, sRS, [.add (col CNT) one, col ROOT]⟩,
     ⟨"mem", 1, sDec, [c 0, c 1, c 0, c 0]⟩,
     ⟨"mem", 1, sDec, [c 1, c 2, c 0, c 0]⟩,
     ⟨"mem", 1, sDec, [c 2, c 3, c 0, c 1]⟩,
     ⟨"decn", 1, sDec, [col CTR, fld 2, c 0]⟩,
     ⟨"decx", 1, .neg sDec, [col CTR, col DROOT, col DCTR]⟩,
     blindMsg "blind_c" (DECSEL + 1) true,
     ⟨"blind_a", 1, .neg (col (BLA + 4)), blindFields BLA⟩,
     ⟨"blind_b", 1, col (BLB + 4), blindFields BLB⟩] := rfl

/-- The lookup buses: memory and segments. -/
def LookupBusD (B : String) : Prop := B = "mem" ∨ B = "segs"

section

variable {hd0 stk0 ctr0 n nilA J : Nat} {heap : List Cell} {N W : Nat} {roots : List Nat}
  {C Mm Pg Wt Sg D : Table}

/-- The CPU sends on the lookup buses with counts `0` or `1`. -/
theorem cpu_senderD (hs : Sat (cpuAirDec hd0 stk0 ctr0 n nilA J) C) {B : String} (hB : LookupBusD B) :
    SenderOn B (cpuAirDec hd0 stk0 ctr0 n nilA J, C) := by
  refine ⟨fun I hI _ => ?_, fun r hr I hI hbus => ?_⟩
  · have : cpuIntersD.all (fun I => decide (1 ≤ I.weight)) = true := rfl
    exact of_decide_eq_true (List.all_eq_true.1 this I hI)
  obtain ⟨k, hk⟩ := kind_ofD hs hr
  obtain ⟨hf, _, hApp, hS, _, hRS, hDec, _⟩ := kind_factsD hr hk
  have act : ∀ j, j < 4 → ((acts.getD j zero).eval (C.env r)).val ≤ 1 := fun j hj => by
    rw [(hf j hj).1]; exact ofN_le_one (actOfD_le k j)
  change I ∈ cpuIntersD at hI
  rw [cpuIntersD_eq] at hI
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hI
  rcases hI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact act 0 (by decide)
  · exact act 1 (by decide)
  · exact act 2 (by decide)
  · exact act 3 (by decide)
  · show (sApp.eval _).val ≤ 1; rw [hApp]; exact ite_le_one _
  · show (sS.eval _).val ≤ 1; rw [hS]; exact ite_le_one _
  · show (sS.eval _).val ≤ 1; rw [hS]; exact ite_le_one _
  · show (sS.eval _).val ≤ 1; rw [hS]; exact ite_le_one _
  · show (sRS.eval _).val ≤ 1; rw [hRS]; exact ite_le_one _
  · show (sDec.eval _).val ≤ 1; rw [hDec]; exact ite_le_one _
  · show (sDec.eval _).val ≤ 1; rw [hDec]; exact ite_le_one _
  · show (sDec.eval _).val ≤ 1; rw [hDec]; exact ite_le_one _
  all_goals rcases hB with rfl | rfl <;> exact absurd hbus (by decide)

theorem dec_bus_cases {I : Inter} (hI : I ∈ Dec.decAir.inters) :
    (I.bus = "mem" ∧ ((∃ j, j < Dec.NSLOT ∧ I = Dec.slotInter j) ∨ ∃ X ∈ Dec.wcols, I.count = col X)) ∨
      I ∈ Dec.busI := by
  change I ∈ Dec.decInters at hI
  rw [Dec.decInters_split] at hI
  rcases List.mem_append.1 hI with hI | hI
  · rcases List.mem_append.1 hI with hI | hI
    · obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hI
      exact .inl ⟨rfl, .inl ⟨j, List.mem_range.1 hj, rfl⟩⟩
    · exact .inr hI
  · obtain ⟨hb, h'⟩ := Dec.writesI_mem I hI
    exact .inl ⟨hb, .inr h'⟩

theorem busI_buses : ∀ I ∈ Dec.busI, I.bus = "decn" ∨ I.bus = "decb" ∨ I.bus = "decd" ∨ I.bus = "decx" := by
  intro I hI
  simp only [Dec.busI, List.mem_cons, List.not_mem_nil, or_false] at hI
  rcases hI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

/-- DEC sends on the lookup buses with counts `0` or `1`. -/
theorem dec_senderD (hs : Sat Dec.decAir D) {B : String} (hB : LookupBusD B) : SenderOn B (Dec.decAir, D) := by
  refine ⟨fun I hI _ => ?_, fun r hr I hI hbus => ?_⟩
  · have : Dec.decAir.inters.all (fun I => decide (1 ≤ I.weight)) = true := by decide
    exact of_decide_eq_true (List.all_eq_true.1 this I hI)
  rcases dec_bus_cases hI with ⟨hm, _⟩ | hI'
  · rcases hB with rfl | rfl
    · exact bit_val_le' (dec_mem_count hr (decRowF_of hs hr) hI hbus)
    · rw [hm] at hbus; exact absurd hbus (by decide)
  · rcases busI_buses I hI' with e | e | e | e <;> rw [e] at hbus <;> rcases hB with rfl | rfl <;>
      exact absurd hbus (by decide)

theorem decB_blind {B : String} (hB : LookupBusD B) : ∀ b ∈ [("blind_c", false)], b.1 ≠ B := by
  intro b hb e
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  subst hb
  rcases hB with rfl | rfl <;> exact absurd e (by decide)

/-- The providers: the memory and segment tables. -/
def provD (p : AirD × Table) : Bool := p.1.name == "mem" || p.1.name == "segs"

variable (h : CompDOK hd0 stk0 ctr0 n nilA J heap N W roots C Mm Pg Wt Sg D)
include h

theorem CompDOK.senders {B : String} (hB : LookupBusD B) :
    ∀ p ∈ compDTables hd0 stk0 ctr0 n nilA J heap N W roots C Mm Pg Wt Sg D, provD p = false → SenderOn B p := by
  intro p hp hpr
  simp only [compDTables, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
  · exact cpu_senderD h.cpu hB
  · exact nomatch hpr
  · exact (prog_senderC h.pgpre B).on
  · exact (wit_senderC h.wtpre hB).on
  · exact nomatch hpr
  · exact senderOn_withBlocks (decB_blind hB) (dec_senderD h.dec hB)

/-- **A `mem` message with count `1` is a memory row.** -/
theorem CompDOK.memHit {v : List F}
    (hit : ∃ p ∈ compDTables hd0 stk0 ctr0 n nilA J heap N W roots C Mm Pg Wt Sg D, provD p = false ∧
      ∃ r, r < p.2.h ∧ ∃ I ∈ p.1.inters, I.bus = "mem" ∧
        I.fields.map (fun e => e.eval (p.2.env r)) = v ∧ I.count.eval (p.2.env r) = 1) :
    ∃ m, m < Mm.h ∧ [Mm.main m 0, Mm.main m 1, Mm.main m 2, Mm.main m 3] = v := by
  obtain ⟨p, hp, hpr, m, hm, hne⟩ := bus_hit_on h.bal h.hts provD (h.senders (.inl rfl)) hit
  simp only [compDTables, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
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
  · exact absurd (notBus (A := segsAir roots) rfl) hne
  · exact nomatch hpr

/-- **A `segs` message with count `1` is a segment row.** -/
theorem CompDOK.segHit {v : List F}
    (hit : ∃ p ∈ compDTables hd0 stk0 ctr0 n nilA J heap N W roots C Mm Pg Wt Sg D, provD p = false ∧
      ∃ r, r < p.2.h ∧ ∃ I ∈ p.1.inters, I.bus = "segs" ∧
        I.fields.map (fun e => e.eval (p.2.env r)) = v ∧ I.count.eval (p.2.env r) = 1) :
    ∃ i, i < Sg.h ∧ [Sg.pre i 0, Sg.pre i 1] = v := by
  obtain ⟨p, hp, hpr, m, hm, hne⟩ := bus_hit_on h.bal h.hts provD (h.senders (.inr rfl)) hit
  simp only [compDTables, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
  · exact nomatch hpr
  · exact absurd (notBus (A := memAirC) rfl) hne
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
  · exact nomatch hpr

theorem CompDOK.mem_h : Mm.h ≤ 2 ^ 27 := h.two (memAirC, Mm) (by simp [compDTables])

theorem CompDOK.cell {a t x y : F}
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
theorem CompDOK.sendD {r : Nat} (hr : r < C.h) {I : Inter} (hI : I ∈ cpuIntersD) (hbus : I.bus = "mem")
    {a t x y : F} (hf : I.fields.map (fun e => e.eval (C.env r)) = [a, t, x, y])
    (hc : I.count.eval (C.env r) = 1) :
    a.val < Mm.h ∧ (memOf Mm)[a.val]? = some (cellOf t x y) :=
  h.cell (h.memHit ⟨_, List.mem_cons_self, rfl, r, hr, I, hI, hbus, hf, hc⟩)

/-- A range check's value is below `2^24`. -/
theorem rangeVal_ltD {r : Nat} (hr : r < C.h) {j : Nat} (hj : j < 4) :
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
      rcases bit_of (range_bitD h.cpu hr hj (i := n) hn) with hb | hb <;> rw [hb]
      · rw [zero_mul', add_zero']
        exact Nat.lt_of_lt_of_le ih (Nat.pow_le_pow_right (by decide) (Nat.le_succ n))
      · rw [one_mul', val_add_nat (by rw [Nat.pow_succ] at hpow; omega), Nat.pow_succ]
        omega
  exact step RANGE_BITS (Nat.le_refl _)

/-- **An active read**: the address is below the counter, and the memory
    holds there a cell with the kind's tag and the row's fields. -/
theorem CompDOK.read {r k : Nat} (hr : r < C.h) (hk : IsKindD C r k) {j : Nat} (hj : j < 4)
    (hact : actOfD k j = 1) :
    rd (memOf Mm) (C.main r CTR).val (C.main r (addrCol j)).val =
      some (cellOf (ofN (tagOfD k j)) (C.main r (FLD + 2 * j)) (C.main r (FLD + 2 * j + 1))) := by
  obtain ⟨hf, _⟩ := kind_factsD hr hk
  obtain ⟨ha, ht⟩ := hf j hj
  rw [hact, ofN_one] at ha
  have hadr : (addrs.getD j zero).eval (C.env r) = C.main r (addrCol j) := by
    rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega) with rfl | rfl | rfl | rfl <;>
      simp [addrs, addrCol, fld, B.col, E.eval, env_main0 hr]
  have hI : readInterD j ∈ cpuIntersD := by
    rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega) with rfl | rfl | rfl | rfl <;>
      (rw [cpuIntersD_eq]; simp only [List.mem_cons, true_or, or_true])
  obtain ⟨hlt, hget⟩ := h.sendD hr hI rfl
    (a := C.main r (addrCol j)) (t := ofN (tagOfD k j)) (x := C.main r (FLD + 2 * j))
    (y := C.main r (FLD + 2 * j + 1))
    (by simp only [readInterD, List.map_cons, List.map_nil, hadr, ht, fld, B.col, E.eval, env_main0 hr]; rfl)
    ha
  -- the range check: counter = address + 1 + value, with no wrap
  have hre := range_eqD h.cpu hr hj
  rw [ha, one_mul', hadr] at hre
  have e := sub_eq_zero hre
  have hctr : C.main r CTR = (C.main r (addrCol j) + 1) + (rangeVal j).eval (C.env r) := by
    rw [← e, add_sub_cancel3]
  have hv := rangeVal_ltD h hr hj
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
theorem CompDOK.step {r k : Nat} (hr : r < C.h) (hk : IsKindD C r k) (hk4 : k < 4) :
    stepRow (memOf Mm) (rowOf C r) = some ⟨((nextHdOfC k).eval (C.env r)).val,
      ((nextStkOfC k).eval (C.env r)).val, ((nextCtrOfC k).eval (C.env r)).val⟩ := by
  obtain ⟨_, _, hApp, hS, _⟩ := kind_factsD hr hk
  have cv := col_eval hr
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 by omega) with rfl | rfl | rfl | rfl
  · -- App: read the head; write the argument's stack cell
    have r0 : rd (memOf Mm) (C.main r CTR).val (C.main r HD).val =
        some (.app (C.main r (FLD + 0)).val (C.main r (FLD + 1)).val) := h.read hr hk (j := 0) (by decide) rfl
    have w0 := h.sendD hr (I := ⟨"mem", 1, sApp, [col CTR, c 5, fld 1, col STK]⟩)
      (by rw [cpuIntersD_eq]; simp only [List.mem_cons, true_or, or_true]) rfl
      (a := C.main r CTR) (t := ofN 5) (x := C.main r (FLD + 1)) (y := C.main r STK)
      (by simp only [List.map_cons, List.map_nil, fld, cv]; rfl) (by rw [hApp]; rfl)
    rw [cellOf_cons] at w0
    have hc1 : (C.main r CTR + 1).val = (C.main r CTR).val + 1 :=
      val_add_of_lt (by have := w0.1; have := h.mem_h; have := P_big; show _ + 1 < P; omega)
    simp only [stepRow, rowOf, stepG, r0, wrs, w0.2, beq_self_eq_true, Bool.and_true, ↓reduceIte,
      List.length_cons, List.length_nil, Option.some.injEq, Air.Row.mk.injEq]
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
      Option.some.injEq, Air.Row.mk.injEq]
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
      Option.some.injEq, Air.Row.mk.injEq]
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
    have w1 := h.sendD hr (I := ⟨"mem", 1, sS, [col CTR, c 3, fld 4, fld 6]⟩)
      (by rw [cpuIntersD_eq]; simp only [List.mem_cons, true_or, or_true]) rfl
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
    have w2 := h.sendD hr (I := ⟨"mem", 1, sS, [.add (col CTR) one, c 5, col CTR, fld 7]⟩)
      (by rw [cpuIntersD_eq]; simp only [List.mem_cons, true_or, or_true]) rfl
      (a := C.main r CTR + 1) (t := ofN 5) (x := C.main r CTR) (y := C.main r (FLD + 7))
      (by simp only [List.map_cons, List.map_nil, fld, E.eval, cv, B.one, B.c, ofN_one]) hs1
    rw [cellOf_cons, hc1] at w2
    have w3 := h.sendD hr (I := ⟨"mem", 1, sS, [.add (col CTR) (c 2), c 5, fld 6, .add (col CTR) one]⟩)
      (by rw [cpuIntersD_eq]; simp only [List.mem_cons, true_or, or_true]) rfl
      (a := C.main r CTR + ofN 2) (t := ofN 5) (x := C.main r (FLD + 6)) (y := C.main r CTR + 1)
      (by simp only [List.map_cons, List.map_nil, fld, E.eval, cv, B.one, B.c, ofN_one]) hs1
    rw [cellOf_cons, hc2, hc1] at w3
    simp only [stepRow, rowOf, stepG, r0, r1, r2, r3, wrs, w1.2, w2.2, w3.2, beq_self_eq_true,
      Bool.and_true, ↓reduceIte, List.length_cons, List.length_nil, Option.some.injEq, Air.Row.mk.injEq]
    refine ⟨?_, ?_, ?_⟩
    · show _ = ((fld 2).eval _).val; rw [fld, cv]
    · show _ = ((E.add (col CTR) (c 2)).eval _).val
      simp only [E.eval, cv, B.c, hc2]
    · show _ = ((E.add (col CTR) (c 3)).eval _).val
      simp only [E.eval, cv, B.c, hc3]

/-- **A halting row halts**: its reads show a combinator short of
    arguments, or an atom. -/
theorem CompDOK.halt {r k : Nat} (hr : r < C.h) (hk : IsKindD C r k) (hk4 : 4 ≤ k) (hk11 : k < 11) :
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



theorem CompDOK.cpu_h : C.h ≤ 2 ^ 27 := h.two (cpuAirDec hd0 stk0 ctr0 n nilA J, C) (by simp [compDTables])
theorem CompDOK.dec_h : D.h ≤ 2 ^ 27 := h.two (decAirB, D) (by simp [compDTables])

omit h in
theorem slotInter_mem {j : Nat} (hj : j < Dec.NSLOT) : Dec.slotInter j ∈ decAirB.inters := by
  show Dec.slotInter j ∈ Dec.decAir.inters ++ _
  apply List.mem_append_left
  show Dec.slotInter j ∈ Dec.decInters
  rw [Dec.decInters_split]
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩))

omit h in
theorem decI_mem {I : Inter} (hI : I ∈ Dec.busI ∨ I ∈ Dec.writesI) : I ∈ decAirB.inters := by
  show I ∈ Dec.decAir.inters ++ _
  apply List.mem_append_left
  show I ∈ Dec.decInters
  rw [Dec.decInters_split]
  rcases hI with hI | hI
  · exact List.mem_append_left _ (List.mem_append_right _ hI)
  · exact List.mem_append_right _ hI

omit h in
/-- `a + (b - a) = b`, by normal forms. -/
theorem add_sub_cancel'' (a b : F) : a + (b - a) = b :=
  E.eval_eq_of_norm (e := .add (.atom (.main 0 0)) (.sub (.atom (.main 0 1)) (.atom (.main 0 0))))
    (e' := .atom (.main 0 1)) (by decide) (fun | .main 0 0 => a | .main 0 1 => b | _ => 0)

/-- **A DEC slot that is active reads the memory below the key.** -/
theorem CompDOK.slotRead {q j : Nat} (hq : q < D.h) (hj : j < Dec.NSLOT)
    (hact : (Dec.actE j).eval (D.env q) = 1) :
    (D.main q (Dec.ADDR + j)).val < (D.main q Dec.KEY).val ∧
      (memOf Mm)[(D.main q (Dec.ADDR + j)).val]? =
        some (cellOf (D.main q (Dec.TAG + j)) (D.main q (Dec.DFLD + 2 * j)) (D.main q (Dec.DFLD + 2 * j + 1))) := by
  have cv := col_eval hq
  obtain ⟨hlt, hget⟩ := h.cell (h.memHit (v := [D.main q (Dec.ADDR + j), D.main q (Dec.TAG + j),
    D.main q (Dec.DFLD + 2 * j), D.main q (Dec.DFLD + 2 * j + 1)]) ⟨(decAirB, D), by simp [compDTables], rfl, q, hq, Dec.slotInter j, slotInter_mem hj, rfl,
    by simp only [Dec.slotInter, Dec.f1, Dec.f2, List.map_cons, List.map_nil, cv], hact⟩)
  refine ⟨?_, hget⟩
  obtain ⟨_, _, _, hre⟩ := slot_cols h.dec hq hj
  rw [hact, one_mul'] at hre
  have e := sub_eq_zero hre
  have hk : D.main q Dec.KEY = (D.main q (Dec.ADDR + j) + 1) + (Dec.rangeValD j).eval (D.env q) := by
    rw [← e, add_sub_cancel3]
  have hv := rangeValD_lt h.dec hq hj
  have hm := h.mem_h
  have hP := P_big
  have h1 : (D.main q (Dec.ADDR + j) + 1).val = (D.main q (Dec.ADDR + j)).val + 1 :=
    val_add_of_lt (by show _ + 1 < P; omega)
  rw [hk, val_add_of_lt (by rw [h1]; omega), h1]
  omega

/-- **A DEC write with count `1` is in the memory.** -/
theorem CompDOK.decWrite {q : Nat} (hq : q < D.h) {I : Inter} (hI : I ∈ Dec.writesI) {a t x y : F}
    (hf : I.fields.map (fun e => e.eval (D.env q)) = [a, t, x, y]) (hc : I.count.eval (D.env q) = 1) :
    a.val < Mm.h ∧ (memOf Mm)[a.val]? = some (cellOf t x y) :=
  h.cell (h.memHit ⟨(decAirB, D), by simp [compDTables], rfl, q, hq, I, decI_mem (.inr hI),
    (Dec.writesI_mem I hI).1, hf, hc⟩)

/-- **Every row's counter** is its head address, one, and a 24-bit value. -/
theorem CompDOK.ctr_eq {r : Nat} (hr : r < C.h) :
    (C.main r HD).val < Mm.h ∧
      (C.main r CTR).val = (C.main r HD).val + 1 + ((rangeVal 0).eval (C.env r)).val := by
  obtain ⟨k, hk⟩ := kind_ofD h.cpu hr
  have hact0 : actOfD k 0 = 1 := by
    unfold actOfD actOfC; split
    · rfl
    · split <;> rfl
  have rd0 := h.read hr hk (j := 0) (by decide) hact0
  have hlt : (C.main r (addrCol 0)).val < Mm.h := by
    unfold rd at rd0
    split at rd0
    · have := (List.getElem?_eq_some_iff.1 rd0).1
      rw [memOf_length] at this; exact this
    · cases rd0
  obtain ⟨hf, _⟩ := kind_factsD hr hk
  obtain ⟨ha, _⟩ := hf 0 (by decide)
  rw [hact0, ofN_one] at ha
  have hre := range_eqD h.cpu hr (j := 0) (by decide)
  rw [ha, one_mul'] at hre
  have hadr : (addrs.getD 0 zero).eval (C.env r) = C.main r HD := by
    simp [addrs, B.col, E.eval, env_main0 hr]
  rw [hadr] at hre
  have e := sub_eq_zero hre
  have hctr : C.main r CTR = (C.main r HD + 1) + (rangeVal 0).eval (C.env r) := by
    rw [← e, add_sub_cancel3]
  have hv := rangeVal_ltD h hr (j := 0) (by decide)
  have hm := h.mem_h
  have hP := P_big
  have h0 : (C.main r HD).val < Mm.h := hlt
  have h1 : (C.main r HD + 1).val = (C.main r HD).val + 1 :=
    val_add_of_lt (by show _ + 1 < P; omega)
  refine ⟨h0, ?_⟩
  rw [hctr, val_add_of_lt (by rw [h1]; omega), h1]

theorem CompDOK.ctr_lt {r : Nat} (hr : r < C.h) : (C.main r CTR).val < 2 ^ 27 + 2 ^ 24 + 1 := by
  obtain ⟨h0, e⟩ := h.ctr_eq hr
  have hv := rangeVal_ltD h hr (j := 0) (by decide)
  have hm := h.mem_h
  omega

/-- A jet row is of kind `12`. -/
theorem CompDOK.kind12 {r : Nat} (hr : r < C.h) (hp : C.main r DECSEL = 1) : IsKindD C r 12 := by
  obtain ⟨k, hk⟩ := kind_ofD h.cpu hr
  have := hk.2.2.2
  rw [hp] at this
  by_cases e : k = 12
  · rw [← e]; exact hk
  · rw [if_neg e] at this; exact absurd this (by decide)

/-- **A jet row's reads**: the atom `J` at the head, the cell `cons p rest`
    at the stack, and the slots `K`, `I`, `K I`. -/
theorem CompDOK.jetReads {r : Nat} (hr : r < C.h) (hp : C.main r DECSEL = 1) (hJ : J < P) :
    rd (memOf Mm) (C.main r CTR).val (C.main r HD).val = some (.atom J) ∧
    rd (memOf Mm) (C.main r CTR).val (C.main r STK).val =
      some (.cons (C.main r (FLD + 2)).val (C.main r (FLD + 3)).val) ∧
    (memOf Mm)[0]? = some .K ∧ (memOf Mm)[1]? = some .I ∧ (memOf Mm)[2]? = some (.app 0 1) := by
  have hk := h.kind12 hr hp
  have p0 := dec_pinD h.cpu hr
  rw [hp, one_mul'] at p0
  have e0 := sub_eq_zero p0
  have r0 := h.read hr hk (j := 0) (by decide) rfl
  have r1 := h.read hr hk (j := 1) (by decide) rfl
  have cv := col_eval hr
  have hs1 : sDec.eval (C.env r) = 1 := by rw [show sDec.eval (C.env r) = C.main r DECSEL from cv DECSEL, hp]
  have s0 := h.sendD hr (I := ⟨"mem", 1, sDec, [c 0, c 1, c 0, c 0]⟩)
    (by rw [cpuIntersD_eq]; simp only [List.mem_cons, true_or, or_true]) rfl
    (a := ofN 0) (t := ofN 1) (x := ofN 0) (y := ofN 0) (by simp only [List.map_cons, List.map_nil, B.c, E.eval]) hs1
  have s1 := h.sendD hr (I := ⟨"mem", 1, sDec, [c 1, c 2, c 0, c 0]⟩)
    (by rw [cpuIntersD_eq]; simp only [List.mem_cons, true_or, or_true]) rfl
    (a := ofN 1) (t := ofN 2) (x := ofN 0) (y := ofN 0) (by simp only [List.map_cons, List.map_nil, B.c, E.eval]) hs1
  have s2 := h.sendD hr (I := ⟨"mem", 1, sDec, [c 2, c 3, c 0, c 1]⟩)
    (by rw [cpuIntersD_eq]; simp only [List.mem_cons, true_or, or_true]) rfl
    (a := ofN 2) (t := ofN 3) (x := ofN 0) (y := ofN 1) (by simp only [List.map_cons, List.map_nil, B.c, E.eval]) hs1
  rw [show addrCol 0 = HD from rfl, show tagOfD 12 0 = 6 from rfl, cellOf_atom, e0, val_ofN hJ] at r0
  rw [show addrCol 1 = STK from rfl, show tagOfD 12 1 = 5 from rfl, cellOf_cons,
    show FLD + 2 * 1 = FLD + 2 from rfl, show FLD + 2 * 1 + 1 = FLD + 3 from rfl] at r1
  exact ⟨r0, r1, s0.2, s1.2, s2.2⟩

/-- **A jet row's next registers**: the result's root at the head, the rest
    of the stack, and the new counter. -/
theorem CompDOK.jetNext {r : Nat} (hn : r + 1 < C.h) (hp : C.main r DECSEL = 1) :
    C.main (r + 1) HD = C.main r DROOT ∧ C.main (r + 1) STK = C.main r (FLD + 3) ∧
    C.main (r + 1) CTR = C.main r DCTR := by
  have hr : r < C.h := Nat.lt_of_succ_lt hn
  have hk := h.kind12 hr hp
  obtain ⟨_, _, _, _, _, hRS, _, h1, h2, h3⟩ := kind_factsD hr hk
  obtain ⟨e1, e2, e3⟩ := next_regsD h.cpu hr hn
  have cv := col_eval hr
  have hrs : C.main r RS = 0 := by rw [← cv RS]; exact hRS
  rw [h1, hrs, hp, zero_mul', one_mul'] at e1
  rw [h2, hrs, hp, zero_mul', one_mul'] at e2
  rw [h3, hp, one_mul'] at e3
  refine ⟨?_, ?_, ?_⟩
  · rw [e1]; show (zero).eval _ + 0 + _ = _; simp only [B.zero, B.c, E.eval, ofN_zero, zero_add', add_zero']
  · rw [e2]; show (zero).eval _ + 0 + _ = _; simp only [B.zero, B.c, E.eval, ofN_zero, zero_add', add_zero']
  · rw [e3]; show (col CTR).eval _ + _ = _; rw [cv, add_sub_cancel'']

end

end Circuit
