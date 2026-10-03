import Ski.Circuit.CompPKind
import Ski.Circuit.CompStep
import Ski.Circuit.JetSound

/-!
# The circuit with the Poseidon2 jet: its tables, and what the lookups force

`CompPOK`: what an accepted proof of the circuit with the Poseidon2 jet
gives, over its nine tables.  The memory, segment and level tables
provide; every other table sends on the `mem`, `segs` and `p2idx` buses
with counts `0` or `1` (`CompPOK.memHit`, `segHit`, `idxHit`).  A CPU row
that is not the jet's reads, steps and halts as the composed CPU's does
(`CompPOK.read`, `step`, `halt`).
-/

namespace Circuit

open B Air

/-- The circuit's nine tables. -/
def compPTables (hd0 stk0 ctr0 n nilA J root : Nat) (heap : List Cell) (N W : Nat) (roots : List Nat)
    (C Mm Pg Wt Sg Pi Po Pp Px : Table) : List (AirD × Table) :=
  [(cpuAirP2 hd0 stk0 ctr0 n nilA J root, C), (memAirC, Mm), (progAirC heap N W, Pg), (witAirP N W, Wt),
   (segsAir roots, Sg), (p2inAir, Pi), (p2outAir, Po), (P2Air.p2Air, Pp), (p2idxAir, Px)]

/-- **What an accepted proof of the circuit with the Poseidon2 jet gives.** -/
structure CompPOK (hd0 stk0 ctr0 n nilA J root : Nat) (heap : List Cell) (N W : Nat) (roots : List Nat)
    (C Mm Pg Wt Sg Pi Po Pp Px : Table) : Prop where
  cpu : Sat (cpuAirP2 hd0 stk0 ctr0 n nilA J root) C
  mem : Sat memAirC Mm
  prog : Sat (progAirC heap N W) Pg
  wit : Sat (witAirP N W) Wt
  pin : Sat p2inAir Pi
  pout : Sat p2outAir Po
  p2 : Sat P2Air.p2Air Pp
  pgpre : PreIs (progAirC heap N W) Pg
  wtpre : PreIs (witAirP N W) Wt
  sgpre : PreIs (segsAir roots) Sg
  pxpre : PreIs p2idxAir Px
  bal : Balanced (compPTables hd0 stk0 ctr0 n nilA J root heap N W roots C Mm Pg Wt Sg Pi Po Pp Px)
  hts : HeightsOK (compPTables hd0 stk0 ctr0 n nilA J root heap N W roots C Mm Pg Wt Sg Pi Po Pp Px)
  two : TwoAdic (compPTables hd0 stk0 ctr0 n nilA J root heap N W roots C Mm Pg Wt Sg Pi Po Pp Px)

/-- The providers: the memory, segment and level tables. -/
def provP (p : AirD × Table) : Bool := p.1.name == "mem" || p.1.name == "segs" || p.1.name == "p2idx"

theorem actOfP_le (k j : Nat) : actOfP k j ≤ 1 := by
  unfold actOfP; split
  · split <;> decide
  · exact actOfC_le k j

theorem cpuIntersP2_eq : cpuIntersP2 =
    [readInterP 0, readInterP 1, readInterP 2, readInterP 3,
     ⟨"mem", 1, sApp, [col CTR, c 5, fld 1, col STK]⟩,
     ⟨"mem", 1, sS, [col CTR, c 3, fld 4, fld 6]⟩,
     ⟨"mem", 1, sS, [.add (col CTR) one, c 5, col CTR, fld 7]⟩,
     ⟨"mem", 1, sS, [.add (col CTR) (c 2), c 5, fld 6, .add (col CTR) one]⟩,
     ⟨"segs", 1, sRS, [.add (col CNT) one, col ROOT]⟩,
     ⟨"mem", 1, sP2, [c 0, c 1, c 0, c 0]⟩,
     ⟨"mem", 1, sP2, [c 1, c 2, c 0, c 0]⟩,
     ⟨"mem", 1, sP2, [c 2, c 3, c 0, c 1]⟩,
     ⟨"p2i", 1, sP2, [col CTR, c 0, c 0]⟩,
     ⟨"p2i", 1, .neg sP2, [col CTR, c P2_BITS, c 0]⟩,
     ⟨"p2o", 1, sP2, [col CTR, c 0, fld 5, c 0, c 0, c 1]⟩,
     ⟨"p2o", 1, .neg sP2, [col CTR, c P2_BITS, fld 5, c 0, c 0, c 1]⟩,
     ⟨"blind_a", 1, .neg (col (BLA + 4)), blindFields BLA⟩,
     ⟨"blind_b", 1, col (BLB + 4), blindFields BLB⟩] := rfl

/-- The buses the lookups use: memory, segments, levels. -/
def LookupBus (B : String) : Prop := B = "mem" ∨ B = "segs" ∨ B = "p2idx"

section

variable {hd0 stk0 ctr0 n nilA J root : Nat} {heap : List Cell} {N W : Nat} {roots : List Nat}
  {C Mm Pg Wt Sg Pi Po Pp Px : Table}

/-- The CPU sends on the lookup buses with counts `0` or `1`. -/
theorem cpu_senderP (hs : Sat (cpuAirP2 hd0 stk0 ctr0 n nilA J root) C) {B : String} (hB : LookupBus B) :
    SenderOn B (cpuAirP2 hd0 stk0 ctr0 n nilA J root, C) := by
  refine ⟨fun I hI _ => ?_, fun r hr I hI hbus => ?_⟩
  · have : cpuIntersP2.all (fun I => decide (1 ≤ I.weight)) = true := rfl
    exact of_decide_eq_true (List.all_eq_true.1 this I hI)
  obtain ⟨k, hk⟩ := kind_ofP2 hs hr
  obtain ⟨hf, _, hApp, hS, _, hRS, hP2, _⟩ := kind_factsP hr hk
  have act : ∀ j, j < 4 → ((actsP.getD j zero).eval (C.env r)).val ≤ 1 := fun j hj => by
    rw [(hf j hj).1]; exact ofN_le_one (actOfP_le k j)
  change I ∈ cpuIntersP2 at hI
  rw [cpuIntersP2_eq] at hI
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hI
  rcases hI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact act 0 (by decide)
  · exact act 1 (by decide)
  · exact act 2 (by decide)
  · exact act 3 (by decide)
  · show (sApp.eval _).val ≤ 1; rw [hApp]; exact ite_le_one _
  · show (sS.eval _).val ≤ 1; rw [hS]; exact ite_le_one _
  · show (sS.eval _).val ≤ 1; rw [hS]; exact ite_le_one _
  · show (sS.eval _).val ≤ 1; rw [hS]; exact ite_le_one _
  · show (sRS.eval _).val ≤ 1; rw [hRS]; exact ite_le_one _
  · show (sP2.eval _).val ≤ 1; rw [hP2]; exact ite_le_one _
  · show (sP2.eval _).val ≤ 1; rw [hP2]; exact ite_le_one _
  · show (sP2.eval _).val ≤ 1; rw [hP2]; exact ite_le_one _
  all_goals rcases hB with rfl | rfl | rfl <;> exact absurd hbus (by decide)

theorem witRowsP_row (N W i : Nat) :
    ((witRowsP N W).getD i []).getD 1 0 = ofN 1 ∨ ((witRowsP N W).getD i []).getD 1 0 = ofN 0 := by
  rcases Nat.lt_or_ge i (witRowsP N W).length with h | h
  · rw [List.getD_eq_getElem?_getD (l := witRowsP N W), List.getElem?_eq_getElem h, Option.getD_some]
    have hm := List.getElem_mem h
    generalize (witRowsP N W)[i] = row at hm ⊢
    unfold witRowsP at hm
    simp only [List.mem_append, List.mem_map, List.mem_range] at hm
    rcases hm with (⟨j, _, e⟩ | ⟨j, _, e⟩) | hm
    · rw [← e]; exact .inl rfl
    · rw [← e]; exact .inl rfl
    · rw [List.eq_of_mem_replicate hm]; exact .inr rfl
  · rw [List.getD_eq_getElem?_getD (l := witRowsP N W), List.getElem?_eq_none h]; exact .inr rfl

theorem wit_senderP (hp : PreIs (witAirP N W) Wt) {B : String} (hB : LookupBus B) :
    SenderOn B (witAirP N W, Wt) := by
  refine ⟨fun I hI _ => by
      simp only [witAirP, witInters, List.mem_cons, List.not_mem_nil, or_false] at hI
      rcases hI with rfl | rfl <;> decide,
    fun r hr I hI hbus => ?_⟩
  simp only [witAirP, witInters, List.mem_cons, List.not_mem_nil, or_false] at hI
  rcases hI with rfl | rfl
  · show ((prec 1).eval _).val ≤ 1
    rw [prec_eval hp hr (by show 1 < 3; decide)]
    rcases witRowsP_row N W r with h | h <;> rw [show (witAirP N W).pretrace = witRowsP N W from rfl, h] <;> decide
  · rcases hB with rfl | rfl | rfl <;> exact absurd hbus (by decide)

/-- P2IN's activity is a bit. -/
theorem pin_act {T : Table} (hs : Sat p2inAir T) {r : Nat} (hr : r < T.h) :
    T.main r 4 * (T.main r 4 - 1) = 0 := by
  have := hs.2 _ (List.mem_cons_self) r hr
  simpa [p2inAir, E.eval, B.bool, B.col, B.one, B.c, env_main0 hr, ofN_one] using this

/-- P2OUT's activity is a bit. -/
theorem pout_act {T : Table} (hs : Sat p2outAir T) {r : Nat} (hr : r < T.h) :
    T.main r 7 * (T.main r 7 - 1) = 0 := by
  have := hs.2 _ (List.mem_cons_self) r hr
  simpa [p2outAir, E.eval, B.bool, B.col, B.one, B.c, env_main0 hr, ofN_one] using this

theorem pin_senderP (hs : Sat p2inAir Pi) {B : String} (hB : LookupBus B) : SenderOn B (p2inAir, Pi) := by
  refine ⟨fun I hI _ => by
      simp only [p2inAir, List.mem_cons, List.not_mem_nil, or_false] at hI
      rcases hI with rfl | rfl | rfl | rfl | rfl <;> decide,
    fun r hr I hI hbus => ?_⟩
  simp only [p2inAir, List.mem_cons, List.not_mem_nil, or_false] at hI
  have ha : ((col 4).eval (Pi.env r)).val ≤ 1 := by rw [col_eval hr]; exact bit_val_le (pin_act hs hr)
  rcases hI with rfl | rfl | rfl | rfl | rfl
  · exact ha
  · rcases hB with rfl | rfl | rfl <;> exact absurd hbus (by decide)
  · rcases hB with rfl | rfl | rfl <;> exact absurd hbus (by decide)
  · exact ha
  · rcases hB with rfl | rfl | rfl <;> exact absurd hbus (by decide)

theorem pout_senderP (hs : Sat p2outAir Po) {B : String} (hB : LookupBus B) : SenderOn B (p2outAir, Po) := by
  refine ⟨fun I hI _ => by
      simp only [p2outAir, List.mem_cons, List.not_mem_nil, or_false] at hI
      rcases hI with rfl | rfl | rfl | rfl | rfl <;> decide,
    fun r hr I hI hbus => ?_⟩
  simp only [p2outAir, List.mem_cons, List.not_mem_nil, or_false] at hI
  have ha : ((col 7).eval (Po.env r)).val ≤ 1 := by rw [col_eval hr]; exact bit_val_le (pout_act hs hr)
  rcases hI with rfl | rfl | rfl | rfl | rfl
  · exact ha
  · rcases hB with rfl | rfl | rfl <;> exact absurd hbus (by decide)
  · rcases hB with rfl | rfl | rfl <;> exact absurd hbus (by decide)
  · exact ha
  · rcases hB with rfl | rfl | rfl <;> exact absurd hbus (by decide)

/-- The Poseidon2 table's messages are on `p2v` and `p2w`. -/
theorem p2_bus {I : Inter} (hI : I ∈ P2Air.p2Air.inters) : I.bus = "p2v" ∨ I.bus = "p2w" := by
  simp only [P2Air.p2Air, List.mem_append, List.mem_map, List.mem_range] at hI
  rcases hI with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩
  · exact .inl rfl
  · exact .inr rfl

theorem p2_senderP {B : String} (hB : LookupBus B) : SenderOn B (P2Air.p2Air, Pp) := by
  refine ⟨fun I hI hbus => ?_, fun r _ I hI hbus => ?_⟩ <;>
    rcases p2_bus hI with e | e <;> rw [e] at hbus <;> rcases hB with rfl | rfl | rfl <;>
    exact absurd hbus (by decide)

theorem prog_senderP (hp : PreIs (progAirC heap N W) Pg) (B : String) : SenderOn B (progAirC heap N W, Pg) :=
  (prog_senderC hp B).on

variable (h : CompPOK hd0 stk0 ctr0 n nilA J root heap N W roots C Mm Pg Wt Sg Pi Po Pp Px)
include h

theorem CompPOK.senders {B : String} (hB : LookupBus B) :
    ∀ p ∈ compPTables hd0 stk0 ctr0 n nilA J root heap N W roots C Mm Pg Wt Sg Pi Po Pp Px,
      provP p = false → SenderOn B p := by
  intro p hp hpr
  simp only [compPTables, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact cpu_senderP h.cpu hB
  · exact nomatch hpr
  · exact prog_senderP h.pgpre B
  · exact wit_senderP h.wtpre hB
  · exact nomatch hpr
  · exact pin_senderP h.pin hB
  · exact pout_senderP h.pout hB
  · exact p2_senderP hB
  · exact nomatch hpr

/-- **A `mem` message with count `1` is a memory row.** -/
theorem CompPOK.memHit {v : List F}
    (hit : ∃ p ∈ compPTables hd0 stk0 ctr0 n nilA J root heap N W roots C Mm Pg Wt Sg Pi Po Pp Px,
      provP p = false ∧ ∃ r, r < p.2.h ∧ ∃ I ∈ p.1.inters, I.bus = "mem" ∧
        I.fields.map (fun e => e.eval (p.2.env r)) = v ∧ I.count.eval (p.2.env r) = 1) :
    ∃ m, m < Mm.h ∧ [Mm.main m 0, Mm.main m 1, Mm.main m 2, Mm.main m 3] = v := by
  obtain ⟨p, hp, hpr, m, hm, hne⟩ := bus_hit_on h.bal h.hts provP (h.senders (.inl rfl)) hit
  simp only [compPTables, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
  · exact nomatch hpr
  · exact nomatch hpr
  · exact absurd (notBus (A := p2idxAir) rfl) hne

/-- **A `p2idx` message with count `1` is a level row**: a row of `idxRows`. -/
theorem CompPOK.idxHit {v : List F}
    (hit : ∃ p ∈ compPTables hd0 stk0 ctr0 n nilA J root heap N W roots C Mm Pg Wt Sg Pi Po Pp Px,
      provP p = false ∧ ∃ r, r < p.2.h ∧ ∃ I ∈ p.1.inters, I.bus = "p2idx" ∧
        I.fields.map (fun e => e.eval (p.2.env r)) = v ∧ I.count.eval (p.2.env r) = 1) :
    ∃ i, i < Px.h ∧ (List.range 6).map (fun j => Px.pre i j) = v := by
  obtain ⟨p, hp, hpr, m, hm, hne⟩ := bus_hit_on h.bal h.hts provP (h.senders (.inr (.inr rfl))) hit
  simp only [compPTables, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact nomatch hpr
  · exact absurd (notBus (A := memAirC) rfl) hne
  · exact nomatch hpr
  · exact nomatch hpr
  · exact absurd (notBus (A := segsAir roots) rfl) hne
  · exact nomatch hpr
  · exact nomatch hpr
  · exact nomatch hpr
  · refine ⟨m, hm, ?_⟩
    have hm' : m < Px.h := hm
    apply Decidable.byContradiction
    intro hv
    apply hne
    show (if "p2idx" = "p2idx" ∧ ((List.range 6).map prec).map (fun e => e.eval (Px.env m)) = v then _ else 0) + 0 = 0
    have e : ((List.range 6).map prec).map (fun e => e.eval (Px.env m)) = (List.range 6).map (fun j => Px.pre m j) := by
      rw [List.map_map]
      exact List.map_congr_left fun j _ => by
        show Px.pre ((m + 0) % Px.h) j = _; rw [Nat.add_zero, Nat.mod_eq_of_lt hm']
    rw [e, if_neg (fun h' => hv h'.2), add_zero']

/-- **A `segs` message with count `1` is a segment row.** -/
theorem CompPOK.segHit {v : List F}
    (hit : ∃ p ∈ compPTables hd0 stk0 ctr0 n nilA J root heap N W roots C Mm Pg Wt Sg Pi Po Pp Px,
      provP p = false ∧ ∃ r, r < p.2.h ∧ ∃ I ∈ p.1.inters, I.bus = "segs" ∧
        I.fields.map (fun e => e.eval (p.2.env r)) = v ∧ I.count.eval (p.2.env r) = 1) :
    ∃ i, i < Sg.h ∧ [Sg.pre i 0, Sg.pre i 1] = v := by
  obtain ⟨p, hp, hpr, m, hm, hne⟩ := bus_hit_on h.bal h.hts provP (h.senders (.inr (.inl rfl))) hit
  simp only [compPTables, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
  · exact nomatch hpr
  · exact nomatch hpr
  · exact absurd (notBus (A := p2idxAir) rfl) hne

theorem CompPOK.mem_h : Mm.h ≤ 2 ^ 27 := h.two (memAirC, Mm) (by simp [compPTables])

theorem CompPOK.cell {a t x y : F}
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
theorem CompPOK.sendP {r : Nat} (hr : r < C.h) {I : Inter} (hI : I ∈ cpuIntersP2) (hbus : I.bus = "mem")
    {a t x y : F} (hf : I.fields.map (fun e => e.eval (C.env r)) = [a, t, x, y])
    (hc : I.count.eval (C.env r) = 1) :
    a.val < Mm.h ∧ (memOf Mm)[a.val]? = some (cellOf t x y) :=
  h.cell (h.memHit ⟨_, List.mem_cons_self, rfl, r, hr, I, hI, hbus, hf, hc⟩)

/-- A range check's value is below `2^24`. -/
theorem rangeVal_ltP {r : Nat} (hr : r < C.h) {j : Nat} (hj : j < 4) :
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
      rcases bit_of (range_bitP2 h.cpu hr hj (i := n) hn) with hb | hb <;> rw [hb]
      · rw [zero_mul', add_zero']
        exact Nat.lt_of_lt_of_le ih (Nat.pow_le_pow_right (by decide) (Nat.le_succ n))
      · rw [one_mul', val_add_nat (by rw [Nat.pow_succ] at hpow; omega), Nat.pow_succ]
        omega
  exact step RANGE_BITS (Nat.le_refl _)

/-- **An active read**: the address is below the counter, and the memory
    holds there a cell with the kind's tag and the row's fields. -/
theorem CompPOK.read {r k : Nat} (hr : r < C.h) (hk : IsKindP C r k) {j : Nat} (hj : j < 4)
    (hact : actOfP k j = 1) :
    rd (memOf Mm) (C.main r CTR).val (C.main r (addrCol j)).val =
      some (cellOf (ofN (tagOfP k j)) (C.main r (FLD + 2 * j)) (C.main r (FLD + 2 * j + 1))) := by
  obtain ⟨hf, _⟩ := kind_factsP hr hk
  obtain ⟨ha, ht⟩ := hf j hj
  rw [hact, ofN_one] at ha
  have hadr : (addrs.getD j zero).eval (C.env r) = C.main r (addrCol j) := by
    rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega) with rfl | rfl | rfl | rfl <;>
      simp [addrs, addrCol, fld, B.col, E.eval, env_main0 hr]
  have hI : readInterP j ∈ cpuIntersP2 := by
    rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega) with rfl | rfl | rfl | rfl <;>
      (rw [cpuIntersP2_eq]; simp only [List.mem_cons, true_or, or_true])
  obtain ⟨hlt, hget⟩ := h.sendP hr hI rfl
    (a := C.main r (addrCol j)) (t := ofN (tagOfP k j)) (x := C.main r (FLD + 2 * j))
    (y := C.main r (FLD + 2 * j + 1))
    (by simp only [readInterP, List.map_cons, List.map_nil, hadr, ht, fld, B.col, E.eval, env_main0 hr]; rfl)
    ha
  -- the range check: counter = address + 1 + value, with no wrap
  have hre := range_eqP2 h.cpu hr hj
  rw [ha, one_mul', hadr] at hre
  have e := sub_eq_zero hre
  have hctr : C.main r CTR = (C.main r (addrCol j) + 1) + (rangeVal j).eval (C.env r) := by
    rw [← e, add_sub_cancel3]
  have hv := rangeVal_ltP h hr hj
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
theorem CompPOK.step {r k : Nat} (hr : r < C.h) (hk : IsKindP C r k) (hk4 : k < 4) :
    stepRow (memOf Mm) (rowOf C r) = some ⟨((nextHdOfC k).eval (C.env r)).val,
      ((nextStkOfC k).eval (C.env r)).val, ((nextCtrOfC k).eval (C.env r)).val⟩ := by
  obtain ⟨_, _, hApp, hS, _⟩ := kind_factsP hr hk
  have cv := col_eval hr
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 by omega) with rfl | rfl | rfl | rfl
  · -- App: read the head; write the argument's stack cell
    have r0 : rd (memOf Mm) (C.main r CTR).val (C.main r HD).val =
        some (.app (C.main r (FLD + 0)).val (C.main r (FLD + 1)).val) := h.read hr hk (j := 0) (by decide) rfl
    have w0 := h.sendP hr (I := ⟨"mem", 1, sApp, [col CTR, c 5, fld 1, col STK]⟩)
      (by rw [cpuIntersP2_eq]; simp only [List.mem_cons, true_or, or_true]) rfl
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
    have w1 := h.sendP hr (I := ⟨"mem", 1, sS, [col CTR, c 3, fld 4, fld 6]⟩)
      (by rw [cpuIntersP2_eq]; simp only [List.mem_cons, true_or, or_true]) rfl
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
    have w2 := h.sendP hr (I := ⟨"mem", 1, sS, [.add (col CTR) one, c 5, col CTR, fld 7]⟩)
      (by rw [cpuIntersP2_eq]; simp only [List.mem_cons, true_or, or_true]) rfl
      (a := C.main r CTR + 1) (t := ofN 5) (x := C.main r CTR) (y := C.main r (FLD + 7))
      (by simp only [List.map_cons, List.map_nil, fld, E.eval, cv, B.one, B.c, ofN_one]) hs1
    rw [cellOf_cons, hc1] at w2
    have w3 := h.sendP hr (I := ⟨"mem", 1, sS, [.add (col CTR) (c 2), c 5, fld 6, .add (col CTR) one]⟩)
      (by rw [cpuIntersP2_eq]; simp only [List.mem_cons, true_or, or_true]) rfl
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
theorem CompPOK.halt {r k : Nat} (hr : r < C.h) (hk : IsKindP C r k) (hk4 : 4 ≤ k) (hk11 : k < 11) :
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
