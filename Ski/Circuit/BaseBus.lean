import Ski.Circuit.BaseKind

/-!
# The memory table, and what the bus forces

- The memory table's address column is its row index (`mem_addr`).  Its
  rows decode to a list of cells, `memOf`, one per address.
- **The lookup lemma** (`lookup`): every message the CPU or the program
  table sends with count `1` has a memory row with the same tuple.  The
  sends are bits, and Plonky3's height check keeps their number below `P`,
  so a nonzero number of them cannot sum to zero in the field.
-/

namespace Circuit

open B

-- ---------------------------------------------------------------------------
-- Numbers in the field
-- ---------------------------------------------------------------------------

theorem ofN_inj {a b : Nat} (ha : a < P) (hb : b < P) (h : ofN a = ofN b) : a = b := by
  have := congrArg Fin.val h
  rwa [val_ofN ha, val_ofN hb] at this

theorem ofN_succ (m : Nat) : ofN m + 1 = ofN (m + 1) := by
  apply Fin.ext
  rw [Fin.val_add]
  show (m % P + 1 % P) % P = (m + 1) % P
  rw [← Nat.add_mod]

theorem val_add_nat {x : F} {n : Nat} (h : x.val + n < P) : (x + ofN n).val = x.val + n := by
  rw [Fin.val_add, val_ofN (Nat.lt_of_le_of_lt (Nat.le_add_left n x.val) h), Nat.mod_eq_of_lt h]

theorem P_big : 2 ^ 27 + 2 ^ 24 + 8 < P := by decide

-- ---------------------------------------------------------------------------
-- Sums of small elements
-- ---------------------------------------------------------------------------

/-- A sum of elements each at most `w`, with the bound below `P`: its value
    bounds each term's, and the number of terms times `w` bounds it. -/
theorem fold_val {α : Type} (f : α → F) (w : Nat) : ∀ (l : List α), (∀ a ∈ l, (f a).val ≤ w) →
    l.length * w < P →
    (l.foldr (fun a acc => f a + acc) 0).val ≤ l.length * w ∧
      ∀ a ∈ l, (f a).val ≤ (l.foldr (fun a acc => f a + acc) 0).val
  | [], _, _ => ⟨Nat.zero_le _, fun _ h => nomatch h⟩
  | a :: l, hb, hs => by
    have ha := hb a (List.mem_cons_self)
    have hl : l.length * w < P := Nat.lt_of_le_of_lt
      (Nat.mul_le_mul_right w (Nat.le_succ _)) hs
    obtain ⟨ih1, ih2⟩ := fold_val f w l (fun b hb' => hb b (List.mem_cons_of_mem _ hb')) hl
    simp only [List.foldr_cons, List.length_cons] at hs ⊢
    have hlt : (f a).val + (l.foldr (fun a acc => f a + acc) 0).val < P := by
      rw [Nat.succ_mul] at hs; omega
    rw [Fin.val_add, Nat.mod_eq_of_lt hlt]
    refine ⟨by rw [Nat.succ_mul]; omega, fun b hb' => ?_⟩
    rcases List.mem_cons.1 hb' with rfl | hb'
    · exact Nat.le_add_right _ _
    · exact Nat.le_trans (ih2 b hb') (Nat.le_add_left _ _)

theorem fold_zero {α : Type} (f : α → F) : ∀ (l : List α), (∀ a ∈ l, f a = 0) →
    l.foldr (fun a acc => f a + acc) 0 = 0
  | [], _ => rfl
  | a :: l, h => by
    simp only [List.foldr_cons]
    rw [h a List.mem_cons_self, fold_zero f l (fun b hb => h b (List.mem_cons_of_mem _ hb)), zero_add']

-- ---------------------------------------------------------------------------
-- The memory table
-- ---------------------------------------------------------------------------

/-- **The address column is the row index.** -/
theorem mem_addr {Mm : Table} (hM : Sat memAir Mm) : ∀ m, m < Mm.h → Mm.main m 0 = ofN m
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
    rw [sub_eq_zero this, mem_addr hM m hm', ofN_succ]

/-- A memory row's cell: its tag and fields decoded. -/
def cellOf (tag a b : F) : Cell :=
  match tag.val with
  | 0 => .S
  | 1 => .K
  | 2 => .I
  | 3 => .app a.val b.val
  | 4 => .nil
  | 5 => .cons a.val b.val
  | 6 => .atom a.val
  | _ => .nil

/-- **The memory the table holds**: one cell per address. -/
def memOf (Mm : Table) : List Cell :=
  (List.range Mm.h).map fun m => cellOf (Mm.main m 1) (Mm.main m 2) (Mm.main m 3)

theorem memOf_length (Mm : Table) : (memOf Mm).length = Mm.h := by simp [memOf]

theorem memOf_get {Mm : Table} {m : Nat} (hm : m < Mm.h) :
    (memOf Mm)[m]? = some (cellOf (Mm.main m 1) (Mm.main m 2) (Mm.main m 3)) := by
  simp [memOf, hm]

/-- A cell encoded and decoded. -/
theorem cellOf_enc (c : Cell) (h1 : (cellFields c).1 < P) (h2 : (cellFields c).2 < P) :
    cellOf (ofN (cellTag c)) (ofN (cellFields c).1) (ofN (cellFields c).2) = c := by
  cases c <;> simp only [cellOf, cellTag, cellFields] at h1 h2 ⊢ <;>
    first | rfl | (rw [val_ofN (by decide)]; simp only [val_ofN h1, val_ofN h2])

-- ---------------------------------------------------------------------------
-- The bus
-- ---------------------------------------------------------------------------

/-- The three tables of the corpus circuit. -/
def baseTables (hd0 stk0 ctr0 : Nat) (heap : List Cell) (C Mm Pg : Table) : List (AirD × Table) :=
  [(cpuAir hd0 stk0 ctr0, C), (memAir, Mm), (progAir heap, Pg)]

theorem cpuInters_weight : cpuInters.foldr (fun I a => I.weight + a) 0 = 8 := rfl

theorem heights {hd0 stk0 ctr0 : Nat} {heap : List Cell} {C Mm Pg : Table}
    (hH : HeightsOK (baseTables hd0 stk0 ctr0 heap C Mm Pg)) : C.h * 8 + Pg.h < P := by
  unfold HeightsOK baseTables at hH
  simp only [List.foldr_cons, List.foldr_nil, cpuAir, memAir, progAir, cpuInters_weight] at hH
  rw [Nat.mul_comm]; omega

/-- A CPU row's messages have counts `0` or `1`. -/
theorem cpu_count {hd0 stk0 ctr0 : Nat} {C : Table} (hC : Sat (cpuAir hd0 stk0 ctr0) C) {r : Nat}
    (hr : r < C.h) : ∀ I ∈ cpuInters, (I.count.eval (C.env r)).val ≤ 1 := by
  obtain ⟨k, hk, hsel⟩ := kind_of (hC.row hr) hr
  obtain ⟨hj, _, ha, hs, _⟩ := kind_facts hr ⟨hk, hsel⟩
  have b01 : ∀ n, n ≤ 1 → (ofN n).val ≤ 1 := fun n hn => by
    rw [val_ofN (Nat.lt_of_le_of_lt hn (by decide))]; exact hn
  have act : ∀ j, j < 4 → ((acts.getD j zero).eval (C.env r)).val ≤ 1 := fun j hj' => by
    rw [(hj j hj').1]
    apply b01
    unfold actOf
    split <;> (try split) <;> decide
  intro I hI
  simp only [cpuInters, writeInters, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false] at hI
  rcases hI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact act 0 (by decide)
  · exact act 1 (by decide)
  · exact act 2 (by decide)
  · exact act 3 (by decide)
  · show (sApp.eval _).val ≤ 1; rw [ha]; apply b01; split <;> decide
  all_goals (show (sS.eval _).val ≤ 1; rw [hs]; apply b01; split <;> decide)

/-- The program table's rows: a heap cell, active, or padding. -/
theorem programRows_row (heap : List Cell) (i : Nat) :
    ((programRows heap).getD i []).getD 4 0 = ofN 1 ∨ ((programRows heap).getD i []).getD 4 0 = ofN 0 := by
  rcases Nat.lt_or_ge i (programRows heap).length with h | h
  · rw [List.getD_eq_getElem?_getD (l := programRows heap), List.getElem?_eq_getElem h, Option.getD_some]
    have hm := List.getElem_mem h
    generalize (programRows heap)[i] = row at hm ⊢
    unfold programRows at hm
    rcases List.mem_append.1 hm with hm | hm
    · obtain ⟨⟨c, j⟩, _, e⟩ := List.mem_map.1 hm
      rw [← e]; exact .inl rfl
    · rw [List.eq_of_mem_replicate hm]; exact .inr rfl
  · rw [List.getD_eq_getElem?_getD (l := programRows heap), List.getElem?_eq_none h]; exact .inr rfl

theorem prog_count {heap : List Cell} {Pg : Table} (hPre : PreIs (progAir heap) Pg) {i : Nat}
    (hi : i < Pg.h) : ((prec 4).eval (Pg.env i)).val ≤ 1 := by
  show (Pg.pre ((i + 0) % Pg.h) 4).val ≤ 1
  rw [Nat.add_zero, Nat.mod_eq_of_lt hi, hPre.2 i 4 hi (by show 4 < 5; decide)]
  rcases programRows_row heap i with h | h <;> rw [show (progAir heap).pretrace = programRows heap from rfl, h] <;>
    decide

/-- **The lookup lemma**: a message sent with count `1` by the CPU or the
    program table has a memory row with its tuple. -/
theorem lookup {hd0 stk0 ctr0 : Nat} {heap : List Cell} {C Mm Pg : Table}
    (hC : Sat (cpuAir hd0 stk0 ctr0) C) (hPre : PreIs (progAir heap) Pg)
    (hB : Balanced (baseTables hd0 stk0 ctr0 heap C Mm Pg))
    (hH : HeightsOK (baseTables hd0 stk0 ctr0 heap C Mm Pg)) (v : List F)
    (hsend : (∃ r, r < C.h ∧ ∃ I ∈ cpuInters, I.bus = "mem" ∧
        I.fields.map (fun e => e.eval (C.env r)) = v ∧ I.count.eval (C.env r) = 1) ∨
      (∃ i, i < Pg.h ∧ [prec 0, prec 1, prec 2, prec 3].map (fun e => e.eval (Pg.env i)) = v ∧
        (prec 4).eval (Pg.env i) = 1)) :
    ∃ m, m < Mm.h ∧ [Mm.main m 0, Mm.main m 1, Mm.main m 2, Mm.main m 3] = v := by
  cases hany : (List.range Mm.h).any (fun m => decide ([Mm.main m 0, Mm.main m 1, Mm.main m 2, Mm.main m 3] = v)) with
  | true =>
    obtain ⟨m, hm, e⟩ := List.any_eq_true.1 hany
    exact ⟨m, List.mem_range.1 hm, of_decide_eq_true e⟩
  | false =>
    exfalso
    have hno : ∀ m, m < Mm.h → [Mm.main m 0, Mm.main m 1, Mm.main m 2, Mm.main m 3] ≠ v := by
      intro m hm e
      have := List.any_eq_false.1 hany m (List.mem_range.2 hm)
      exact this (decide_eq_true e)
    have hH' := heights hH
    have hb := hB "mem" v
    unfold baseTables at hb
    simp only [List.foldr_cons, List.foldr_nil] at hb
    -- the memory table sends nothing with this tuple
    have hmem : tableSends memAir Mm "mem" v = 0 := by
      apply fold_zero
      intro m hm
      have hm := List.mem_range.1 hm
      show (if "mem" = "mem" ∧ [(col 0).eval (Mm.env m), (col 1).eval (Mm.env m), (col 2).eval (Mm.env m),
        (col 3).eval (Mm.env m)] = v then _ else 0) + 0 = 0
      simp only [B.col, E.eval, env_main0 hm]
      rw [if_neg (fun h => hno m hm h.2), add_zero']
    rw [hmem, zero_add', add_zero'] at hb
    -- the CPU's and the program table's sends, as numbers
    have hrow : ∀ r, r < C.h → ∀ I ∈ cpuInters,
        ((if I.bus = "mem" ∧ I.fields.map (fun e => e.eval (C.env r)) = v then I.count.eval (C.env r)
          else 0)).val ≤ 1 := by
      intro r hr I hI
      split
      · exact cpu_count hC hr I hI
      · exact Nat.zero_le _
    have hcpu := fun r (hr : r < C.h) => fold_val (fun I => if I.bus = "mem" ∧
        I.fields.map (fun e => e.eval (C.env r)) = v then I.count.eval (C.env r) else 0) 1 cpuInters
      (hrow r hr) (by rw [show cpuInters.length = 8 from rfl]; decide)
    have hC' := fold_val (fun r => rowSends (cpuAir hd0 stk0 ctr0) C "mem" v r) 8 (List.range C.h)
      (fun r hr => (hcpu r (List.mem_range.1 hr)).1) (by rw [List.length_range]; omega)
    have hP' := fold_val (fun i => rowSends (progAir heap) Pg "mem" v i) 1 (List.range Pg.h)
      (fun i hi => by
        have hi := List.mem_range.1 hi
        show ((if _ then _ else 0) + 0 : F).val ≤ 1
        rw [add_zero']
        split
        · exact prog_count hPre hi
        · exact Nat.zero_le _)
      (by rw [List.length_range]; omega)
    rw [List.length_range] at hC' hP'
    have hsum : (tableSends (cpuAir hd0 stk0 ctr0) C "mem" v).val +
        (tableSends (progAir heap) Pg "mem" v).val = 0 := by
      have e := congrArg Fin.val hb
      rw [Fin.val_add, Nat.mod_eq_of_lt (by
        show (tableSends (cpuAir hd0 stk0 ctr0) C "mem" v).val + (tableSends (progAir heap) Pg "mem" v).val < P
        unfold tableSends; omega)] at e
      exact e
    rcases hsend with ⟨r, hr, I, hI, hbus, hf, hc⟩ | ⟨i, hi, hf, hc⟩
    · have h1 := (hcpu r hr).2 I hI
      have h2 := hC'.2 r (List.mem_range.2 hr)
      simp only [if_pos (And.intro hbus hf), hc] at h1
      have : (1 : F).val = 1 := rfl
      unfold tableSends at hsum
      change _ ≤ (rowSends (cpuAir hd0 stk0 ctr0) C "mem" v r).val at h1
      omega
    · have h2 := hP'.2 i (List.mem_range.2 hi)
      have h1 : (rowSends (progAir heap) Pg "mem" v i).val = 1 := by
        show ((if "mem" = "mem" ∧ [prec 0, prec 1, prec 2, prec 3].map (fun e => e.eval (Pg.env i)) = v
          then (prec 4).eval (Pg.env i) else 0) + 0 : F).val = 1
        rw [if_pos ⟨rfl, hf⟩, hc]; rfl
      unfold tableSends at hsum
      omega

end Circuit
