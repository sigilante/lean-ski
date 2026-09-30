import Ski.Circuit.CompWitT

/-!
# Completeness of the composed circuit

A run the Lean AIR with segments accepts, from the composed machine of
literal bits and a well-formed region, over a memory of `2^11` cells in
`2^11` rows (the composed verifier's heights), gives honest tables the
composed circuit accepts, decoding back to the run (`comp_complete`).
-/

namespace Circuit

open B Air Compose CompM Stmt Mach Wit

/-- Every row up to the last end lies in a segment. -/
theorem seg_cover {e : Nat → Nat} {n : Nat} : ∀ j, j < n → ∀ i, i ≤ e j →
    ∃ j', j' ≤ j ∧ segStart e j' ≤ i ∧ i ≤ e j'
  | 0, _, i, hi => ⟨0, Nat.le_refl _, Nat.zero_le _, hi⟩
  | j + 1, hj, i, hi => by
    rcases Nat.lt_or_ge (e j) i with h | h
    · exact ⟨j + 1, Nat.le_refl _, Nat.succ_le_of_lt h, hi⟩
    · obtain ⟨j', h1, h2, h3⟩ := seg_cover (e := e) (n := n) j (by omega) i h
      exact ⟨j', by omega, h2, h3⟩

/-- **Every row's counter is within the memory.** -/
theorem AcceptsC.ctr_le {M : List Cell} {m0 : Mach} {roots : List Nat} {nilA n : Nat} {e : Nat → Nat}
    {row : Nat → Row} (h : AcceptsC M m0 roots nilA n e row) :
    ∀ i, i ≤ e (n - 1) → (row i).ctr ≤ M.length := by
  intro i hi
  have hn := h.npos
  obtain ⟨j, hj, h1, h2⟩ := seg_cover (e := e) (n := n) (n - 1) (by omega) i hi
  obtain ⟨hc, _⟩ := h.runs j (by omega)
  have hs := h.segment (j := j) (by omega) hc
  obtain ⟨hr, _⟩ := hs.reach (i - segStart e j) (by omega)
  rwa [show segStart e j + (i - segStart e j) = i by omega] at hr

-- ---------------------------------------------------------------------------
-- The other honest tables
-- ---------------------------------------------------------------------------

def progTableC (heap : List Cell) (N W : Nat) : Table :=
  ⟨(progRowsC heap N W).length, fun _ _ => 0, fun q j => ((progRowsC heap N W).getD q []).getD j 0⟩

def segsTableC (roots : List Nat) (cpu : AirD) (C : Table) : Table :=
  ⟨(segRows roots).length,
   fun q _ => if q < roots.length then tableSends cpu C "segs" [ofN q, ofN (roots.getD q 0)] else 0,
   fun q j => ((segRows roots).getD q []).getD j 0⟩

/-- The honest memory table of the composed circuit: one row per cell, its
    multiplicity the lookups of its tuple, the blinding flag clear. -/
def memTableC (A : List Cell) (cpu prog wit : AirD) (C Pg Wt : Table) : Table :=
  ⟨A.length, fun m col =>
    if col = 0 then ofN m
    else if col = 1 then ofN (cellTag (A.getD m .nil))
    else if col = 2 then ofN (cellFields (A.getD m .nil)).1
    else if col = 3 then ofN (cellFields (A.getD m .nil)).2
    else if col = 4 then tableSends cpu C "mem" (tupleOf A m) + (tableSends prog Pg "mem" (tupleOf A m) +
      tableSends wit Wt "mem" (tupleOf A m))
    else 0,
   fun _ _ => 0⟩

theorem pow2From_ge : ∀ (f p n : Nat), p ≤ pow2From f p n
  | 0, _, _ => Nat.le_refl _
  | f + 1, p, n => by
    unfold pow2From
    split
    · exact Nat.le_trans (by omega) (pow2From_ge f (2 * p) n)
    · exact Nat.le_refl _

theorem progRowsC_pos (heap : List Cell) (N W : Nat) : 0 < (progRowsC heap N W).length := by
  have := pow2From_ge 64 (2 ^ 8) ((heap.zipIdx.filter fun x => !(3 ≤ x.2 && x.2 < 3 + N + W)).length)
  unfold progRowsC pow2Min
  simp only [List.length_append, List.length_map, List.length_replicate]
  have : (0 : Nat) < 2 ^ 8 := by decide
  omega

theorem segRows_pos (roots : List Nat) : 0 < (segRows roots).length := by
  have := pow2From_ge 64 (2 ^ 8) (roots.zipIdx.map fun x => [ofN x.2, ofN x.1]).length
  unfold segRows pow2Min
  simp only [List.length_append, List.length_replicate]
  have : (0 : Nat) < 2 ^ 8 := by decide
  omega

theorem progC_sat (heap : List Cell) (N W : Nat) :
    Sat (progAirC heap N W) (progTableC heap N W) ∧ PreIs (progAirC heap N W) (progTableC heap N W) := by
  refine ⟨⟨progRowsC_pos heap N W,
    fun c hc i hi => ?_⟩, ⟨rfl, fun _ _ _ _ => rfl⟩⟩
  simp only [progAirC, List.mem_cons, List.not_mem_nil, or_false] at hc
  subst hc
  show (progTableC heap N W).main ((i + 0) % _) 0 = 0
  rfl

/-- **The program table's messages are honest**, given the public cells in memory. -/
theorem progC_honest {A heap : List Cell} {N W : Nat}
    (hpub : ∀ i, i < heap.length → ¬ (3 ≤ i ∧ i < 3 + N + W) → i < A.length ∧ A.getD i .nil = heap.getD i .nil) :
    ∀ r, r < (progTableC heap N W).h → ∀ I ∈ (progAirC heap N W).inters,
      I.count.eval ((progTableC heap N W).env r) ≠ 0 →
      ∃ m, m < A.length ∧ I.fields.map (fun e => e.eval ((progTableC heap N W).env r)) = tupleOf A m := by
  intro q hq I hI hc
  simp only [progAirC, List.mem_cons, List.not_mem_nil, or_false] at hI
  subst hI
  have pv : ∀ j, (prec j).eval ((progTableC heap N W).env q) = ((progRowsC heap N W).getD q []).getD j 0 := by
    intro j; show (progTableC heap N W).pre ((q + 0) % _) j = _; rw [Nat.add_zero, Nat.mod_eq_of_lt hq]; rfl
  let pub := heap.zipIdx.filter fun x => !(3 ≤ x.2 && x.2 < 3 + N + W)
  let rows := pub.map fun (x : Cell × Nat) =>
    [ofN x.2, ofN (cellTag x.1), ofN (cellFields x.1).1, ofN (cellFields x.1).2, ofN 1]
  have hrows : progRowsC heap N W = rows ++ List.replicate (pow2Min 8 rows.length - rows.length)
      [ofN 0, ofN 0, ofN 0, ofN 0, ofN 0] := rfl
  rcases Nat.lt_or_ge q rows.length with hl | hl
  · have hg : (progRowsC heap N W).getD q [] = rows[q] := by
      rw [hrows, List.getD_eq_getElem?_getD, List.getElem?_append_left hl, List.getElem?_eq_getElem hl]; rfl
    have hm : rows[q] ∈ rows := List.getElem_mem hl
    obtain ⟨⟨c, i⟩, hmp, he⟩ := List.mem_map.1 hm
    obtain ⟨hz, hp⟩ := List.mem_filter.1 hmp
    obtain ⟨_, hi, hc'⟩ := List.mem_zipIdx hz
    simp only [Nat.zero_add, Nat.sub_zero] at hi hc'
    have hp' : ¬ (3 ≤ i ∧ i < 3 + N + W) := by
      simp only [Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not] at hp
      rintro ⟨h1, h2⟩; rcases hp with h | h <;> contradiction
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
    rcases Nat.lt_or_ge q (rows ++ List.replicate (pow2Min 8 rows.length - rows.length)
        [ofN 0, ofN 0, ofN 0, ofN 0, ofN 0]).length with h' | h'
    · rw [List.getElem?_append_right hl, List.getElem?_replicate]
      simp only [List.length_append, List.length_replicate] at h'
      rw [if_pos (by omega)]; rfl
    · rw [List.getElem?_eq_none h']; rfl

section

variable {a0 : Nat} {A : List Cell} {N W : Nat} (ha0 : 0 < N → 2 ≤ a0)
  (hbits : ∀ i, i < N → A.getD (a0 + i) .nil = .K ∨ A.getD (a0 + i) .nil = .app 0 1)
  (hreg : ∀ i, i < W → cellOK (a0 + N + i) (A.getD (a0 + N + i) .nil) = true)
  (hsmall : a0 + N + W ≤ 2 ^ 24) (hlen : a0 + N + W ≤ A.length)
include ha0 hbits hreg hlen

/-- **The witness table's messages are honest.** -/
theorem witT_honest : ∀ r, r < (witTableG a0 A N W).h → ∀ I ∈ (witAir N W).inters, I.bus = "mem" →
    I.count.eval ((witTableG a0 A N W).env r) ≠ 0 →
    ∃ m, m < A.length ∧ I.fields.map (fun e => e.eval ((witTableG a0 A N W).env r)) = tupleOf A m := by
  intro q hq I hI hbus hc
  simp only [witAir, witInters, List.mem_cons, List.not_mem_nil, or_false] at hI
  rcases hI with rfl | rfl
  · have pv := witT_penv (a0 := a0) (A := A) hq
    have ev := witT_env (a0 := a0) (A := A) hq
    rcases Nat.lt_or_ge q (N + W) with hact | hact
    · obtain ⟨hok, _⟩ := wit_cell ha0 hbits hreg hact
      obtain ⟨vf, va, vb, _, _⟩ := witCol_active (a0 := a0) (A := A) hact
      have hpre := witRowsG_get (a0 := a0) (N := N) (W := W) hact
      refine ⟨a0 + q, by omega, ?_⟩
      simp only [List.map_cons, List.map_nil, E.eval, pv, hpre, ev, B.c, vf 1 (by decide), vf 2 (by decide),
        vf 3 (by decide), va, vb]
      unfold tupleOf
      generalize A.getD (a0 + q) .nil = cell at hok ⊢
      rcases cellOK_cases hok with rfl | rfl | rfl | ⟨x, y, rfl, _, _⟩
      · rfl
      · rfl
      · rfl
      · rfl
    · exfalso; apply hc
      show (prec 1).eval _ = 0
      rw [pv, witRowsG_pad (by omega) hq]; rfl
  · exact absurd hbus (by decide)

end

section

variable {A : List Cell} {m0 : Mach} {roots : List Nat} {nilA n : Nat} {e : Nat → Nat} {row : Nat → Row}
  (hA : AcceptsC A m0 roots nilA n e row) {K : Nat} (hK : e (n - 1) < K)
include hA hK

/-- **The composed CPU's `mem` messages are honest.** -/
theorem cpuC_honest : ∀ r, r < (cpuTableC A row e n roots K).h → ∀ I ∈ cpuIntersC, I.bus = "mem" →
    I.count.eval ((cpuTableC A row e n roots K).env r) ≠ 0 →
    ∃ m, m < A.length ∧ I.fields.map (fun c => c.eval ((cpuTableC A row e n roots K).env r)) = tupleOf A m := by
  intro r (hr : r < K) I hI hbus hc
  obtain ⟨I0, hI0, ec, ef⟩ := cpuC_memSend hA hK (roots := roots) hr hI hbus
  obtain ⟨m, hm, e'⟩ := cpu_honest (M := A) (row := rowP row e n) (k := K) (fun i hi => valid_rowP hA hK hi)
    r hr I0 hI0 (by rw [ec]; exact hc)
  exact ⟨m, hm, by rw [← ef, e']⟩

/-- **The composed CPU's `segs` messages are honest**: a restart looks up
    the next segment's row. -/
theorem cpuC_segsHonest (hn : roots.length = n) : ∀ r, r < (cpuTableC A row e n roots K).h → ∀ I ∈ cpuIntersC,
    I.bus = "segs" → I.count.eval ((cpuTableC A row e n roots K).env r) ≠ 0 →
    ∃ q, q < roots.length ∧
      I.fields.map (fun c => c.eval ((cpuTableC A row e n roots K).env r)) = [ofN q, ofN (roots.getD q 0)] := by
  intro r (hr : r < K) I hI hbus hc
  have cv := cpuC_col hA hK (roots := roots) hr
  change I ∈ cpuIntersC at hI
  rw [cpuIntersC_eq] at hI
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hI
  rcases hI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact absurd hbus (by decide) | skip
  have hrs : isRestart e n r = true := by
    cases h' : isRestart e n r with
    | true => rfl
    | false =>
      exfalso; apply hc
      show (col RS).eval _ = 0
      rw [cv, cpuColC_rs]; unfold rsI; rw [h']; rfl
  obtain ⟨j, hj, rfl⟩ := isRestart_iff.1 hrs
  refine ⟨j + 1, by omega, ?_⟩
  simp only [List.map_cons, List.map_nil, E.eval, cv, B.one, B.c, ofN_one, cpuColC_cnt, cpuColC_root,
    cntS_end hA.emono j (by omega)]
  rw [← ofN_one, ← ofN_add]

theorem cpuC_blindZero : ∀ r, r < (cpuTableC A row e n roots K).h → ∀ I ∈ cpuIntersC, I.bus ≠ "mem" →
    I.bus ≠ "segs" → I.count.eval ((cpuTableC A row e n roots K).env r) = 0 := by
  intro r (hr : r < K) I hI h1 h2
  have cv := cpuC_col hA hK (roots := roots) hr
  change I ∈ cpuIntersC at hI
  rw [cpuIntersC_eq] at hI
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hI
  rcases hI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact absurd rfl h1 | exact absurd rfl h2 | skip
  · show -((col (BLA + 4)).eval _) = 0
    rw [cv, cpuColC_blind _ (.inl rfl)]; decide
  · show (col (BLB + 4)).eval _ = 0
    rw [cv, cpuColC_blind _ (.inr rfl)]

end

-- ---------------------------------------------------------------------------
-- Every bus balances
-- ---------------------------------------------------------------------------

/-- A table whose messages on `B` are honest sends nothing with a tuple no
    honest message carries. -/
theorem sends_zero_of {A : AirD} {T : Table} {B : String} {v : List F} {Q : List F → Prop}
    (hh : ∀ r, r < T.h → ∀ I ∈ A.inters, I.bus = B → I.count.eval (T.env r) ≠ 0 →
      Q (I.fields.map fun c => c.eval (T.env r)))
    (hno : ¬ Q v) : tableSends A T B v = 0 := by
  unfold tableSends
  apply fold_zero
  intro r hr
  unfold rowSends
  apply fold_zero
  intro I hI
  split
  · next hc =>
    by_cases h0 : I.count.eval (T.env r) = 0
    · exact h0
    · exact absurd (hc.2 ▸ hh r (List.mem_range.1 hr) I hI hc.1 h0) hno
  · rfl

theorem sends_nobus {A : AirD} {T : Table} {B : String} {v : List F} (h : ∀ I ∈ A.inters, I.bus ≠ B) :
    tableSends A T B v = 0 :=
  sends_zero_of (Q := fun _ => False) (fun _ _ I hI hb => absurd hb (h I hI)) id

/-- `a + (-(a + (b + c)) + (b + (c + (0 + 0)))) = 0`, by normal forms. -/
theorem bal3_identity (a b c : F) : a + (-(a + (b + c)) + (b + (c + (0 + 0)))) = 0 :=
  E.eval_eq_of_norm
    (e := .add (.atom (.main 0 0)) (.add (.neg (.add (.atom (.main 0 0)) (.add (.atom (.main 0 1)) (.atom (.main 0 2)))))
      (.add (.atom (.main 0 1)) (.add (.atom (.main 0 2)) (.add (.const 0) (.const 0))))))
    (e' := .const 0) (by decide)
    (fun | .main 0 0 => a | .main 0 1 => b | .main 0 2 => c | _ => 0)

theorem neg_zero_eq : -(0 : F) = 0 := by decide

theorem bal_segs (a : F) : a + (0 + (0 + (0 + (-a + 0)))) = 0 := by
  rw [zero_add', zero_add', zero_add', add_zero']
  rw [add_comm']; exact neg_add_cancel' a

theorem segRows_len (roots : List Nat) : roots.length ≤ (segRows roots).length := by
  unfold segRows; simp

/-- **The composed circuit's buses balance** on the honest tables. -/
theorem balancedC {A : List Cell} {hd0 stk0 ctr0 n nilA : Nat} {heap : List Cell} {N W : Nat} {roots : List Nat}
    {C Pg Wt : Table} (hML : A.length < P) (hR : roots.length < P) (hR0 : 0 < roots.length)
    (hcM : ∀ r, r < C.h → ∀ I ∈ cpuIntersC, I.bus = "mem" → I.count.eval (C.env r) ≠ 0 →
      ∃ m, m < A.length ∧ I.fields.map (fun c => c.eval (C.env r)) = tupleOf A m)
    (hcS : ∀ r, r < C.h → ∀ I ∈ cpuIntersC, I.bus = "segs" → I.count.eval (C.env r) ≠ 0 →
      ∃ q, q < roots.length ∧ I.fields.map (fun c => c.eval (C.env r)) = [ofN q, ofN (roots.getD q 0)])
    (hcZ : ∀ r, r < C.h → ∀ I ∈ cpuIntersC, I.bus ≠ "mem" → I.bus ≠ "segs" → I.count.eval (C.env r) = 0)
    (hpM : ∀ r, r < Pg.h → ∀ I ∈ (progAirC heap N W).inters, I.count.eval (Pg.env r) ≠ 0 →
      ∃ m, m < A.length ∧ I.fields.map (fun c => c.eval (Pg.env r)) = tupleOf A m)
    (hwM : ∀ r, r < Wt.h → ∀ I ∈ (witAir N W).inters, I.bus = "mem" → I.count.eval (Wt.env r) ≠ 0 →
      ∃ m, m < A.length ∧ I.fields.map (fun c => c.eval (Wt.env r)) = tupleOf A m)
    (hwZ : ∀ r, r < Wt.h → ∀ I ∈ (witAir N W).inters, I.bus ≠ "mem" → I.count.eval (Wt.env r) = 0) :
    Balanced (compTables hd0 stk0 ctr0 n nilA heap N W roots C
      (memTableC A (cpuAirC hd0 stk0 ctr0 n nilA) (progAirC heap N W) (witAir N W) C Pg Wt) Pg Wt
      (segsTableC roots (cpuAirC hd0 stk0 ctr0 n nilA) C)) := by
  intro B v
  unfold compTables
  simp only [List.foldr_cons, List.foldr_nil]
  let cpu := cpuAirC hd0 stk0 ctr0 n nilA
  let Mm := memTableC A cpu (progAirC heap N W) (witAir N W) C Pg Wt
  let Sg := segsTableC roots cpu C
  by_cases hBm : B = "mem"
  · subst hBm
    have hseg : tableSends (segsAir roots) Sg "mem" v = 0 :=
      sends_nobus (fun I hI => by simp only [segsAir, List.mem_cons, List.not_mem_nil, or_false] at hI; subst hI; decide)
    rw [hseg]
    -- a memory row's sends
    have hrow : ∀ m, m < A.length → rowSends memAirC Mm "mem" v m =
        if tupleOf A m = v then -(tableSends cpu C "mem" (tupleOf A m) + (tableSends (progAirC heap N W) Pg "mem"
          (tupleOf A m) + tableSends (witAir N W) Wt "mem" (tupleOf A m))) else 0 := by
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
          (tableSends (progAirC heap N W) Pg "mem" v + tableSends (witAir N W) Wt "mem" v)) := by
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
      exact bal3_identity _ _ _
    | false =>
      have hno : ¬ ∃ m, m < A.length ∧ v = tupleOf A m := by
        rintro ⟨m, hm, e⟩
        have := List.any_eq_false.1 hany m (List.mem_range.2 hm)
        exact this (decide_eq_true e.symm)
      have h1 : tableSends cpu C "mem" v = 0 := sends_zero_of (Q := fun w => ∃ m, m < A.length ∧ w = tupleOf A m)
        (fun r hr I hI hb hc => by obtain ⟨m, hm, e⟩ := hcM r hr I hI hb hc; exact ⟨m, hm, e⟩) hno
      have h2 : tableSends (progAirC heap N W) Pg "mem" v = 0 :=
        sends_zero_of (Q := fun w => ∃ m, m < A.length ∧ w = tupleOf A m)
          (fun r hr I hI _ hc => by obtain ⟨m, hm, e⟩ := hpM r hr I hI hc; exact ⟨m, hm, e⟩) hno
      have h3 : tableSends (witAir N W) Wt "mem" v = 0 :=
        sends_zero_of (Q := fun w => ∃ m, m < A.length ∧ w = tupleOf A m)
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
    have z_prog : tableSends (progAirC heap N W) Pg B v = 0 :=
      sends_nobus (fun I hI => by
        simp only [progAirC, List.mem_cons, List.not_mem_nil, or_false] at hI; subst hI; exact fun h => hBm h.symm)
    by_cases hBs : B = "segs"
    · subst hBs
      have z_wit : tableSends (witAir N W) Wt "segs" v = 0 :=
        sends_nobus (fun I hI => by
          simp only [witAir, witInters, List.mem_cons, List.not_mem_nil, or_false] at hI
          rcases hI with rfl | rfl <;> decide)
      rw [z_mem, z_prog, z_wit]
      have hSgh : Sg.h = (segRows roots).length := rfl
      -- a segment row's sends
      have hrow : ∀ q, q < Sg.h → rowSends (segsAir roots) Sg "segs" v q =
          if q < roots.length ∧ [ofN q, ofN (roots.getD q 0)] = v then -(tableSends cpu C "segs" v) else 0 := by
        intro q hq
        show (if "segs" = "segs" ∧ [(prec 0).eval (Sg.env q), (prec 1).eval (Sg.env q)] = v then
          -((col 0).eval (Sg.env q)) else 0) + 0 = _
        have e0 : (prec 0).eval (Sg.env q) = ((segRows roots).getD q []).getD 0 0 := by
          show Sg.pre ((q + 0) % Sg.h) 0 = _; rw [Nat.add_zero, Nat.mod_eq_of_lt hq]; rfl
        have e1 : (prec 1).eval (Sg.env q) = ((segRows roots).getD q []).getD 1 0 := by
          show Sg.pre ((q + 0) % Sg.h) 1 = _; rw [Nat.add_zero, Nat.mod_eq_of_lt hq]; rfl
        have em : (col 0).eval (Sg.env q) = if q < roots.length then
            tableSends cpu C "segs" [ofN q, ofN (roots.getD q 0)] else 0 := by
          rw [B.col, E.eval, env_main0 hq]; rfl
        rw [e0, e1, em, add_zero']
        rcases segRows_get hR0 (by rw [← hSgh]; exact hq) with ⟨hq', g⟩ | ⟨hq', g⟩
        · rw [g, if_pos hq']
          by_cases ht : [ofN q, ofN (roots.getD q 0)] = v
          · rw [if_pos ⟨rfl, ht⟩, if_pos ⟨hq', ht⟩, ht]
          · rw [if_neg (fun h => ht h.2), if_neg (fun h => ht h.2)]
        · have hn : ¬ (q < roots.length) := by omega
          simp only [hn, false_and, ↓reduceIte]
          split <;> first | exact neg_zero_eq | rfl
      cases hany : (List.range roots.length).any (fun q => decide ([ofN q, ofN (roots.getD q 0)] = v)) with
      | true =>
        obtain ⟨q0, hq0, e0⟩ := List.any_eq_true.1 hany
        have hq0 := List.mem_range.1 hq0
        have e0 := of_decide_eq_true e0
        have hsg : tableSends (segsAir roots) Sg "segs" v = -(tableSends cpu C "segs" v) := by
          show List.foldr (fun r acc => rowSends (segsAir roots) Sg "segs" v r + acc) 0 (List.range Sg.h) = _
          rw [fold_range_single _ Sg.h q0 (by rw [hSgh]; exact Nat.lt_of_lt_of_le hq0 (segRows_len roots)),
            hrow q0 (by rw [hSgh]; exact Nat.lt_of_lt_of_le hq0 (segRows_len roots)), if_pos ⟨hq0, e0⟩]
          intro q hq hne
          rw [hrow q hq, if_neg]
          rintro ⟨hql, e⟩
          rw [← e0] at e
          have := congrArg List.head? e
          simp only [List.head?_cons, Option.some.injEq] at this
          exact hne (ofN_inj (Nat.lt_trans hql hR) (Nat.lt_trans hq0 hR) this)
        rw [hsg]
        exact bal_segs _
      | false =>
        have hno : ¬ ∃ q, q < roots.length ∧ v = [ofN q, ofN (roots.getD q 0)] := by
          rintro ⟨q, hq, e⟩
          have := List.any_eq_false.1 hany q (List.mem_range.2 hq)
          exact this (decide_eq_true e.symm)
        have h1 : tableSends cpu C "segs" v = 0 :=
          sends_zero_of (Q := fun w => ∃ q, q < roots.length ∧ w = [ofN q, ofN (roots.getD q 0)])
            (fun r hr I hI hb hc => by obtain ⟨q, hq, e⟩ := hcS r hr I hI hb hc; exact ⟨q, hq, e⟩) hno
        have h2 : tableSends (segsAir roots) Sg "segs" v = 0 := by
          show List.foldr (fun r acc => rowSends (segsAir roots) Sg "segs" v r + acc) 0 (List.range Sg.h) = 0
          apply fold_zero
          intro q hq
          rw [hrow q (List.mem_range.1 hq), if_neg (fun h => hno ⟨q, h.1, h.2.symm⟩)]
        rw [h1, h2]; decide
    · -- every other bus: nothing
      have z_cpu : tableSends cpu C B v = 0 := by
        apply sends_zero_of (Q := fun _ => False) _ id
        intro r hr I hI hb hc
        exact hc (hcZ r hr I hI (fun h => hBm (hb ▸ h)) (fun h => hBs (hb ▸ h)))
      have z_wit : tableSends (witAir N W) Wt B v = 0 := by
        apply sends_zero_of (Q := fun _ => False) _ id
        intro r hr I hI hb hc
        exact hc (hwZ r hr I hI (fun h => hBm (hb ▸ h)))
      have z_seg : tableSends (segsAir roots) Sg B v = 0 :=
        sends_nobus (fun I hI => by
          simp only [segsAir, List.mem_cons, List.not_mem_nil, or_false] at hI; subst hI; exact fun h => hBs h.symm)
      rw [z_cpu, z_mem, z_prog, z_wit, z_seg]; decide

theorem memC_sat (A : List Cell) (cpu prog wit : AirD) (C Pg Wt : Table) (hA : 0 < A.length) :
    Sat memAirC (memTableC A cpu prog wit C Pg Wt) := by
  refine ⟨hA, fun c hc m hm' => ?_⟩
  have hm : m < (memTableC A cpu prog wit C Pg Wt).h := hm'
  simp only [memAirC, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl
  · simp only [B.whenFirst, B.col, E.eval, env_first, env_main0 hm]
    split
    · next h0 => subst h0; exact mul_zero' _
    · exact zero_mul' _
  · simp only [B.whenTrans, B.eq, B.nxt, B.col, B.one, B.c, E.eval, env_trans, env_main1, env_main0 hm]
    split
    · exact zero_mul' _
    · next hne =>
      have hne' : ¬ (m + 1 = A.length) := hne
      have hm1 : m + 1 < A.length := by have : m < A.length := hm; omega
      show 1 * ((memTableC A cpu prog wit C Pg Wt).main ((m + 1) % A.length) 0 - (ofN m + ofN 1)) = 0
      rw [Nat.mod_eq_of_lt hm1, one_mul', ofN_one, ofN_succ]
      exact sub_self' _
  · simp only [B.bool, B.col, B.one, B.c, E.eval, env_main0 hm]
    show (0 : F) * (0 - ofN 1) = 0
    exact zero_mul' _

theorem witT_blindZero {a0 : Nat} {A : List Cell} {N W : Nat} : ∀ r, r < (witTableG a0 A N W).h →
    ∀ I ∈ (witAir N W).inters, I.bus ≠ "mem" → I.count.eval ((witTableG a0 A N W).env r) = 0 := by
  intro q hq I hI hb
  simp only [witAir, witInters, List.mem_cons, List.not_mem_nil, or_false] at hI
  rcases hI with rfl | rfl
  · exact absurd rfl hb
  · show (col (WT_BLIND + 4)).eval _ = 0
    rw [witT_env hq]
    rcases Nat.lt_or_ge q (N + W) with h | h
    · exact (witCol_active h).2.2.2.2
    · exact witCol_inactive h _

/-- Increasing ends: the `j`-th is at least `j`. -/
theorem emono_ge {e : Nat → Nat} {n : Nat} (hmono : ∀ j, j + 1 < n → e j < e (j + 1)) :
    ∀ j, j < n → j ≤ e j
  | 0, _ => Nat.zero_le _
  | j + 1, hj => by have := emono_ge hmono j (by omega); have := hmono j hj; omega

/-- **A step keeps the stack pointer in memory.** -/
theorem step_stk {M : List Cell} (hfit : Fits M) {r r' : Row} (hs : stepRow M r = some r')
    (hc : r.ctr ≤ M.length) (hc' : r'.ctr ≤ M.length) : r'.stk ≤ M.length := by
  have hS := shape (M := M) (r := r) (.inl (by rw [hs]; rfl))
  have fl : ∀ j, j < 4 → actOf (kindOf M r) j = 1 → (fieldsAt M r j).2 < M.length := by
    intro j hj ha
    obtain ⟨cell, hrd, _⟩ := hS.reads j hj ha
    obtain ⟨_, hget⟩ := rd_get hrd
    have hfa : fieldsAt M r j = cellFields cell := by unfold fieldsAt; rw [hrd]; rfl
    rw [hfa]
    exact (hfit cell (List.mem_of_getElem? hget)).2
  rcases Nat.lt_or_ge (kindOf M r) 4 with h4 | h4
  · rcases (show kindOf M r = 0 ∨ kindOf M r = 1 ∨ kindOf M r = 2 ∨ kindOf M r = 3 by omega) with e | e | e | e
    · rw [(hS.app e).2] at hs; rw [← Option.some.inj hs]; exact hc
    · rw [hS.i e] at hs; rw [← Option.some.inj hs]
      exact Nat.le_of_lt (fl 1 (by decide) (by rw [e]; rfl))
    · rw [hS.k2 e] at hs; rw [← Option.some.inj hs]
      exact Nat.le_of_lt (fl 2 (by decide) (by rw [e]; rfl))
    · rw [(hS.s e).2.2.2] at hs
      rw [← Option.some.inj hs] at hc' ⊢
      show r.ctr + 2 ≤ M.length
      have : r.ctr + 3 ≤ M.length := hc'
      omega
  · rw [hS.none h4] at hs; cases hs

section

variable {A : List Cell} {m0 : Mach} {roots : List Nat} {nilA n : Nat} {e : Nat → Nat} {row : Nat → Row}
  (hA : AcceptsC A m0 roots nilA n e row) (hfit : Fits A) (hnil : nilA ≤ A.length)
include hA hfit hnil

/-- **Every stack pointer is in memory.** -/
theorem AcceptsC.stk_le : ∀ i, i ≤ e (n - 1) → (row i).stk ≤ A.length := by
  have hc := Circuit.AcceptsC.ctr_le hA
  intro i
  induction i with
  | zero => intro _; rw [hA.stk0]; exact hnil
  | succ i ih =>
    intro hi
    cases hr : isRestart e n i with
    | true =>
      obtain ⟨j, hj, rfl⟩ := isRestart_iff.1 hr
      rw [hA.restart j hj]; exact hnil
    | false =>
      have ne : ∀ j, j + 1 < n → i ≠ e j := fun j hj h' => by
        rw [isRestart_iff.2 ⟨j, hj, h'.symm⟩] at hr; cases hr
      rcases hA.trans i (by omega) ne with h | h
      · exact step_stk hfit h (hc i (by omega)) (hc (i + 1) hi)
      · rw [h.2]; exact ih (by omega)

end

-- ---------------------------------------------------------------------------
-- The honest segment table is public
-- ---------------------------------------------------------------------------

/-! The segment table's multiplicities are a main column, which the prover
writes.  For an accepting run they are fixed by the statement: one restart
into each segment after the first, none into the first (`segs_honest`).  So
the honest segment table is `segsPub roots`, a function of the public
roots, as `composed.rs` writes it, and its LogUp terminal is public. -/

/-- **The public segment table**: the preprocessed `(j, root_j)` rows, and
    multiplicity `1` on each segment after the first. -/
def segsPub (roots : List Nat) : Table :=
  ⟨(segRows roots).length, fun q _ => if 1 ≤ q ∧ q < roots.length then 1 else 0,
   fun q j => ((segRows roots).getD q []).getD j 0⟩

/-- A row sends on a bus through the one interaction on that bus. -/
theorem rowSends_one {T : Table} {bus : String} {v : List F} {r : Nat} (I0 : Inter) :
    ∀ (L1 L2 : List Inter), (∀ I ∈ L1, I.bus ≠ bus) → (∀ I ∈ L2, I.bus ≠ bus) →
    (L1 ++ I0 :: L2).foldr (fun I acc =>
      (if I.bus = bus ∧ I.fields.map (fun e => e.eval (T.env r)) = v then I.count.eval (T.env r) else 0) + acc) 0 =
      if I0.bus = bus ∧ I0.fields.map (fun e => e.eval (T.env r)) = v then I0.count.eval (T.env r) else 0
  | [], L2, _, h2 => by
    rw [List.nil_append, List.foldr_cons]
    have : ∀ L : List Inter, (∀ I ∈ L, I.bus ≠ bus) → L.foldr (fun I acc =>
        (if I.bus = bus ∧ I.fields.map (fun e => e.eval (T.env r)) = v then I.count.eval (T.env r) else 0) + acc)
        0 = 0 := by
      intro L hL
      induction L with
      | nil => rfl
      | cons I L ih =>
        rw [List.foldr_cons, if_neg (fun h => hL I List.mem_cons_self h.1), ih (fun J hJ => hL J (List.mem_cons_of_mem I hJ))]
        exact zero_add' 0
    rw [this L2 h2]
    exact add_zero' _
  | I :: L1, L2, h1, h2 => by
    rw [List.cons_append, List.foldr_cons]
    rw [if_neg (fun h => h1 I List.mem_cons_self h.1),
      rowSends_one I0 L1 L2 (fun J hJ => h1 J (List.mem_cons_of_mem I hJ)) h2]
    exact zero_add' _

/-- A sum over rows of one row's `1`. -/
theorem foldr_single (K x : Nat) (hx : x < K) :
    (List.range K).foldr (fun r acc => (if r = x then (1 : F) else 0) + acc) 0 = 1 := by
  have key : ∀ m, m ≤ K → (List.range m).foldr (fun r acc => (if r = x then (1 : F) else 0) + acc) 0 =
      if x < m then 1 else 0 := by
    intro m
    induction m with
    | zero => intro _; rfl
    | succ m ih =>
      intro hm
      rw [List.range_succ, List.foldr_append]
      show (List.range m).foldr _ ((if m = x then (1 : F) else 0) + 0) = _
      rw [add_zero']
      rcases Nat.lt_trichotomy m x with h | h | h
      · rw [if_neg (by omega), if_neg (by omega)]
        exact (ih (by omega)).trans (if_neg (by omega))
      · subst h
        rw [if_pos rfl, if_pos (by omega)]
        have e0 : ∀ l : List Nat, (∀ r ∈ l, r ≠ m) → l.foldr (fun r acc => (if r = m then (1 : F) else 0) + acc) 1 = 1 := by
          intro l hl
          induction l with
          | nil => rfl
          | cons r l ihl =>
            show (if r = m then (1 : F) else 0) + _ = 1
            rw [if_neg (hl r List.mem_cons_self), ihl (fun r' h' => hl r' (List.mem_cons_of_mem r h'))]
            exact zero_add' 1
        exact e0 _ (fun r hr => by have := List.mem_range.1 hr; omega)
      · rw [if_neg (by omega), if_pos (by omega)]
        exact (ih (by omega)).trans (if_pos h)
  rw [key K (Nat.le_refl K), if_pos hx]

section

variable {A : List Cell} {m0 : Mach} {roots : List Nat} {nilA n : Nat} {e : Nat → Nat} {row : Nat → Row}
  (hA : AcceptsC A m0 roots nilA n e row) {K : Nat} (hK : e (n - 1) < K)
include hA hK

/-- A CPU row's `segs` message: the restart indicator, with the next
    segment's number and root. -/
theorem cpuC_rowSegs (hd0 stk0 ctr0 n' nilA' : Nat) {r : Nat} (hr : r < K) (v : List F) :
    rowSends (cpuAirC hd0 stk0 ctr0 n' nilA') (cpuTableC A row e n roots K) "segs" v r =
      if [ofN (cntS (rsI e n) r + 1), ofN (roots.getD (cntS (rsI e n) r + 1) 0)] = v
      then ofN (rsI e n r) else 0 := by
  have cv := cpuC_col hA hK (roots := roots) hr
  unfold rowSends
  show cpuIntersC.foldr _ 0 = _
  rw [cpuIntersC_eq]
  have he := rowSends_one (T := cpuTableC A row e n roots K) (bus := "segs") (v := v) (r := r)
    ⟨"segs", 1, sRS, [.add (col CNT) one, col ROOT]⟩
    [readInterC 0, readInterC 1, readInterC 2, readInterC 3,
     ⟨"mem", 1, sApp, [col CTR, c 5, fld 1, col STK]⟩,
     ⟨"mem", 1, sS, [col CTR, c 3, fld 4, fld 6]⟩,
     ⟨"mem", 1, sS, [.add (col CTR) one, c 5, col CTR, fld 7]⟩,
     ⟨"mem", 1, sS, [.add (col CTR) (c 2), c 5, fld 6, .add (col CTR) one]⟩]
    [⟨"blind_a", 1, .neg (col (BLA + 4)), blindFields BLA⟩,
     ⟨"blind_b", 1, col (BLB + 4), blindFields BLB⟩]
    (by decide) (by decide)
  refine he.trans ?_
  have hf : List.map (fun x0 => x0.eval ((cpuTableC A row e n roots K).env r)) [.add (col CNT) one, col ROOT] =
      [ofN (cntS (rsI e n) r + 1), ofN (roots.getD (cntS (rsI e n) r + 1) 0)] := by
    simp only [List.map_cons, List.map_nil, E.eval, cv, B.one, B.c, ofN_one, cpuColC_cnt, cpuColC_root]
    rw [← ofN_one, ← ofN_add]
  have hc : sRS.eval ((cpuTableC A row e n roots K).env r) = ofN (rsI e n r) := by
    show (col RS).eval _ = _
    rw [cv, cpuColC_rs]
  rw [hf, hc]
  by_cases hv : [ofN (cntS (rsI e n) r + 1), ofN (roots.getD (cntS (rsI e n) r + 1) 0)] = v
  · rw [if_pos ⟨rfl, hv⟩, if_pos hv]
  · rw [if_neg (fun h => hv h.2), if_neg hv]

/-- **The honest segment multiplicities**: segment `q`'s row receives one
    restart when `q ≥ 1`, and none for the first. -/
theorem cpuC_segsCount (hd0 stk0 ctr0 n' nilA' : Nat) (hn : roots.length = n) (hP : n < P) {q : Nat}
    (hq : q < n) :
    tableSends (cpuAirC hd0 stk0 ctr0 n' nilA') (cpuTableC A row e n roots K) "segs"
      [ofN q, ofN (roots.getD q 0)] = if 1 ≤ q then 1 else 0 := by
  have hmono := hA.emono
  -- which rows send to segment `q`
  have row_eq : ∀ r, r < K → rowSends (cpuAirC hd0 stk0 ctr0 n' nilA') (cpuTableC A row e n roots K) "segs"
      [ofN q, ofN (roots.getD q 0)] r = if 1 ≤ q ∧ r = e (q - 1) then 1 else 0 := by
    intro r hr
    rw [cpuC_rowSegs hA hK hd0 stk0 ctr0 n' nilA' hr]
    cases hrs : isRestart e n r with
    | false =>
      have h0 : rsI e n r = 0 := by unfold rsI; rw [hrs]; rfl
      rw [h0]
      have : ¬ (1 ≤ q ∧ r = e (q - 1)) := by
        rintro ⟨h1, rfl⟩
        have : isRestart e n (e (q - 1)) = true := isRestart_iff.2 ⟨q - 1, by omega, rfl⟩
        rw [this] at hrs; cases hrs
      rw [if_neg this]
      split <;> rfl
    | true =>
      obtain ⟨j, hj, rfl⟩ := isRestart_iff.1 hrs
      have h1 : rsI e n (e j) = 1 := by unfold rsI; rw [hrs]; rfl
      rw [h1, cntS_end hmono j (by omega)]
      by_cases hjq : j + 1 = q
      · subst hjq
        rw [if_pos rfl, if_pos ⟨by omega, by simp⟩]; rfl
      · have hne : [ofN (j + 1), ofN (roots.getD (j + 1) 0)] ≠ [ofN q, ofN (roots.getD q 0)] := by
          intro h
          have h' := congrArg List.head? h
          simp only [List.head?_cons, Option.some.injEq] at h'
          have := congrArg Fin.val h'
          rw [val_ofN (by omega), val_ofN (by omega)] at this
          exact hjq this
        rw [if_neg hne]
        have : ¬ (1 ≤ q ∧ e j = e (q - 1)) := by
          rintro ⟨h1, h2⟩
          rcases Nat.lt_trichotomy j (q - 1) with h | h | h
          · have := emono_lt hmono h (by omega); omega
          · omega
          · have := emono_lt hmono h (by omega); omega
        rw [if_neg this]
  unfold tableSends
  show (List.range K).foldr _ 0 = _
  have hcongr : (List.range K).foldr (fun r acc => rowSends (cpuAirC hd0 stk0 ctr0 n' nilA')
      (cpuTableC A row e n roots K) "segs" [ofN q, ofN (roots.getD q 0)] r + acc) 0 =
      (List.range K).foldr (fun r acc => (if 1 ≤ q ∧ r = e (q - 1) then (1 : F) else 0) + acc) 0 := by
    have : ∀ l : List Nat, (∀ r ∈ l, r < K) → l.foldr (fun r acc => rowSends (cpuAirC hd0 stk0 ctr0 n' nilA')
        (cpuTableC A row e n roots K) "segs" [ofN q, ofN (roots.getD q 0)] r + acc) 0 =
        l.foldr (fun r acc => (if 1 ≤ q ∧ r = e (q - 1) then (1 : F) else 0) + acc) 0 := by
      intro l hl
      induction l with
      | nil => rfl
      | cons r l ih =>
        show _ + _ = _ + _
        rw [row_eq r (hl r List.mem_cons_self), ih (fun r' h' => hl r' (List.mem_cons_of_mem r h'))]
    exact this _ (fun r hr => List.mem_range.1 hr)
  rw [hcongr]
  by_cases h1 : 1 ≤ q
  · have hlt : e (q - 1) < K := Nat.lt_of_le_of_lt (emono_le hmono (a := q - 1) (b := n - 1) (by omega) (by omega)) hK
    rw [if_pos h1]
    refine Eq.trans ?_ (foldr_single K (e (q - 1)) hlt)
    simp only [h1, true_and]
  · rw [if_neg h1]
    have : ∀ l : List Nat, l.foldr (fun r acc => (if 1 ≤ q ∧ r = e (q - 1) then (1 : F) else 0) + acc) 0 = 0 := by
      intro l
      induction l with
      | nil => rfl
      | cons r l ih =>
        show _ + _ = 0
        rw [if_neg (fun h => h1 h.1), ih]
        exact zero_add' 0
    exact this _

/-- **The honest segment table is the public one.** -/
theorem segs_honest (hd0 stk0 ctr0 n' nilA' : Nat) (hn : roots.length = n) (hP : n < P) :
    segsTableC roots (cpuAirC hd0 stk0 ctr0 n' nilA') (cpuTableC A row e n roots K) = segsPub roots := by
  unfold segsTableC segsPub
  congr 1
  funext q _
  by_cases hq : q < roots.length
  · rw [if_pos hq, cpuC_segsCount hA hK hd0 stk0 ctr0 n' nilA' hn hP (by omega)]
    by_cases h1 : 1 ≤ q
    · rw [if_pos h1, if_pos ⟨h1, hq⟩]
    · rw [if_neg h1, if_neg (fun h => h1 h.1)]
  · rw [if_neg hq, if_neg (fun h => hq h.2)]

end


theorem progRowsC_le {heap : List Cell} {N W : Nat} (h : heap.length ≤ 2 ^ 24) :
    (progRowsC heap N W).length ≤ 2 ^ 24 := by
  have hf := List.length_filter_le (fun x : Cell × Nat => !(3 ≤ x.2 && x.2 < 3 + N + W)) heap.zipIdx
  rw [List.length_zipIdx] at hf
  have hp := pow2From_le (n := (heap.zipIdx.filter fun x => !(3 ≤ x.2 && x.2 < 3 + N + W)).length) (by omega) 64 8
    (by decide)
  unfold progRowsC pow2Min
  simp only [List.length_append, List.length_map, List.length_replicate]
  omega

theorem segRows_le {roots : List Nat} (h : roots.length ≤ 2 ^ 24) : (segRows roots).length ≤ 2 ^ 24 := by
  have hp := pow2From_le (n := (roots.zipIdx.map fun x => [ofN x.2, ofN x.1]).length) (by simp; omega) 64 8
    (by decide)
  unfold segRows pow2Min
  simp only [List.length_append, List.length_replicate]
  simp only [List.length_map, List.length_zipIdx] at hp ⊢
  omega

theorem witRowsG_len {a0 N W : Nat} (h : N + W ≤ 2 ^ 8) : (witRowsG a0 N W).length = 2 ^ 8 := by
  unfold witRowsG
  simp only [List.length_append, List.length_map, List.length_range, List.length_replicate]
  omega

theorem witRows_len {N W : Nat} (h : N + W ≤ 2 ^ 8) : (witRows N W).length = 2 ^ 8 := witRowsG_len h

/-- **Completeness of the composed circuit**, for any evaluation statement
    (bits of a shape, terms), at the heights a statement names: a run the
    Lean AIR with segments accepts, from the composed machine of literal
    bits and a well-formed region, over a memory of
    `2^Lm` cells whose cells point into it, ending within `2^R` rows, with
    at most `2^8` private cells, `R` and `Lm` at most `20`, gives tables
    that AIRs with the composed circuit's normal forms accept, with
    Plonky3's selectors; they decode back to the memory and the run. -/
theorem comp_completeG_log {R Lm : Nat} (hR : R ≤ 20) (hLm : Lm ≤ 20) {shp : BT} {Ps : List Term} {W : Nat} {Rs : List AirD} (hs : sameAirsB Rs (compAirsG shp Ps W) = true)
    {ρ : Nat → Bool} {region : List Cell} (hrl : region.length = W)
    (hr : ∀ i c, region[i]? = some c → cellOK (BT.nleaves shp + 3 + i) c = true)
    {A : List Cell} {e : Nat → Nat} {row : Nat → Row}
    (hA : AcceptsC A (cMachine ρ shp region Ps) (cHeap ρ shp region Ps).2
      (cHeap ρ shp region Ps).1.length Ps.length e row)
    (hfit : Fits A) (hlen : A.length = 2 ^ Lm) (hK : e (Ps.length - 1) < 2 ^ R)
    (hNW : BT.nleaves shp + W ≤ 2 ^ 8) :
    ∃ C Mm Pg Wt Sg, AcceptedP Rs [C, Mm, Pg, Wt, Sg] ∧ C.h = 2 ^ R ∧ Mm.h = 2 ^ Lm ∧ Wt.h = 2 ^ 8 ∧
      Pg = progTableC (blankM shp W Ps).heap (BT.nleaves shp) W ∧ Sg = segsPub (blankRoots shp W Ps) ∧
      memOf Mm = A ∧ ∀ i, i ≤ e (Ps.length - 1) → rowOf C i = row i := by
  have hRb : 2 ^ R ≤ 1048576 := Nat.pow_le_pow_right (by decide) hR
  have hLb : 2 ^ Lm ≤ 1048576 := Nat.pow_le_pow_right (by decide) hLm
  have hl : region.length = (List.replicate W Cell.S).length := by rw [List.length_replicate, hrl]
  obtain ⟨_, hstk, hroots, hlenm, htake, hpub⟩ :=
    cMachine_public ρ (fun _ => false) shp region (List.replicate W .S) Ps hl
  have eR : (cHeap ρ shp region Ps).2 = blankRoots shp W Ps := hroots
  have eN : (cHeap ρ shp region Ps).1.length = (blankM shp W Ps).stk := hstk
  rw [eR, eN] at hA
  obtain ⟨m0, hm0⟩ : ∃ m, cMachine ρ shp region Ps = m := ⟨_, rfl⟩
  rw [hm0] at hA htake hpub hlenm
  have hn : 0 < Ps.length := hA.npos
  have hnR : (blankRoots shp W Ps).length = Ps.length := blankRoots_length _ _ _
  have hctr := Circuit.AcceptsC.ctr_le hA
  -- the memory holds the machine
  have h0 : A.take m0.heap.length = m0.heap := by rw [← hA.ctr0]; exact hA.heap0
  have hmlen : m0.heap.length ≤ A.length := by
    have := congrArg List.length h0; rw [List.length_take] at this; omega
  have hpre : BT.nleaves shp + 3 + W ≤ m0.heap.length := by
    have := congrArg List.length htake
    simp only [List.length_take, List.length_append, slotHeap_length, hrl] at this
    omega
  have hAm : ∀ i, i < m0.heap.length → A.getD i .nil = m0.heap.getD i .nil := by
    intro i hi
    have := congrArg (fun l => l[i]?) h0
    simp only [List.getElem?_take, if_pos hi] at this
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, this]
  have hslot : ∀ k, k < BT.nleaves shp + 3 + W →
      A.getD k .nil = (slotHeap ρ (BT.nleaves shp) ++ region).getD k .nil := by
    intro k hk
    rw [hAm k (by omega)]
    have := congrArg (fun l => l[k]?) htake
    simp only [List.getElem?_take, if_pos (show k < BT.nleaves shp + 3 + region.length by omega)] at this
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, this]
  have hbits : ∀ i, i < BT.nleaves shp → A.getD (3 + i) .nil = .K ∨ A.getD (3 + i) .nil = .app 0 1 := by
    intro i hi
    rw [hslot (3 + i) (by omega), List.getD_eq_getElem?_getD,
      List.getElem?_append_left (by rw [slotHeap_length]; omega)]
    unfold slotHeap
    rw [List.getElem?_append_right (by simp),
      show 3 + i - ([Cell.K, Cell.I, Cell.app 0 1] : List Cell).length = i by simp, List.getElem?_map,
      List.getElem?_range hi, Option.map_some, Option.getD_some]
    cases ρ i
    · exact .inr rfl
    · exact .inl rfl
  have hreg : ∀ i, i < W → cellOK (3 + BT.nleaves shp + i) (A.getD (3 + BT.nleaves shp + i) .nil) = true := by
    intro i hi
    rw [hslot _ (by omega), List.getD_eq_getElem?_getD,
      List.getElem?_append_right (by rw [slotHeap_length]; omega), slotHeap_length,
      show 3 + BT.nleaves shp + i - (BT.nleaves shp + 3) = i by omega]
    have hri : i < region.length := by omega
    rw [List.getElem?_eq_getElem hri, Option.getD_some]
    have := hr i region[i] (List.getElem?_eq_getElem hri)
    rwa [show BT.nleaves shp + 3 + i = 3 + BT.nleaves shp + i by omega] at this
  -- the numbers
  have hPP : P = 2013265921 := rfl
  have hAl : A.length < P := by rw [hlen, hPP]; omega
  have hnK : Ps.length ≤ 2 ^ R := by
    have := emono_ge hA.emono (Ps.length - 1) (by omega); omega
  have hRlt : (blankRoots shp W Ps).length < P := by rw [hnR]; omega
  have hsmall : 3 + BT.nleaves shp + W ≤ 2 ^ 24 := by omega
  have hlenW : 3 + BT.nleaves shp + W ≤ A.length := by omega
  have hbl : (blankM shp W Ps).heap.length = m0.heap.length := hlenm.symm
  -- the tables
  let C := cpuTableC A row e Ps.length (blankRoots shp W Ps) (2 ^ R)
  let cpu := cpuAirC (blankM shp W Ps).hd (blankM shp W Ps).stk
    (blankM shp W Ps).heap.length (blankRoots shp W Ps).length
    (blankM shp W Ps).stk
  let Pg := progTableC (blankM shp W Ps).heap (BT.nleaves shp) W
  let Wt := witTable A (BT.nleaves shp) W
  let Mm := memTableC A cpu (progAirC (blankM shp W Ps).heap (BT.nleaves shp) W)
    (witAir (BT.nleaves shp) W) C Pg Wt
  let Sg := segsTableC (blankRoots shp W Ps) cpu C
  have hb : ∀ i, i < 2 ^ R → (rowP row e Ps.length i).ctr ≤ 2 ^ 24 := by
    intro i _
    unfold rowP
    split
    · exact Nat.le_trans (hctr i (by assumption)) (by omega)
    · exact Nat.le_trans (hctr _ (Nat.le_refl _)) (by omega)
  have hcpu : Sat cpu C := by
    have := cpuC_sat hA hK hb
    have eAir : cpuAirC ((blankRoots shp W Ps).getD 0 0) (blankM shp W Ps).stk
        m0.heap.length Ps.length (blankM shp W Ps).stk = cpu := by
      show _ = cpuAirC _ _ _ _ _
      rw [hbl, hnR]; rfl
    rw [eAir] at this
    exact this
  have hpubA : ∀ i, i < (blankM shp W Ps).heap.length →
      ¬ (3 ≤ i ∧ i < 3 + BT.nleaves shp + W) →
      i < A.length ∧ A.getD i .nil = (blankM shp W Ps).heap.getD i .nil := by
    intro i hi hp
    have hi' : i < m0.heap.length := by omega
    refine ⟨by omega, ?_⟩
    have hor : i < 3 ∨ BT.nleaves shp + 3 + region.length ≤ i := by
      rcases Nat.lt_or_ge i 3 with h3 | h3
      · exact .inl h3
      · refine .inr ?_
        have := Nat.le_of_not_lt (fun hlt => hp ⟨h3, hlt⟩)
        omega
    rw [hAm i hi', List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, hpub i hor]
    rfl
  have hacc : Accepted (compAirsG shp Ps W) [C, Mm, Pg, Wt, Sg] := by
    have z : (compAirsG shp Ps W).zip [C, Mm, Pg, Wt, Sg] =
        compTables (blankM shp W Ps).hd (blankM shp W Ps).stk
          (blankM shp W Ps).heap.length (blankRoots shp W Ps).length
          (blankM shp W Ps).stk (blankM shp W Ps).heap (BT.nleaves shp) W
          (blankRoots shp W Ps) C Mm Pg Wt Sg := rfl
    refine ⟨rfl, ?_, ?_, ?_, ?_⟩
    · rw [z]
      intro p hp
      simp only [compTables, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl
      · exact ⟨hcpu, .inl rfl⟩
      · exact ⟨memC_sat A _ _ _ _ _ _ (by omega), .inl rfl⟩
      · exact ⟨(progC_sat _ _ _).1, .inr (progC_sat _ _ _).2⟩
      · exact ⟨wit_sat (a0 := 3) (fun _ => by decide) hbits hreg hsmall, .inr ⟨rfl, fun _ _ _ _ => rfl⟩⟩
      · exact ⟨⟨segRows_pos _, fun c hc => nomatch hc⟩, .inr ⟨rfl, fun _ _ _ _ => rfl⟩⟩
    · rw [z]
      exact balancedC hAl hRlt (by omega) (cpuC_honest hA hK) (cpuC_segsHonest hA hK hnR) (cpuC_blindZero hA hK)
        (progC_honest hpubA) (witT_honest (a0 := 3) (fun _ => by decide) hbits hreg hlenW) witT_blindZero
    · rw [z]
      unfold HeightsOK compTables
      simp only [List.foldr_cons, List.foldr_nil]
      have hPg : Pg.h ≤ 2 ^ 24 := progRowsC_le (by omega)
      have hSg : Sg.h ≤ 2 ^ 24 := segRows_le (by omega)
      have hWt : Wt.h = 2 ^ 8 := witRows_len hNW
      have hC : C.h = 2 ^ R := rfl
      have hMm : Mm.h = 2 ^ Lm := hlen
      show 11 * C.h + (1 * Mm.h + (1 * Pg.h + (2 * Wt.h + (0 * Sg.h + 0)))) < P
      omega
    · rw [z]
      intro p hp
      simp only [compTables, List.mem_cons, List.not_mem_nil, or_false] at hp
      have hPg : Pg.h ≤ 2 ^ 24 := progRowsC_le (by omega)
      have hSg : Sg.h ≤ 2 ^ 24 := segRows_le (by omega)
      have hWt : Wt.h = 2 ^ 8 := witRows_len hNW
      rcases hp with rfl | rfl | rfl | rfl | rfl
      · show 2 ^ R ≤ 2 ^ 27; exact Nat.pow_le_pow_right (by decide) (by omega)
      · show A.length ≤ 2 ^ 27; omega
      · show Pg.h ≤ 2 ^ 27; omega
      · show Wt.h ≤ 2 ^ 27; omega
      · show Sg.h ≤ 2 ^ 27; omega
  have hRs : AcceptedP Rs [C, Mm, Pg, Wt, Sg] :=
    (acceptedP_iff_of (compG_guarded shp Ps W) hs _).2 (accepted_transfer (sameAirsB_symm hs) hacc)
  refine ⟨C, Mm, Pg, Wt, Sg, hRs, rfl, hlen, witRows_len hNW, rfl,
    segs_honest hA hK _ _ _ _ _ hnR (by rw [← hnR]; exact hRlt), ?_, ?_⟩
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
    have hiK : i < 2 ^ R := by omega
    have e1 : rowP row e Ps.length i = row i := by unfold rowP; rw [if_pos hi]
    have hc := hctr i hi
    have hnil : (blankM shp W Ps).stk ≤ A.length := by
      show (cHeap _ _ _ _).1.length ≤ _
      have : (cHeap (fun _ => false) shp (List.replicate W .S) Ps).1.length + 1 =
          (blankM shp W Ps).heap.length := by
        show _ = ((cHeap _ _ _ _).1 ++ [Cell.nil]).length; simp
      omega
    have hs := Circuit.AcceptsC.stk_le hA hfit hnil i hi
    have hS := shape (valid_rowP hA hK hiK)
    obtain ⟨cell, hrd, _⟩ := hS.reads 0 (by decide) rfl
    have hh := (rd_get hrd).1
    rw [e1] at hh
    show (⟨(cpuColC A row e Ps.length (blankRoots shp W Ps) i HD).val,
      (cpuColC A row e Ps.length (blankRoots shp W Ps) i STK).val,
      (cpuColC A row e Ps.length (blankRoots shp W Ps) i CTR).val⟩ : Row) = row i
    rw [cpuColC_reg _ (.inl rfl), cpuColC_reg _ (.inr (.inl rfl)), cpuColC_reg _ (.inr (.inr rfl)), e1]
    show (⟨(ofN (row i).hd).val, (ofN (row i).stk).val, (ofN (row i).ctr).val⟩ : Row) = row i
    rw [val_ofN (by show (row i).hd < P; have : (row i).hd < (row i).ctr := hh; omega),
      val_ofN (by omega), val_ofN (by omega)]

theorem comp_complete_log {R Lm : Nat} (hR : R ≤ 20) (hLm : Lm ≤ 20) {M : MF} {W : Nat} {Rs : List AirD}
    (hs : sameAirsB Rs (compAirs M W) = true)
    {ρ : Nat → Bool} {region : List Cell} (hrl : region.length = W)
    (hr : ∀ i c, region[i]? = some c → cellOK (BT.nleaves (clear M) + 3 + i) c = true)
    {A : List Cell} {e : Nat → Nat} {row : Nat → Row}
    (hA : AcceptsC A (cMachine ρ (clear M) region (stmtOf M)) (cHeap ρ (clear M) region (stmtOf M)).2
      (cHeap ρ (clear M) region (stmtOf M)).1.length (stmtOf M).length e row)
    (hfit : Fits A) (hlen : A.length = 2 ^ Lm) (hK : e ((stmtOf M).length - 1) < 2 ^ R)
    (hNW : BT.nleaves (clear M) + W ≤ 2 ^ 8) :
    ∃ C Mm Pg Wt Sg, AcceptedP Rs [C, Mm, Pg, Wt, Sg] ∧ C.h = 2 ^ R ∧ Mm.h = 2 ^ Lm ∧ Wt.h = 2 ^ 8 ∧
      Pg = progTableC (blankM (clear M) W (stmtOf M)).heap (BT.nleaves (clear M)) W ∧
      Sg = segsPub (blankRoots (clear M) W (stmtOf M)) ∧
      memOf Mm = A ∧ ∀ i, i ≤ e ((stmtOf M).length - 1) → rowOf C i = row i :=
  comp_completeG_log hR hLm hs hrl hr hA hfit hlen hK hNW

/-- **Completeness of the composed circuit** at its default heights, `2^11`
    rows and memory cells and `2^8` private cells. -/
theorem comp_complete {M : MF} {W : Nat} {Rs : List AirD} (hs : sameAirsB Rs (compAirs M W) = true)
    {ρ : Nat → Bool} {region : List Cell} (hrl : region.length = W)
    (hr : ∀ i c, region[i]? = some c → cellOK (BT.nleaves (clear M) + 3 + i) c = true)
    {A : List Cell} {e : Nat → Nat} {row : Nat → Row}
    (hA : AcceptsC A (cMachine ρ (clear M) region (stmtOf M)) (cHeap ρ (clear M) region (stmtOf M)).2
      (cHeap ρ (clear M) region (stmtOf M)).1.length (stmtOf M).length e row)
    (hfit : Fits A) (hlen : A.length = 2 ^ 11) (hK : e ((stmtOf M).length - 1) < 2 ^ 11)
    (hNW : BT.nleaves (clear M) + W ≤ 2 ^ 8) :
    ∃ C Mm Pg Wt Sg, AcceptedP Rs [C, Mm, Pg, Wt, Sg] ∧ C.h = 2 ^ 11 ∧ Mm.h = 2 ^ 11 ∧ Wt.h = 2 ^ 8 ∧
      Pg = progTableC (blankM (clear M) W (stmtOf M)).heap (BT.nleaves (clear M)) W ∧
      Sg = segsPub (blankRoots (clear M) W (stmtOf M)) ∧
      memOf Mm = A ∧ ∀ i, i ≤ e ((stmtOf M).length - 1) → rowOf C i = row i :=
  comp_complete_log (by decide) (by decide) hs hrl hr hA hfit hlen hK hNW

end Circuit
