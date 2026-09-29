import Ski.Circuit.BaseTable

/-!
# Completeness of the corpus circuit

**`base_complete`**: a run the Lean AIR accepts, whose memory fits the
range checks (`2^24` cells) and whose rows fit a domain (`2^27`), gives
tables the corpus circuit accepts, under the same reading of an accepted
proof as soundness (`Accepted`), and they decode back to the run.

The tables are the honest ones: the CPU table of `BaseTable.lean`, a
memory table with one row per cell whose multiplicity is the number of
times the other tables look it up, and the verifier's program table.
-/

namespace Circuit

open B Air Mach

-- ---------------------------------------------------------------------------
-- The program table's height
-- ---------------------------------------------------------------------------

theorem pow2From_le {n : Nat} (hn : n ≤ 2 ^ 24) : ∀ f e, e ≤ 24 → pow2From f (2 ^ e) n ≤ 2 ^ 24
  | 0, e, he => Nat.pow_le_pow_right (by decide) he
  | f + 1, e, he => by
    unfold pow2From
    split
    · next hlt =>
      have he' : e < 24 := by
        rcases Nat.lt_or_ge e 24 with h | h
        · exact h
        · have := Nat.pow_le_pow_right (show 0 < 2 by decide) h; omega
      rw [show 2 * 2 ^ e = 2 ^ (e + 1) by rw [Nat.pow_succ, Nat.mul_comm]]
      exact pow2From_le hn f (e + 1) he'
    · exact Nat.pow_le_pow_right (by decide) he

theorem programRows_length_le {heap : List Cell} (h : heap.length ≤ 2 ^ 24) :
    (programRows heap).length ≤ 2 ^ 24 := by
  have hp : pow2AtLeast heap.length ≤ 2 ^ 24 := pow2From_le h 64 4 (by decide)
  simp only [programRows, List.length_append, List.length_map, List.length_zipIdx, List.length_replicate]
  omega

-- ---------------------------------------------------------------------------
-- The memory and program tables
-- ---------------------------------------------------------------------------

/-- A memory cell's tuple on the bus. -/
def tupleOf (M : List Cell) (m : Nat) : List F :=
  [ofN m, ofN (cellTag (M.getD m .nil)), ofN (cellFields (M.getD m .nil)).1, ofN (cellFields (M.getD m .nil)).2]

/-- The verifier's program table. -/
def progTable (heap : List Cell) : Table :=
  ⟨(programRows heap).length, fun _ _ => 0, fun i j => ((programRows heap).getD i []).getD j 0⟩

/-- **The honest memory table**: one row per cell, its multiplicity the
    number of lookups of its tuple. -/
def memTable (M : List Cell) (C Pg : Table) (hd0 stk0 ctr0 : Nat) (heap : List Cell) : Table :=
  ⟨M.length, fun m col =>
    if col = 0 then ofN m
    else if col = 1 then ofN (cellTag (M.getD m .nil))
    else if col = 2 then ofN (cellFields (M.getD m .nil)).1
    else if col = 3 then ofN (cellFields (M.getD m .nil)).2
    else tableSends (cpuAir hd0 stk0 ctr0) C "mem" (tupleOf M m) + tableSends (progAir heap) Pg "mem" (tupleOf M m),
    fun _ _ => 0⟩

theorem mem_sat (M : List Cell) (C Pg : Table) (hd0 stk0 ctr0 : Nat) (heap : List Cell) (hM : 0 < M.length) :
    Sat memAir (memTable M C Pg hd0 stk0 ctr0 heap) := by
  refine ⟨hM, fun e he m hm' => ?_⟩
  have hm : m < (memTable M C Pg hd0 stk0 ctr0 heap).h := hm'
  simp only [memAir, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · simp only [B.whenFirst, B.col, E.eval, env_first, env_main0 hm]
    split
    · next h0 => subst h0; exact mul_zero' _
    · exact zero_mul' _
  · simp only [B.whenTrans, B.eq, B.nxt, B.col, B.one, B.c, E.eval, env_trans, env_main1, env_main0 hm]
    split
    · exact zero_mul' _
    · next hne =>
      have hne' : ¬ (m + 1 = M.length) := hne
      have hm1 : m + 1 < M.length := by have : m < M.length := hm; omega
      show 1 * ((memTable M C Pg hd0 stk0 ctr0 heap).main ((m + 1) % M.length) 0 - (ofN m + ofN 1)) = 0
      rw [Nat.mod_eq_of_lt hm1, one_mul', ofN_one, ofN_succ]
      exact sub_self' _

theorem prog_sat (heap : List Cell) (hh : 0 < heap.length) :
    Sat (progAir heap) (progTable heap) ∧ PreIs (progAir heap) (progTable heap) := by
  refine ⟨⟨Nat.lt_of_lt_of_le hh (programRows_length heap), fun e he i (hi : i < (programRows heap).length) => ?_⟩,
    ⟨rfl, fun _ _ _ _ => rfl⟩⟩
  simp only [progAir, List.mem_cons, List.not_mem_nil, or_false] at he
  subst he
  show (progTable heap).main ((i + 0) % _) 0 = 0
  rfl

-- ---------------------------------------------------------------------------
-- The bus balances
-- ---------------------------------------------------------------------------

theorem fold_init {α : Type} (f : α → F) (x : F) : ∀ l : List α,
    l.foldr (fun b acc => f b + acc) x = l.foldr (fun b acc => f b + acc) 0 + x
  | [] => (zero_add' x).symm
  | b :: l => by simp only [List.foldr_cons]; rw [fold_init f x l, add_assoc']

/-- A sum over the rows with one nonzero term. -/
theorem fold_range_single (f : Nat → F) : ∀ L m0, m0 < L → (∀ m, m < L → m ≠ m0 → f m = 0) →
    (List.range L).foldr (fun b acc => f b + acc) 0 = f m0
  | 0, _, h, _ => absurd h (Nat.not_lt_zero _)
  | L + 1, m0, hm0, hz => by
    rw [List.range_succ, List.foldr_append, List.foldr_cons, List.foldr_nil, fold_init]
    rcases Nat.lt_or_ge m0 L with h | h
    · rw [fold_range_single f L m0 h (fun m hm hne => hz m (Nat.lt_succ_of_lt hm) hne),
        hz L (Nat.lt_succ_self L) (Nat.ne_of_gt h), add_zero', add_zero']
    · have e : m0 = L := Nat.le_antisymm (Nat.le_of_lt_succ hm0) h
      subst e
      rw [fold_zero f _ (fun m hm => hz m (Nat.lt_succ_of_lt (List.mem_range.1 hm))
        (Nat.ne_of_lt (List.mem_range.1 hm))), zero_add', add_zero']

/-- `a + (-(a + b) + (b + 0)) = 0`, by normal forms. -/
theorem bal_identity (a b : F) : a + (-(a + b) + (b + 0)) = 0 :=
  E.eval_eq_of_norm
    (e := .add (.atom (.main 0 0)) (.add (.neg (.add (.atom (.main 0 0)) (.atom (.main 0 1))))
      (.add (.atom (.main 0 1)) (.const 0))))
    (e' := .const 0) (by decide)
    (fun | .main 0 0 => a | .main 0 1 => b | _ => 0)

theorem cpuInters_bus : ∀ I ∈ cpuInters, I.bus = "mem" := by
  intro I hI
  simp only [cpuInters, writeInters, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
    or_false] at hI
  rcases hI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- A table whose nonzero sends are all memory tuples sends nothing on a
    tuple that is not one. -/
theorem sends_zero {M : List Cell} {A : AirD} {T : Table} {bus : String} {v : List F}
    (hbus : ∀ I ∈ A.inters, I.bus = "mem")
    (hh : ∀ r, r < T.h → ∀ I ∈ A.inters, I.count.eval (T.env r) ≠ 0 →
      ∃ m, m < M.length ∧ I.fields.map (fun e => e.eval (T.env r)) = tupleOf M m)
    (hno : ¬ (bus = "mem" ∧ ∃ m, m < M.length ∧ tupleOf M m = v)) :
    tableSends A T bus v = 0 := by
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
    · exfalso
      obtain ⟨m, hm, e⟩ := hh r (List.mem_range.1 hr) I hI h0
      exact hno ⟨hc.1 ▸ hbus I hI, m, hm, e ▸ hc.2⟩
  · rfl

/-- **The bus balances**, when every nonzero send of the CPU and the
    program table is a memory tuple. -/
theorem balanced {M : List Cell} {hd0 stk0 ctr0 : Nat} {heap : List Cell} {C Pg : Table}
    (hML : M.length < P)
    (hcpu : ∀ r, r < C.h → ∀ I ∈ cpuInters, I.count.eval (C.env r) ≠ 0 →
      ∃ m, m < M.length ∧ I.fields.map (fun e => e.eval (C.env r)) = tupleOf M m)
    (hprog : ∀ r, r < Pg.h → ∀ I ∈ (progAir heap).inters, I.count.eval (Pg.env r) ≠ 0 →
      ∃ m, m < M.length ∧ I.fields.map (fun e => e.eval (Pg.env r)) = tupleOf M m) :
    Balanced (baseTables hd0 stk0 ctr0 heap C (memTable M C Pg hd0 stk0 ctr0 heap) Pg) := by
  intro bus v
  unfold baseTables
  simp only [List.foldr_cons, List.foldr_nil]
  -- a memory row's sends
  have hrow : ∀ m, m < M.length → rowSends memAir (memTable M C Pg hd0 stk0 ctr0 heap) bus v m =
      if "mem" = bus ∧ tupleOf M m = v then
        -(tableSends (cpuAir hd0 stk0 ctr0) C "mem" (tupleOf M m) + tableSends (progAir heap) Pg "mem" (tupleOf M m))
      else 0 := by
    intro m hm
    have hm' : m < (memTable M C Pg hd0 stk0 ctr0 heap).h := hm
    simp only [rowSends, memAir, List.foldr_cons, List.foldr_nil, List.map_cons, List.map_nil, B.col, E.eval,
      env_main0 hm', add_zero']
    rfl
  cases hany : (List.range M.length).any (fun m => decide (tupleOf M m = v)) && decide (bus = "mem") with
  | true =>
    simp only [Bool.and_eq_true, List.any_eq_true, List.mem_range, decide_eq_true_eq] at hany
    obtain ⟨⟨m0, hm0, e0⟩, rfl⟩ := hany
    have hmem : tableSends memAir (memTable M C Pg hd0 stk0 ctr0 heap) "mem" v =
        -(tableSends (cpuAir hd0 stk0 ctr0) C "mem" v + tableSends (progAir heap) Pg "mem" v) := by
      show List.foldr (fun r acc => rowSends memAir (memTable M C Pg hd0 stk0 ctr0 heap) "mem" v r + acc) 0
        (List.range M.length) = _
      rw [fold_range_single _ M.length m0 hm0, hrow m0 hm0,
        if_pos ⟨rfl, e0⟩, e0]
      intro b hb hne
      rw [hrow b hb, if_neg]
      intro ⟨_, e⟩
      rw [← e0] at e
      have := congrArg List.head? e
      simp only [tupleOf, List.head?_cons, Option.some.injEq] at this
      exact hne (ofN_inj (Nat.lt_trans hb hML) (Nat.lt_trans hm0 hML) this)
    show tableSends (cpuAir hd0 stk0 ctr0) C "mem" v +
      (tableSends memAir (memTable M C Pg hd0 stk0 ctr0 heap) "mem" v + (tableSends (progAir heap) Pg "mem" v + 0)) = 0
    rw [hmem]
    exact bal_identity _ _
  | false =>
    have hno : ¬ (bus = "mem" ∧ ∃ m, m < M.length ∧ tupleOf M m = v) := by
      rintro ⟨hb, m, hm, e⟩
      have : ((List.range M.length).any (fun m => decide (tupleOf M m = v)) && decide (bus = "mem")) = true := by
        simp only [Bool.and_eq_true, List.any_eq_true, List.mem_range, decide_eq_true_eq]
        exact ⟨⟨m, hm, e⟩, hb⟩
      rw [hany] at this; cases this
    have h1 : tableSends (cpuAir hd0 stk0 ctr0) C bus v = 0 := sends_zero cpuInters_bus hcpu hno
    have h3 : tableSends (progAir heap) Pg bus v = 0 :=
      sends_zero (fun I hI => by simp only [progAir, List.mem_cons, List.not_mem_nil, or_false] at hI; rw [hI])
        hprog hno
    have h2 : tableSends memAir (memTable M C Pg hd0 stk0 ctr0 heap) bus v = 0 := by
      show List.foldr (fun r acc => rowSends memAir (memTable M C Pg hd0 stk0 ctr0 heap) bus v r + acc) 0
        (List.range M.length) = 0
      apply fold_zero
      intro m hm
      rw [hrow m (List.mem_range.1 hm), if_neg]
      intro ⟨hb, e⟩
      exact hno ⟨hb.symm, m, List.mem_range.1 hm, e⟩
    rw [h1, h2, h3, add_zero', add_zero', add_zero']

-- ---------------------------------------------------------------------------
-- Every nonzero send is a memory tuple
-- ---------------------------------------------------------------------------

theorem tuple_get {M : List Cell} {m : Nat} {cell : Cell} (h : M[m]? = some cell) :
    m < M.length ∧ tupleOf M m = [ofN m, ofN (cellTag cell), ofN (cellFields cell).1, ofN (cellFields cell).2] := by
  have hm : m < M.length := by
    rcases Nat.lt_or_ge m M.length with hm | hm
    · exact hm
    · rw [List.getElem?_eq_none hm] at h; cases h
  have hg : M.getD m .nil = cell := by rw [List.getD_eq_getElem?_getD, h]; rfl
  exact ⟨hm, by rw [tupleOf, hg]⟩

theorem rd_get {M : List Cell} {c a : Nat} {cell : Cell} (h : rd M c a = some cell) : a < c ∧ M[a]? = some cell := by
  unfold rd at h
  split at h
  · exact ⟨by assumption, h⟩
  · cases h

theorem cpu_fld {M : List Cell} {row : Nat → Row} {k : Nat} {i : Nat} (hi : i < k) {j : Nat} (hj : j < 4) :
    (fld (2 * j)).eval ((cpuTable M row k).env i) = ofN (fieldsAt M (row i) j).1 ∧
    (fld (2 * j + 1)).eval ((cpuTable M row k).env i) = ofN (fieldsAt M (row i) j).2 := by
  have cv := cpu_env (M := M) (row := row) hi
  constructor
  · rw [fld, cv, cpuCol_fld M _ (by omega), if_pos (by omega),
      show 2 * j / 2 = j by omega]
  · rw [fld, cv, cpuCol_fld M _ (by omega), if_neg (by omega),
      show (2 * j + 1) / 2 = j by omega]

/-- **One CPU row's lookups are honest**: a send with nonzero count carries
    a memory cell's tuple. -/
theorem cpu_honestAt {M : List Cell} {row : Nat → Row} {k i : Nat} (hi : i < k) (hvi : Valid M (row i)) :
    ∀ I ∈ cpuInters, I.count.eval ((cpuTable M row k).env i) ≠ 0 →
    ∃ m, m < M.length ∧ I.fields.map (fun e => e.eval ((cpuTable M row k).env i)) = tupleOf M m := by
  intro I hI hc
  have hS := shape hvi
  have hK := cpu_kind hi hS
  obtain ⟨hf, _, hApp, hSS, _⟩ := kind_facts hi hK
  have cv := cpu_env (M := M) (row := row) hi
  -- a read
  have read : ∀ j, j < 4 → I = readInter j → ∃ m, m < M.length ∧
      I.fields.map (fun e => e.eval ((cpuTable M row k).env i)) = tupleOf M m := by
    intro j hj e
    subst e
    have ha : actOf (kindOf M (row i)) j = 1 := by
      have h1 := actOf_le (kindOf M (row i)) j
      have hc' : ofN (actOf (kindOf M (row i)) j) ≠ 0 := by rw [← (hf j hj).1]; exact hc
      rcases Nat.lt_or_ge (actOf (kindOf M (row i)) j) 1 with h0 | h0
      · exact absurd (by rw [show actOf (kindOf M (row i)) j = 0 by omega]; rfl) hc'
      · omega
    obtain ⟨cell, hrd, htag⟩ := hS.reads j hj ha
    obtain ⟨_, hget⟩ := rd_get hrd
    obtain ⟨hm, ht⟩ := tuple_get hget
    refine ⟨_, hm, ?_⟩
    have hfa : fieldsAt M (row i) j = cellFields cell := by
      unfold fieldsAt; rw [hrd]; rfl
    obtain ⟨f1, f2⟩ := cpu_fld (M := M) (row := row) hi hj
    simp only [readInter, List.map_cons, List.map_nil, cpu_addr hi hj, (hf j hj).2, f1, f2, ht, hfa, htag]
  simp only [cpuInters, writeInters, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
    or_false] at hI
  have hkind : ∀ n, ofN (if kindOf M (row i) = n then 1 else 0) ≠ 0 → kindOf M (row i) = n := by
    intro n h
    by_cases e : kindOf M (row i) = n
    · exact e
    · rw [if_neg e] at h; exact absurd rfl h
  rcases hI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact read 0 (by decide) rfl
  · exact read 1 (by decide) rfl
  · exact read 2 (by decide) rfl
  · exact read 3 (by decide) rfl
  · -- App's write
    have hk0 := hkind 0 (by rw [← hApp]; exact hc)
    obtain ⟨hw, _⟩ := hS.app hk0
    obtain ⟨hm, ht⟩ := tuple_get hw
    refine ⟨_, hm, ?_⟩
    obtain ⟨_, f2⟩ := cpu_fld (M := M) (row := row) hi (j := 0) (by decide)
    simp only [List.map_cons, List.map_nil, cv, cpuCol_ctr, cpuCol_stk, B.c, E.eval, ht]
    rw [show fld 1 = fld (2 * 0 + 1) from rfl, f2]; rfl
  all_goals
    have hk3 := hkind 3 (by rw [← hSS]; exact hc)
    obtain ⟨w1, w2, w3, _⟩ := hS.s hk3
    obtain ⟨_, f4⟩ := cpu_fld (M := M) (row := row) hi (j := 2) (by decide)
    obtain ⟨f6, f7⟩ := cpu_fld (M := M) (row := row) hi (j := 3) (by decide)
  · obtain ⟨hm, ht⟩ := tuple_get w1
    refine ⟨_, hm, ?_⟩
    simp only [List.map_cons, List.map_nil, cv, cpuCol_ctr, B.c, E.eval, ht]
    rw [show fld 4 = fld (2 * 2) from rfl, show fld 6 = fld (2 * 3) from rfl, (cpu_fld (M := M) (row := row) hi (j := 2) (by decide)).1, f6]
    rfl
  · obtain ⟨hm, ht⟩ := tuple_get w2
    refine ⟨_, hm, ?_⟩
    simp only [List.map_cons, List.map_nil, cv, cpuCol_ctr, B.c, B.one, E.eval, ht, ← ofN_add]
    rw [show fld 7 = fld (2 * 3 + 1) from rfl, f7]
    rfl
  · obtain ⟨hm, ht⟩ := tuple_get w3
    refine ⟨_, hm, ?_⟩
    simp only [List.map_cons, List.map_nil, cv, cpuCol_ctr, B.c, B.one, E.eval, ht, ← ofN_add]
    rw [show fld 6 = fld (2 * 3) from rfl, f6]
    rfl


section

variable {M : List Cell} {row : Nat → Row} {k : Nat} (hv : ∀ i, i < k → Valid M (row i))
include hv

/-- **The CPU's lookups are honest**: a send with nonzero count carries
    a memory cell's tuple. -/
theorem cpu_honest : ∀ r, r < (cpuTable M row k).h → ∀ I ∈ cpuInters,
    I.count.eval ((cpuTable M row k).env r) ≠ 0 →
    ∃ m, m < M.length ∧ I.fields.map (fun e => e.eval ((cpuTable M row k).env r)) = tupleOf M m :=
  fun i hi => cpu_honestAt hi (hv i hi)
end

theorem programRows_pad {heap : List Cell} {i : Nat} (h : heap.length ≤ i) :
    ((programRows heap).getD i []).getD 4 0 = 0 := by
  unfold programRows
  rw [List.getD_eq_getElem?_getD (a := ([] : List F)), List.getElem?_append_right (by simp [h]),
    List.getElem?_replicate]
  split <;> rfl

/-- **The program table's sends are honest**, given the loaded heap at the
    front of the memory. -/
theorem prog_honest {M heap : List Cell} (h0 : M.take heap.length = heap) :
    ∀ r, r < (progTable heap).h → ∀ I ∈ (progAir heap).inters,
    I.count.eval ((progTable heap).env r) ≠ 0 →
    ∃ m, m < M.length ∧ I.fields.map (fun e => e.eval ((progTable heap).env r)) = tupleOf M m := by
  intro i (hi : i < (programRows heap).length) I hI hc
  simp only [progAir, List.mem_cons, List.not_mem_nil, or_false] at hI
  subst hI
  have hpre : ∀ j, (prec j).eval ((progTable heap).env i) = ((programRows heap).getD i []).getD j 0 := by
    intro j
    show (progTable heap).pre ((i + 0) % (programRows heap).length) j = _
    rw [Nat.add_zero, Nat.mod_eq_of_lt hi]; rfl
  rcases Nat.lt_or_ge i heap.length with hl | hl
  · have hget : M[i]? = some heap[i] := by
      have := congrArg (fun l => l[i]?) h0
      simp only [List.getElem?_take, if_pos hl] at this
      rw [this, List.getElem?_eq_getElem hl]
    obtain ⟨hm, ht⟩ := tuple_get hget
    refine ⟨_, hm, ?_⟩
    simp only [List.map_cons, List.map_nil, hpre, programRows_get hl, ht]
    rfl
  · exact absurd (by rw [show (prec 4).eval _ = _ from hpre 4, programRows_pad hl]) hc

-- ---------------------------------------------------------------------------
-- Completeness
-- ---------------------------------------------------------------------------

section

variable {M : List Cell} {t : Term} {k : Nat} {row : Nat → Row} (hA : Accepts M t k row)
include hA

theorem accepts_valid : ∀ i, i < k → Valid M (row i) := by
  intro i hi
  rcases Nat.lt_or_ge (i + 1) k with h | h
  · rcases hA.trans i h with h' | h'
    · exact .inl (by rw [h']; rfl)
    · exact .inr h'.1
  · have e : i = k - 1 := by omega
    exact .inr (e ▸ hA.final)

/-- A field of a cell an active read finds points into the memory. -/
theorem field_lt (hfit : Fits M) {i : Nat} (hi : i < k) {j : Nat} (hj : j < 4)
    (ha : actOf (kindOf M (row i)) j = 1) : (fieldsAt M (row i) j).2 < M.length := by
  obtain ⟨cell, hrd, _⟩ := (shape (accepts_valid hA i hi)).reads j hj ha
  obtain ⟨_, hget⟩ := rd_get hrd
  have hfa : fieldsAt M (row i) j = cellFields cell := by unfold fieldsAt; rw [hrd]; rfl
  rw [hfa]
  exact (hfit cell (List.mem_of_getElem? hget)).2

/-- Every stack pointer points into the memory. -/
theorem stk_le (hfit : Fits M) : ∀ i, i < k → (row i).stk ≤ M.length := by
  have hctr := hA.ctr_le
  intro i
  induction i with
  | zero =>
    intro h0
    obtain ⟨_, _, hs⟩ := load_fits t
    have hl := hctr 0 h0
    rw [hA.stk0]; rw [hA.ctr0] at hl; omega
  | succ i ih =>
    intro hi1
    have hi : i < k := Nat.lt_of_succ_lt hi1
    have hS := shape (accepts_valid hA i hi)
    rcases hA.trans i hi1 with h | h
    · rcases Nat.lt_or_ge (kindOf M (row i)) 4 with h4 | h4
      · rcases (show kindOf M (row i) = 0 ∨ kindOf M (row i) = 1 ∨ kindOf M (row i) = 2 ∨ kindOf M (row i) = 3 by omega)
          with e | e | e | e
        · rw [(hS.app e).2] at h; rw [← Option.some.inj h]; exact hctr i hi
        · rw [hS.i e] at h; rw [← Option.some.inj h]
          exact Nat.le_of_lt (field_lt hA hfit hi (j := 1) (by decide) (by rw [e]; rfl))
        · rw [hS.k2 e] at h; rw [← Option.some.inj h]
          exact Nat.le_of_lt (field_lt hA hfit hi (j := 2) (by decide) (by rw [e]; rfl))
        · rw [(hS.s e).2.2.2] at h
          have h1 := hctr (i + 1) hi1
          rw [← Option.some.inj h] at h1 ⊢
          show (row i).ctr + 2 ≤ M.length
          have : (row i).ctr + 3 ≤ M.length := h1
          omega
      · rw [hS.none h4] at h; cases h
    · rw [h.2]; exact ih hi

/-- **Completeness of the corpus circuit**: a run the Lean AIR accepts,
    with its memory's cells pointing into it, at most `2^24` cells (the
    range checks' reach) and at most `2^27` rows (a domain), gives tables
    the circuit the verifier builds for `t` accepts, and they decode back
    to the run. -/
theorem base_complete (hfit : Fits M) (hL : M.length ≤ 2 ^ 24) (hk : k ≤ 2 ^ 27) :
    ∃ C Mm Pg, Accepted (baseAirs t) [C, Mm, Pg] ∧ C.h = k ∧ memOf Mm = M ∧
      ∀ i, i < k → rowOf C i = row i := by
  have hv := accepts_valid hA
  have hctr := hA.ctr_le
  have hPb := P_big
  have hML : M.length < P := by omega
  have hb : ∀ i, i < k → (row i).ctr ≤ 2 ^ 24 := fun i hi => Nat.le_trans (hctr i hi) hL
  have h0 : M.take (load t).heap.length = (load t).heap := by rw [← hA.ctr0]; exact hA.heap0
  have hlen0 : (load t).heap.length ≤ M.length := by
    have := congrArg List.length h0
    rw [List.length_take] at this
    omega
  obtain ⟨_, _, hstk⟩ := load_fits t
  have hpos : 0 < (load t).heap.length := Nat.lt_of_le_of_lt (Nat.zero_le _) hstk
  have hPg := programRows_length_le (Nat.le_trans hlen0 hL)
  have hcpu := cpu_sat hv hA.trans hA.final hb hA.pos
  rw [hA.hd0, hA.stk0, hA.ctr0] at hcpu
  obtain ⟨hps, hpre⟩ := prog_sat (load t).heap hpos
  let C := cpuTable M row k
  let Pg := progTable (load t).heap
  let Mm := memTable M C Pg (load t).hd (load t).stk (load t).heap.length (load t).heap
  refine ⟨C, Mm, Pg, ⟨rfl, ?_, ?_, ?_, ?_⟩, rfl, ?_, ?_⟩
  · intro p hp
    simp only [baseAirs, List.zip_cons_cons, List.zip_nil_right, List.mem_cons, List.not_mem_nil,
      or_false] at hp
    rcases hp with rfl | rfl | rfl
    · exact ⟨hcpu, .inl rfl⟩
    · exact ⟨mem_sat M C Pg _ _ _ _ (Nat.lt_of_lt_of_le hpos hlen0), .inl rfl⟩
    · exact ⟨hps, .inr hpre⟩
  · exact balanced hML (cpu_honest hv) (prog_honest h0)
  · show HeightsOK (baseTables (load t).hd (load t).stk (load t).heap.length (load t).heap C Mm Pg)
    unfold HeightsOK baseTables
    simp only [List.foldr_cons, List.foldr_nil, cpuAir, memAir, progAir, cpuInters_weight]
    show 8 * k + (0 * M.length + ((1 + 0) * (programRows (load t).heap).length + 0)) < P
    have : P = 2013265921 := rfl
    omega
  · intro p hp
    simp only [baseAirs, List.zip_cons_cons, List.zip_nil_right, List.mem_cons, List.not_mem_nil,
      or_false] at hp
    rcases hp with rfl | rfl | rfl
    · exact hk
    · show M.length ≤ 2 ^ 27; omega
    · show (programRows (load t).heap).length ≤ 2 ^ 27; omega
  · -- the memory decodes back
    apply List.ext_getElem?
    intro m
    unfold memOf
    rw [List.getElem?_map]
    rcases Nat.lt_or_ge m Mm.h with hm | hm
    · rw [List.getElem?_range hm, Option.map_some]
      have hm' : m < M.length := hm
      have hg : M.getD m .nil = M[m] := by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hm']; rfl
      have hf := hfit _ (List.getElem_mem hm')
      show some (cellOf (ofN (cellTag (M.getD m .nil))) (ofN (cellFields (M.getD m .nil)).1)
        (ofN (cellFields (M.getD m .nil)).2)) = _
      rw [hg, cellOf_enc _ (by omega) (by omega), List.getElem?_eq_getElem hm']
    · rw [List.getElem?_eq_none (by rw [List.length_range]; exact hm), List.getElem?_eq_none hm]; rfl
  · -- the rows decode back
    intro i hi
    have hc := hctr i hi
    have hs := stk_le hA hfit i hi
    obtain ⟨cell, hrd, _⟩ := (shape (hv i hi)).reads 0 (by decide) rfl
    have hh := (rd_get hrd).1
    show (⟨(ofN (row i).hd).val, (ofN (row i).stk).val, (ofN (row i).ctr).val⟩ : Row) = row i
    rw [val_ofN (by show (row i).hd < P; have : (row i).hd < (row i).ctr := hh; omega),
      val_ofN (by omega), val_ofN (by omega)]

end

-- ---------------------------------------------------------------------------
-- From evaluation
-- ---------------------------------------------------------------------------

/-- A machine state whose cells and registers point into its heap. -/
def MFits (m : Mach) : Prop := Fits m.heap ∧ m.hd < m.heap.length ∧ m.stk < m.heap.length

theorem fits_get {h : List Cell} (hf : Fits h) {a : Nat} {c : Cell} (hg : h[a]? = some c) :
    (cellFields c).1 < h.length ∧ (cellFields c).2 < h.length :=
  hf c (List.mem_of_getElem? hg)

/-- **A step keeps the pointers in the heap.** -/
theorem mstep_fits {m m' : Mach} (hm : MFits m) (hs : mstep m = some m') : MFits m' := by
  obtain ⟨hf, hhd, hstk⟩ := hm
  unfold mstep at hs
  cases h0 : m.get m.hd with
  | none => rw [h0] at hs; cases hs
  | some c0 =>
    have f0 := fits_get hf h0
    rw [h0] at hs
    cases c0 with
    | app f x =>
      simp only [alloc, Option.some.injEq] at hs
      subst hs
      simp only [cellFields] at f0
      refine ⟨fits_push hf ⟨by simp only [cellFields]; omega, by simp only [cellFields]; omega⟩, ?_, ?_⟩ <;>
        simp only [List.length_append, List.length_singleton] <;> omega
    | I =>
      cases h1 : m.get m.stk with
      | none => simp only [h1] at hs; cases hs
      | some c1 =>
        have f1 := fits_get hf h1
        cases c1 with
        | cons x s =>
          simp only [h1, Option.some.injEq] at hs
          subst hs
          exact ⟨hf, f1.1, f1.2⟩
        | _ => simp only [h1] at hs; cases hs
    | K =>
      cases h1 : m.get m.stk with
      | none => simp only [h1] at hs; cases hs
      | some c1 =>
        have f1 := fits_get hf h1
        cases c1 with
        | cons x s1 =>
          cases h2 : m.get s1 with
          | none => simp only [h1, h2] at hs; cases hs
          | some c2 =>
            have f2 := fits_get hf h2
            cases c2 with
            | cons y s2 =>
              simp only [h1, h2, Option.some.injEq] at hs
              subst hs
              exact ⟨hf, f1.1, f2.2⟩
            | _ => simp only [h1, h2] at hs; cases hs
        | _ => simp only [h1] at hs; cases hs
    | S =>
      cases h1 : m.get m.stk with
      | none => simp only [h1] at hs; cases hs
      | some c1 =>
        have f1 := fits_get hf h1
        cases c1 with
        | cons x s1 =>
          cases h2 : m.get s1 with
          | none => simp only [h1, h2] at hs; cases hs
          | some c2 =>
            have f2 := fits_get hf h2
            cases c2 with
            | cons y s2 =>
              cases h3 : m.get s2 with
              | none => simp only [h1, h2, h3] at hs; cases hs
              | some c3 =>
                have f3 := fits_get hf h3
                cases c3 with
                | cons z s3 =>
                  simp only [h1, h2, h3, alloc, Option.some.injEq] at hs
                  subst hs
                  simp only [cellFields] at f1 f2 f3
                  have up : ∀ {a n : Nat}, a < n → a < n + 1 := fun h => Nat.lt_succ_of_lt h
                  have a1 : (cellFields (Cell.app y z)).1 < m.heap.length + 1 ∧
                      (cellFields (Cell.app y z)).2 < m.heap.length + 1 := ⟨up f2.1, up f3.1⟩
                  have g1 := fits_push hf a1
                  have a2 : (cellFields (Cell.cons m.heap.length s3)).1 < (m.heap ++ [Cell.app y z]).length + 1 ∧
                      (cellFields (Cell.cons m.heap.length s3)).2 < (m.heap ++ [Cell.app y z]).length + 1 := by
                    simp only [List.length_append, List.length_singleton, cellFields]
                    exact ⟨up (Nat.lt_succ_self _), up (up f3.2)⟩
                  have g2 := fits_push g1 a2
                  have a3 : (cellFields (Cell.cons z (m.heap ++ [Cell.app y z]).length)).1 <
                        (m.heap ++ [Cell.app y z] ++ [Cell.cons m.heap.length s3]).length + 1 ∧
                      (cellFields (Cell.cons z (m.heap ++ [Cell.app y z]).length)).2 <
                        (m.heap ++ [Cell.app y z] ++ [Cell.cons m.heap.length s3]).length + 1 := by
                    simp only [List.length_append, List.length_singleton, cellFields]
                    exact ⟨up (up (up f3.1)), up (Nat.lt_succ_self _)⟩
                  have g3 := fits_push g2 a3
                  refine ⟨g3, ?_, ?_⟩
                  · show x < (m.heap ++ [Cell.app y z] ++ [Cell.cons m.heap.length s3] ++
                      [Cell.cons z (m.heap ++ [Cell.app y z]).length]).length
                    simp only [List.length_append, List.length_singleton]
                    exact up (up (up f1.1))
                  · show (m.heap ++ [Cell.app y z] ++ [Cell.cons m.heap.length s3]).length <
                      (m.heap ++ [Cell.app y z] ++ [Cell.cons m.heap.length s3] ++
                        [Cell.cons z (m.heap ++ [Cell.app y z]).length]).length
                    simp only [List.length_append, List.length_singleton]
                    exact Nat.lt_succ_self _
                | _ => simp only [h1, h2, h3] at hs; cases hs
            | _ => simp only [h1, h2] at hs; cases hs
        | _ => simp only [h1] at hs; cases hs
    | _ => cases hs

theorem iterM_fits : ∀ (i : Nat) {m : Mach}, MFits m → MFits (iterM i m)
  | 0, _, h => h
  | i + 1, m, h => by
    show MFits (iterM i (adv m))
    apply iterM_fits i
    unfold adv
    cases hs : mstep m with
    | none => exact h
    | some m' => exact mstep_fits h hs

/-- A height the verifier accepts for the CPU or the memory table: a power
    of two, at most `2^21` (`MAX_LOG_HEIGHT` in `bench/plonky3/src/main.rs`,
    which keeps every address and counter within the range checks). -/
def VHeight (n : Nat) : Prop := ∃ d, d ≤ 21 ∧ n = 2 ^ d

theorem VHeight.le {n : Nat} (h : VHeight n) : n ≤ 2 ^ 21 := by
  obtain ⟨d, hd, rfl⟩ := h
  exact Nat.pow_le_pow_right (by decide) hd

theorem fits_pad {M : List Cell} (hf : Fits M) (n : Nat) : Fits (M ++ List.replicate n .nil) := by
  intro c hc
  rw [List.length_append]
  rcases List.mem_append.1 hc with hc' | hc'
  · have := hf c hc'; exact ⟨by omega, by omega⟩
  · rw [List.eq_of_mem_replicate hc']
    have : 0 < n := by
      rcases n with _ | n
      · simp at hc'
      · exact Nat.succ_pos _
    rw [List.length_replicate]
    exact ⟨by simp only [cellFields]; omega, by simp only [cellFields]; omega⟩

/-- **Completeness at the verifier's heights**: a run the Lean AIR accepts,
    on `k` rows and a memory padded with nils to `L` cells, both heights the
    verifier accepts, gives tables of exactly those heights that the circuit
    accepts, decoding back to the run and the padded memory; the Rust prover
    pads so (`table_of`). -/
theorem base_complete_padded {M : List Cell} {t : Term} {k : Nat} {row : Nat → Row}
    (hA : Accepts M t k row) (hfit : Fits M) {L : Nat} (hML : M.length ≤ L) (hL : VHeight L)
    (hk : VHeight k) :
    ∃ C Mm Pg, Accepted (baseAirs t) [C, Mm, Pg] ∧ C.h = k ∧ Mm.h = L ∧
      memOf Mm = M ++ List.replicate (L - M.length) .nil ∧ ∀ i, i < k → rowOf C i = row i := by
  have hA' := hA.pad (List.replicate (L - M.length) .nil)
  have hlen : (M ++ List.replicate (L - M.length) Cell.nil).length = L := by
    rw [List.length_append, List.length_replicate]; omega
  have h21 : (2 : Nat) ^ 21 ≤ 2 ^ 24 := by decide
  have h27 : (2 : Nat) ^ 21 ≤ 2 ^ 27 := by decide
  obtain ⟨C, Mm, Pg, hacc, hCh, hmem, hrow⟩ := base_complete hA' (fits_pad hfit _)
    (by rw [hlen]; exact Nat.le_trans hL.le h21) (Nat.le_trans hk.le h27)
  refine ⟨C, Mm, Pg, hacc, hCh, ?_, hmem, hrow⟩
  rw [← memOf_length Mm, hmem, hlen]

/-- **Completeness from evaluation**: when `t` evaluates to `v`, its run
    halts after `n` transitions on a memory `M`, and at every CPU height
    `k > n` and memory height `L ≥ |M|` the verifier accepts, the corpus
    circuit accepts tables of exactly those heights that decode to `M`,
    padded with nils, and end on `v`. -/
theorem eval_complete {t v : Term} (he : Eval t v) :
    ∃ (n : Nat) (M : List Cell), ∀ k L, n < k → VHeight k → M.length ≤ L → VHeight L →
      ∃ C Mm Pg, Accepted (baseAirs t) [C, Mm, Pg] ∧ C.h = k ∧ Mm.h = L ∧
        memOf Mm = M ++ List.replicate (L - M.length) .nil ∧
        decode (st (memOf Mm) (rowOf C (k - 1))) = some v := by
  obtain ⟨N, hN⟩ := evalF_complete he
  obtain ⟨m', c, hr, hstop, hv⟩ := reach_of_evalF hN (hsize (load t)) (Nat.le_refl _) (decode_load t)
  obtain ⟨n, hstep, hfin⟩ := iterM_of_reach hr hstop
  refine ⟨n, m'.heap, fun k L hk hkV hML hLV => ?_⟩
  -- the run, as `air_complete` builds it
  have pre : ∀ i, m'.heap.take (iterM i (load t)).heap.length = (iterM i (load t)).heap := by
    intro i
    obtain ⟨cs, hc⟩ := iterM_prefix (load t) i n
    have e : iterM (i + n) (load t) = m' := hfin _ (by omega)
    rw [e] at hc
    exact take_of_prefix hc
  have hA : Accepts m'.heap t k (fun i => regs (iterM i (load t))) := by
    refine ⟨by omega, pre 0, rfl, rfl, rfl, ?_, ?_⟩
    · intro i _
      by_cases hi : i < n
      · exact .inl (mstep_stepRow (pre i) (pre (i + 1)) (hstep i hi))
      · have e1 : iterM i (load t) = m' := hfin i (by omega)
        have e2 : iterM (i + 1) (load t) = m' := hfin (i + 1) (by omega)
        refine .inr ⟨?_, by show regs _ = regs _; rw [e1, e2]⟩
        show haltRow m'.heap (regs (iterM i (load t))) = true
        rw [e1]
        exact haltRow_of (by simp) hv hstop
    · show haltRow m'.heap (regs (iterM (k - 1) (load t))) = true
      rw [hfin (k - 1) (by omega)]
      exact haltRow_of (by simp) hv hstop
  have hfit : Fits m'.heap := by
    have := iterM_fits n (m := load t) (load_fits t)
    rw [hfin n (Nat.le_refl n)] at this
    exact this.1
  obtain ⟨C, Mm, Pg, hacc, hCh, hMh, hmem, hrow⟩ := base_complete_padded hA hfit hML hLV hkV
  refine ⟨C, Mm, Pg, hacc, hCh, hMh, hmem, ?_⟩
  rw [hmem, hrow (k - 1) (by omega)]
  show decode (st (m'.heap ++ _) (regs (iterM (k - 1) (load t)))) = some v
  rw [hfin (k - 1) (by omega), st_regs (by simp)]
  exact hv

/-- **Completeness of the Rust circuit**: AIRs with the normal forms of
    the verifier's accept the honest tables of every evaluation, at every
    height the verifier accepts that holds the run. -/
theorem export_complete {t v : Term} {Rs : List AirD} (hs : sameAirsB Rs (baseAirs t) = true) (he : Eval t v) :
    ∃ (n : Nat) (M : List Cell), ∀ k L, n < k → VHeight k → M.length ≤ L → VHeight L →
      ∃ C Mm Pg, Accepted Rs [C, Mm, Pg] ∧ C.h = k ∧ Mm.h = L ∧
        memOf Mm = M ++ List.replicate (L - M.length) .nil ∧
        decode (st (memOf Mm) (rowOf C (k - 1))) = some v := by
  obtain ⟨n, M, h⟩ := eval_complete he
  refine ⟨n, M, fun k L hk hkV hML hLV => ?_⟩
  obtain ⟨C, Mm, Pg, hacc, rest⟩ := h k L hk hkV hML hLV
  exact ⟨C, Mm, Pg, accepted_transfer (sameAirsB_symm hs) hacc, rest⟩

end Circuit
