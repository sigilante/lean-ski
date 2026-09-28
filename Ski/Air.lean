import Ski.Heap

open Term

/-!
# The circuit: an AIR over the write-once heap

The prover's trace is a table of rows, one per transition of the heap
machine (`Ski/Heap.lean`), padded to a public budget `k`.  A row holds the
machine's three registers: the head pointer, the stack pointer and the
allocation counter.  The heap is not in the rows.  It is one committed
**memory table** `M`, and a row reaches it only through lookups:
- a **read** of address `a` at a row with counter `c` is `M[a]`, and is
  valid only when `a < c`, so a row reads only what was written before it
  (`rd`);
- a **write** at the counter is a check that `M[c]` holds the cell the rule
  builds (`wr`).

**The constraints** (`Accepts`):
- the first row is the loaded term: `M` begins with the loaded heap, and the
  registers point at the term and the empty stack;
- each row either steps to the next by the local rule `stepRow`, which
  reads at most four cells and writes at most three, or has halted and
  repeats;
- the last row has halted.

`haltRow` decides halting from reads alone: the head is a combinator and
the stack holds fewer arguments than its rule takes.  A write cannot make
a row halt, so a prover who corrupts a write cannot stop the run early.

**The theorems.**
- `stepRow_mstep`, `mstep_stepRow`: a row step is a machine transition, in
  both directions, whenever the memory table extends the machine's heap.
- `air_sound`: a table the constraints accept ends on a state that reads
  back a value `v` with `runF (c + 1) t = some (v, c)`, so `t` evaluates
  to `v` (`air_sound_eval`).
- `air_complete`: when `t` evaluates to `v`, the machine halts after some
  `n` transitions, and at every budget `k > n` there is a memory table and
  a table of `k` rows that the constraints accept, ending on `v`.
- `air_budgets`: and the constraints accept a table of `k` rows exactly
  when `k > n`.  As at L1 (`certified_pad_budgets`), the table's length
  reveals only the public budget.

The memory table is committed data and the lookups are a claim about it.
That a cryptographic lookup argument enforces them is the proof system's
job (§5 of `PLAN.md`); this file fixes what they must enforce.
-/

namespace Air

open Mach

/-- A trace row: the machine's registers. -/
structure Row where
  hd : Nat
  stk : Nat
  ctr : Nat
  deriving DecidableEq, Repr

-- ---------------------------------------------------------------------------
-- The rule table
-- ---------------------------------------------------------------------------

/-- **The rule table**, over a reader `g` of cells and the counter `c`: the
    next head and stack, and the cells written at `c, c + 1, …`.  An unwind
    writes one stack cell; `I` and `K` write nothing; `S` writes `y z` and
    two stack cells. -/
def stepG (g : Nat → Option Cell) (c hd stk : Nat) : Option (Nat × Nat × List Cell) :=
  match g hd with
  | some (.app f x) => some (f, c, [.cons x stk])
  | some .I =>
    match g stk with
    | some (.cons x s) => some (x, s, [])
    | _ => none
  | some .K =>
    match g stk with
    | some (.cons x s1) =>
      match g s1 with
      | some (.cons _ s2) => some (x, s2, [])
      | _ => none
    | _ => none
  | some .S =>
    match g stk with
    | some (.cons x s1) =>
      match g s1 with
      | some (.cons y s2) =>
        match g s2 with
        | some (.cons z s3) => some (x, c + 2, [.app y z, .cons c s3, .cons z (c + 1)])
        | _ => none
      | _ => none
    | _ => none
  | _ => none

/-- **The machine is the rule table** over its own heap. -/
theorem mstep_eq (m : Mach) :
    mstep m = (stepG m.get m.heap.length m.hd m.stk).map
      (fun p => (⟨m.heap ++ p.2.2, p.1, p.2.1⟩ : Mach)) := by
  unfold mstep stepG
  cases h0 : m.get m.hd with
  | none => rfl
  | some c0 =>
    cases c0 with
    | app f x => simp [alloc]
    | I =>
      dsimp only
      cases h1 : m.get m.stk with
      | none => rfl
      | some c1 => cases c1 <;> simp
    | K =>
      dsimp only
      cases h1 : m.get m.stk with
      | none => rfl
      | some c1 =>
        cases c1 with
        | cons x s1 =>
          dsimp only
          cases h2 : m.get s1 with
          | none => rfl
          | some c2 => cases c2 <;> simp
        | _ => rfl
    | S =>
      dsimp only
      cases h1 : m.get m.stk with
      | none => rfl
      | some c1 =>
        cases c1 with
        | cons x s1 =>
          dsimp only
          cases h2 : m.get s1 with
          | none => rfl
          | some c2 =>
            cases c2 with
            | cons y s2 =>
              dsimp only
              cases h3 : m.get s2 with
              | none => rfl
              | some c3 =>
                cases c3 with
                | cons z s3 => simp [alloc]
                | _ => rfl
            | _ => rfl
        | _ => rfl
    | nil => rfl
    | cons _ _ => rfl

-- ---------------------------------------------------------------------------
-- Lookups and the constraints
-- ---------------------------------------------------------------------------

/-- A read at a row with counter `c`: the memory table's cell, if it was
    written before the row. -/
def rd (M : List Cell) (c a : Nat) : Option Cell := if a < c then M[a]? else none

/-- The write check: the memory table holds `ws` from address `c` on. -/
def wrs (M : List Cell) : Nat → List Cell → Bool
  | _, [] => true
  | c, w :: ws => (M[c]? == some w) && wrs M (c + 1) ws

/-- **The transition constraint** of one row: the rule table, reading the
    memory table, with its writes checked. -/
def stepRow (M : List Cell) (r : Row) : Option Row :=
  match stepG (rd M r.ctr) r.ctr r.hd r.stk with
  | some (h, s, ws) => if wrs M r.ctr ws then some ⟨h, s, r.ctr + ws.length⟩ else none
  | none => none

/-- The stack at `s` ends within `n` cells: fewer than `n` arguments. -/
def short (M : List Cell) (c : Nat) : Nat → Nat → Bool
  | 0, _ => false
  | n + 1, s =>
    match rd M c s with
    | some .nil => true
    | some (.cons _ s') => short M c n s'
    | _ => false

/-- **The halting constraint**, from reads alone: the head is a combinator
    with fewer arguments than its rule takes. -/
def haltRow (M : List Cell) (r : Row) : Bool :=
  match rd M r.ctr r.hd with
  | some .I => short M r.ctr 1 r.stk
  | some .K => short M r.ctr 2 r.stk
  | some .S => short M r.ctr 3 r.stk
  | _ => false

/-- The machine state a row denotes: the memory table up to the counter. -/
def st (M : List Cell) (r : Row) : Mach := ⟨M.take r.ctr, r.hd, r.stk⟩

/-- The registers of a machine state. -/
def regs (m : Mach) : Row := ⟨m.hd, m.stk, m.heap.length⟩

/-- **The AIR accepts** a table of `k` rows over the memory table `M`, for
    the term `t`. -/
structure Accepts (M : List Cell) (t : Term) (k : Nat) (row : Nat → Row) : Prop where
  pos : 0 < k
  heap0 : M.take (row 0).ctr = (load t).heap
  hd0 : (row 0).hd = (load t).hd
  stk0 : (row 0).stk = (load t).stk
  ctr0 : (row 0).ctr = (load t).heap.length
  trans : ∀ i, i + 1 < k →
    stepRow M (row i) = some (row (i + 1)) ∨ (haltRow M (row i) = true ∧ row (i + 1) = row i)
  final : haltRow M (row (k - 1)) = true

-- ---------------------------------------------------------------------------
-- Reads and writes against a prefix of the memory table
-- ---------------------------------------------------------------------------

theorem rd_eq (M : List Cell) (c a : Nat) : rd M c a = (M.take c)[a]? := by
  unfold rd
  rw [List.getElem?_take]

theorem take_length {M : List Cell} {c : Nat} (h : c ≤ M.length) : (M.take c).length = c := by
  rw [List.length_take]; omega

theorem take_one_more {M : List Cell} {c : Nat} {w : Cell} (h : M[c]? = some w) :
    M.take (c + 1) = M.take c ++ [w] := by
  rw [List.take_add_one, h]; rfl

/-- A write check extends the prefix by the written cells. -/
theorem take_of_wrs : ∀ {M : List Cell} {c : Nat} {ws : List Cell}, wrs M c ws = true →
    M.take (c + ws.length) = M.take c ++ ws
  | _, _, [], _ => by simp
  | M, c, w :: ws, h => by
    unfold wrs at h
    rw [Bool.and_eq_true] at h
    have h1 : M[c]? = some w := beq_iff_eq.1 h.1
    have ih := take_of_wrs h.2
    rw [List.length_cons, show c + (ws.length + 1) = c + 1 + ws.length by omega, ih,
      take_one_more h1, List.append_assoc]
    rfl

theorem wrs_of_take : ∀ {M : List Cell} {c : Nat} {ws : List Cell}, c ≤ M.length →
    M.take (c + ws.length) = M.take c ++ ws → wrs M c ws = true
  | _, _, [], _, _ => rfl
  | M, c, w :: ws, hc, h => by
    have hl := congrArg List.length h
    rw [List.length_take, List.length_append, take_length hc, List.length_cons] at hl
    have hle : c + (ws.length + 1) ≤ M.length := by rw [← hl]; exact Nat.min_le_right _ _
    have h1 : M.take (c + 1) = M.take c ++ [w] := by
      have := congrArg (List.take (c + 1)) h
      rw [List.take_take, Nat.min_eq_left (by simp), List.take_append,
        List.take_of_length_le (l := M.take c) (i := c + 1) (by rw [take_length hc]; omega),
        take_length hc, show c + 1 - c = 1 by omega] at this
      rw [this]
      rfl
    have hw : M[c]? = some w := by
      rw [List.take_add_one] at h1
      have h2 := List.append_cancel_left h1
      cases hc' : M[c]? with
      | none => rw [hc'] at h2; cases h2
      | some y => rw [hc'] at h2; cases h2; rfl
    have hrest : M.take (c + 1 + ws.length) = M.take (c + 1) ++ ws := by
      rw [show c + 1 + ws.length = c + (w :: ws).length by simp; omega, h, h1, List.append_assoc]
      rfl
    unfold wrs
    rw [hw, beq_self_eq_true, Bool.true_and]
    exact wrs_of_take (by omega) hrest

theorem get_st (M : List Cell) (r : Row) : (st M r).get = rd M r.ctr := by
  funext a; rw [rd_eq]; rfl

-- ---------------------------------------------------------------------------
-- The transition constraint is the machine
-- ---------------------------------------------------------------------------

/-- **Soundness of the transition constraint**: a row step is the machine's
    transition on the state the row denotes. -/
theorem stepRow_mstep {M : List Cell} {r r' : Row} (hc : r.ctr ≤ M.length)
    (h : stepRow M r = some r') : mstep (st M r) = some (st M r') ∧ r'.ctr ≤ M.length := by
  unfold stepRow at h
  cases hg : stepG (rd M r.ctr) r.ctr r.hd r.stk with
  | none => rw [hg] at h; cases h
  | some p =>
    obtain ⟨h1, s1, ws⟩ := p
    rw [hg] at h
    dsimp only at h
    cases hw : wrs M r.ctr ws with
    | false => rw [hw] at h; cases h
    | true =>
      rw [hw, if_pos rfl] at h
      cases h
      have ht := take_of_wrs hw
      have hlen := congrArg List.length ht
      rw [List.length_take, List.length_append, take_length hc] at hlen
      refine ⟨?_, by show r.ctr + ws.length ≤ M.length; omega⟩
      rw [mstep_eq, get_st]
      show (stepG (rd M r.ctr) (M.take r.ctr).length r.hd r.stk).map _ = _
      rw [take_length hc, hg]
      show some (⟨M.take r.ctr ++ ws, h1, s1⟩ : Mach) = some ⟨M.take (r.ctr + ws.length), h1, s1⟩
      rw [ht]

/-- **Completeness of the transition constraint**: a machine transition
    between prefixes of the memory table is a row step. -/
theorem mstep_stepRow {M : List Cell} {m m' : Mach} (hm : M.take m.heap.length = m.heap)
    (hm' : M.take m'.heap.length = m'.heap) (h : mstep m = some m') :
    stepRow M (regs m) = some (regs m') := by
  have hc : m.heap.length ≤ M.length := by
    have := congrArg List.length hm
    rw [List.length_take] at this
    omega
  have hg : rd M m.heap.length = m.get := by
    funext a; rw [rd_eq, hm]; rfl
  rw [mstep_eq] at h
  cases hs : stepG m.get m.heap.length m.hd m.stk with
  | none => rw [hs] at h; cases h
  | some p =>
    obtain ⟨h1, s1, ws⟩ := p
    rw [hs] at h
    cases h
    have e : M.take (m.heap.length + ws.length) = M.take m.heap.length ++ ws := by
      rw [hm]
      have := hm'
      rw [List.length_append] at this
      exact this
    have hw := wrs_of_take hc e
    unfold stepRow regs
    dsimp only
    rw [hg, hs]
    dsimp only
    rw [hw, if_pos rfl, List.length_append]

-- ---------------------------------------------------------------------------
-- The halting constraint is the machine's halt
-- ---------------------------------------------------------------------------

/-- **Soundness of the halting constraint**: a halted row denotes a state
    with no transition. -/
theorem haltRow_mstep {M : List Cell} {r : Row} (h : haltRow M r = true) : mstep (st M r) = none := by
  rw [mstep_eq, get_st]
  show (stepG (rd M r.ctr) _ r.hd r.stk).map _ = none
  unfold haltRow at h
  unfold stepG
  cases h0 : rd M r.ctr r.hd with
  | none => rw [h0] at h; cases h
  | some c0 =>
    rw [h0] at h
    cases c0 with
    | I =>
      dsimp only at h ⊢
      unfold short at h
      cases h1 : rd M r.ctr r.stk with
      | none => rw [h1] at h; cases h
      | some c1 => rw [h1] at h; cases c1 <;> first | rfl | cases h
    | K =>
      dsimp only at h ⊢
      unfold short at h
      cases h1 : rd M r.ctr r.stk with
      | none => rw [h1] at h; cases h
      | some c1 =>
        rw [h1] at h
        cases c1 with
        | nil => rfl
        | cons x s1 =>
          dsimp only at h ⊢
          unfold short at h
          cases h2 : rd M r.ctr s1 with
          | none => rw [h2] at h; cases h
          | some c2 => rw [h2] at h; cases c2 <;> first | rfl | cases h
        | _ => cases h
    | S =>
      dsimp only at h ⊢
      unfold short at h
      cases h1 : rd M r.ctr r.stk with
      | none => rw [h1] at h; cases h
      | some c1 =>
        rw [h1] at h
        cases c1 with
        | nil => rfl
        | cons x s1 =>
          dsimp only at h ⊢
          unfold short at h
          cases h2 : rd M r.ctr s1 with
          | none => rw [h2] at h; cases h
          | some c2 =>
            rw [h2] at h
            cases c2 with
            | nil => rfl
            | cons y s2 =>
              dsimp only at h ⊢
              unfold short at h
              cases h3 : rd M r.ctr s2 with
              | none => rw [h3] at h; cases h
              | some c3 => rw [h3] at h; cases c3 <;> first | rfl | cases h
            | _ => cases h
        | _ => cases h
    | _ => cases h

/-- A term's stack cell exists only with fuel left. -/
theorem stackAt_pos {heap : List Cell} {f a : Nat} {ts : List Term} (h : stackAt heap f a = some ts) :
    ∃ f', f = f' + 1 := by
  cases f with
  | zero => unfold stackAt at h; cases h
  | succ f' => exact ⟨f', rfl⟩

/-- **Completeness of the halting constraint**: a state that reads back a
    term and has no transition is a halted row. -/
theorem haltRow_of {M : List Cell} {m : Mach} {t : Term} (hm : M.take m.heap.length = m.heap)
    (hdec : decode m = some t) (hn : mstep m = none) : haltRow M (regs m) = true := by
  have hg : rd M m.heap.length = m.get := by
    funext a; rw [rd_eq, hm]; rfl
  rw [mstep_eq] at hn
  have hs : stepG m.get m.heap.length m.hd m.stk = none := by
    cases e : stepG m.get m.heap.length m.hd m.stk with
    | none => rfl
    | some p => rw [e] at hn; cases hn
  obtain ⟨th, args, h1, h2, _⟩ := decode_eq hdec
  unfold haltRow regs
  dsimp only
  rw [hg]
  unfold stepG at hs
  have hget : ∀ a, m.get a = m.heap[a]? := fun _ => rfl
  -- the stack's first cell
  have stk1 := stackAt_cell h2
  cases termAt_cell h1 with
  | inl hS =>
    rw [hget, hS.1]
    rw [hget, hS.1] at hs
    dsimp only at hs ⊢
    unfold short
    rw [hg]
    rcases stk1 with ⟨hnil, _⟩ | ⟨x, s1, _, rest, hc1, _, hr1, _⟩
    · rw [hget, hnil]
    · rw [hget, hc1]
      rw [hget, hc1] at hs
      dsimp only at hs ⊢
      unfold short
      rw [hg]
      obtain ⟨f1, hf1⟩ := stackAt_pos hr1
      rw [hf1] at hr1
      rcases stackAt_cell hr1 with ⟨hnil, _⟩ | ⟨y, s2, _, rest2, hc2, _, hr2, _⟩
      · rw [hget, hnil]
      · rw [hget, hc2]
        rw [hget, hc2] at hs
        dsimp only at hs ⊢
        unfold short
        rw [hg]
        obtain ⟨f2, hf2⟩ := stackAt_pos hr2
        rw [hf2] at hr2
        rcases stackAt_cell hr2 with ⟨hnil, _⟩ | ⟨z, s3, _, _, hc3, _, _, _⟩
        · rw [hget, hnil]
        · rw [hget, hc3] at hs; cases hs
  | inr h =>
  cases h with
  | inl hK =>
    rw [hget, hK.1]
    rw [hget, hK.1] at hs
    dsimp only at hs ⊢
    unfold short
    rw [hg]
    rcases stk1 with ⟨hnil, _⟩ | ⟨x, s1, _, rest, hc1, _, hr1, _⟩
    · rw [hget, hnil]
    · rw [hget, hc1]
      rw [hget, hc1] at hs
      dsimp only at hs ⊢
      unfold short
      rw [hg]
      obtain ⟨f1, hf1⟩ := stackAt_pos hr1
      rw [hf1] at hr1
      rcases stackAt_cell hr1 with ⟨hnil, _⟩ | ⟨y, s2, _, _, hc2, _, _, _⟩
      · rw [hget, hnil]
      · rw [hget, hc2] at hs; cases hs
  | inr h =>
  cases h with
  | inl hI =>
    rw [hget, hI.1]
    rw [hget, hI.1] at hs
    dsimp only at hs ⊢
    unfold short
    rw [hg]
    rcases stk1 with ⟨hnil, _⟩ | ⟨x, s1, _, _, hc1, _, _, _⟩
    · rw [hget, hnil]
    · rw [hget, hc1] at hs; cases hs
  | inr hA =>
    obtain ⟨g, x, _, _, hc, _, _, _⟩ := hA
    rw [hget, hc] at hs
    cases hs

-- ---------------------------------------------------------------------------
-- The AIR accepts exactly the machine's runs
-- ---------------------------------------------------------------------------

/-- A reachable state reaches one more step. -/
theorem Reach.snoc {m m1 m2 : Mach} {c : Nat} (h : Reach m m1 c) (hs : mstep m1 = some m2) :
    ∃ c', Reach m m2 c' := by
  induction h with
  | refl m =>
    cases hc : isContraction m with
    | false => exact ⟨0, .unwind hs hc (.refl _)⟩
    | true => exact ⟨1, .contract hs hc (.refl _)⟩
  | unwind h1 hc _ ih =>
    obtain ⟨c', h'⟩ := ih hs
    exact ⟨c', .unwind h1 hc h'⟩
  | contract h1 hc _ ih =>
    obtain ⟨c', h'⟩ := ih hs
    exact ⟨c' + 1, .contract h1 hc h'⟩

theorem st_row0 {M : List Cell} {t : Term} {k : Nat} {row : Nat → Row} (h : Accepts M t k row) :
    st M (row 0) = load t := by
  unfold st
  rw [h.heap0, h.hd0, h.stk0]

/-- **Soundness of the AIR.**  A table the constraints accept ends on a
    state that reads back the value `runF` reaches, after `c` contractions. -/
theorem air_sound {M : List Cell} {t : Term} {k : Nat} {row : Nat → Row}
    (h : Accepts M t k row) :
    ∃ v c, decode (st M (row (k - 1))) = some v ∧ runF (c + 1) t = some (v, c) := by
  have inv : ∀ i, i < k → (row i).ctr ≤ M.length ∧ ∃ c, Reach (load t) (st M (row i)) c := by
    intro i
    induction i with
    | zero =>
      intro _
      refine ⟨?_, 0, by rw [st_row0 h]; exact .refl _⟩
      have := congrArg List.length h.heap0
      rw [List.length_take, ← h.ctr0] at this
      omega
    | succ i ih =>
      intro hi
      obtain ⟨hc, c, hr⟩ := ih (by omega)
      cases h.trans i hi with
      | inl hs =>
        obtain ⟨hm, hc'⟩ := stepRow_mstep hc hs
        exact ⟨hc', Reach.snoc hr hm⟩
      | inr hh =>
        rw [hh.2]
        exact ⟨hc, c, hr⟩
  obtain ⟨_, c, hr⟩ := inv (k - 1) (by have := h.pos; omega)
  obtain ⟨j, hj⟩ := mrunC_of_reach hr (haltRow_mstep h.final)
  obtain ⟨v, hv, hrun⟩ := mrunC_sound (decode_load t) hj
  exact ⟨v, c, hv, hrun⟩

/-- A table the constraints accept proves the evaluation it ends on. -/
theorem air_sound_eval {M : List Cell} {t : Term} {k : Nat} {row : Nat → Row}
    (h : Accepts M t k row) : ∃ v, decode (st M (row (k - 1))) = some v ∧ Eval t v := by
  obtain ⟨v, c, hv, hrun⟩ := air_sound h
  refine ⟨v, hv, ?_⟩
  have e := runF_evalF (k := c + 1) (t := t)
  rw [hrun] at e
  exact evalF_sound e.symm

/-- One transition, or none at a halt. -/
def adv (m : Mach) : Mach := (mstep m).getD m

/-- `i` transitions. -/
def iterM : Nat → Mach → Mach
  | 0, m => m
  | i + 1, m => iterM i (adv m)

theorem iterM_succ' : ∀ (i : Nat) (m : Mach), iterM (i + 1) m = adv (iterM i m)
  | 0, _ => rfl
  | i + 1, m => iterM_succ' i (adv m)

theorem adv_prefix (m : Mach) : ∃ cs, (adv m).heap = m.heap ++ cs := by
  unfold adv
  cases h : mstep m with
  | none => exact ⟨[], by simp⟩
  | some m' => exact mstep_append h

theorem iterM_prefix (m : Mach) (i : Nat) : ∀ j, ∃ cs, (iterM (i + j) m).heap = (iterM i m).heap ++ cs
  | 0 => ⟨[], by simp⟩
  | j + 1 => by
    obtain ⟨cs, hc⟩ := iterM_prefix m i j
    obtain ⟨ds, hd⟩ := adv_prefix (iterM (i + j) m)
    refine ⟨cs ++ ds, ?_⟩
    rw [show i + (j + 1) = (i + j) + 1 by omega, iterM_succ', hd, hc, List.append_assoc]

/-- A run to a halt, as iteration. -/
theorem iterM_of_reach {m m' : Mach} {c : Nat} (h : Reach m m' c) (hn : mstep m' = none) :
    ∃ n, (∀ i, i < n → mstep (iterM i m) = some (iterM (i + 1) m)) ∧ ∀ j, n ≤ j → iterM j m = m' := by
  induction h with
  | refl m =>
    refine ⟨0, fun _ h => absurd h (Nat.not_lt_zero _), ?_⟩
    intro j _
    induction j with
    | zero => rfl
    | succ j ih =>
      rw [iterM_succ', ih (Nat.zero_le _)]
      unfold adv
      rw [hn]
      rfl
  | @unwind m m1 m2 c hs _ _ ih =>
    obtain ⟨n, h1, h2⟩ := ih hn
    have ha : adv m = m1 := by unfold adv; rw [hs]; rfl
    refine ⟨n + 1, ?_, ?_⟩
    · intro i hi
      cases i with
      | zero => show mstep m = some (iterM 0 (adv m)); rw [ha]; exact hs
      | succ i => show mstep (iterM i (adv m)) = some (iterM (i + 1) (adv m)); rw [ha]; exact h1 i (by omega)
    · intro j hj
      cases j with
      | zero => omega
      | succ j => show iterM j (adv m) = m2; rw [ha]; exact h2 j (by omega)
  | @contract m m1 m2 c hs _ _ ih =>
    obtain ⟨n, h1, h2⟩ := ih hn
    have ha : adv m = m1 := by unfold adv; rw [hs]; rfl
    refine ⟨n + 1, ?_, ?_⟩
    · intro i hi
      cases i with
      | zero => show mstep m = some (iterM 0 (adv m)); rw [ha]; exact hs
      | succ i => show mstep (iterM i (adv m)) = some (iterM (i + 1) (adv m)); rw [ha]; exact h1 i (by omega)
    · intro j hj
      cases j with
      | zero => omega
      | succ j => show iterM j (adv m) = m2; rw [ha]; exact h2 j (by omega)

theorem take_of_prefix {M h cs : List Cell} (e : M = h ++ cs) : M.take h.length = h := by
  rw [e]; simp

theorem st_regs {M : List Cell} {m : Mach} (hm : M.take m.heap.length = m.heap) : st M (regs m) = m := by
  unfold st regs
  dsimp only
  rw [hm]

/-- **Completeness of the AIR.**  When `t` evaluates to `v`, the machine
    halts after some `n` transitions, and at every budget `k > n` the
    constraints accept a table of `k` rows ending on `v`. -/
theorem air_complete {t v : Term} (he : Eval t v) :
    ∃ n, ∀ k, n < k → ∃ (M : List Cell) (row : Nat → Row),
      Accepts M t k row ∧ decode (st M (row (k - 1))) = some v := by
  obtain ⟨N, hN⟩ := evalF_complete he
  obtain ⟨m', c, hr, hstop, hv⟩ := reach_of_evalF hN (hsize (load t)) (Nat.le_refl _) (decode_load t)
  obtain ⟨n, hstep, hfin⟩ := iterM_of_reach hr hstop
  refine ⟨n, fun k hk => ⟨m'.heap, fun i => regs (iterM i (load t)), ?_, ?_⟩⟩
  · -- every state on the run is a prefix of the last
    have pre : ∀ i, m'.heap.take (iterM i (load t)).heap.length = (iterM i (load t)).heap := by
      intro i
      obtain ⟨cs, hc⟩ := iterM_prefix (load t) i n
      have e : iterM (i + n) (load t) = m' := hfin _ (by omega)
      rw [e] at hc
      exact take_of_prefix hc
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
  · show decode (st m'.heap (regs (iterM (k - 1) (load t)))) = some v
    rw [hfin (k - 1) (by omega), st_regs (by simp)]
    exact hv

/-- **The budgets at which the AIR accepts.**  When `t` evaluates, the
    machine halts after some `n` transitions, and the constraints accept a
    table of `k` rows exactly when `k > n`: one row per transition and at
    least the final halt.  The table's length reveals only the budget. -/
theorem air_budgets {t v : Term} (he : Eval t v) :
    ∃ n, ∀ k, (∃ (M : List Cell) (row : Nat → Row), Accepts M t k row) ↔ n < k := by
  obtain ⟨N, hN⟩ := evalF_complete he
  obtain ⟨m', c, hr, hstop, hv⟩ := reach_of_evalF hN (hsize (load t)) (Nat.le_refl _) (decode_load t)
  obtain ⟨n, hstep, hfin⟩ := iterM_of_reach hr hstop
  refine ⟨n, fun k => ⟨?_, ?_⟩⟩
  · -- every accepted row is a state on the run, no further along than its index
    intro ⟨M, row, h⟩
    have inv : ∀ i, i < k → (row i).ctr ≤ M.length ∧ ∃ j, j ≤ i ∧ st M (row i) = iterM j (load t) := by
      intro i
      induction i with
      | zero =>
        intro _
        refine ⟨?_, 0, Nat.le_refl 0, st_row0 h⟩
        have := congrArg List.length h.heap0
        rw [List.length_take, ← h.ctr0] at this
        omega
      | succ i ih =>
        intro hi
        obtain ⟨hc, j, hj, he'⟩ := ih (by omega)
        cases h.trans i hi with
        | inl hs =>
          obtain ⟨hm, hc'⟩ := stepRow_mstep hc hs
          refine ⟨hc', j + 1, by omega, ?_⟩
          rw [iterM_succ', ← he']
          unfold adv
          rw [hm]
          rfl
        | inr hh =>
          rw [hh.2]
          exact ⟨hc, j, by omega, he'⟩
    obtain ⟨_, j, hj, he'⟩ := inv (k - 1) (by have := h.pos; omega)
    have hn := haltRow_mstep h.final
    rw [he'] at hn
    have hjn : n ≤ j := by
      cases Nat.lt_or_ge j n with
      | inl hlt => rw [hstep j hlt] at hn; cases hn
      | inr hge => exact hge
    have := h.pos
    omega
  · intro hk
    have pre : ∀ i, m'.heap.take (iterM i (load t)).heap.length = (iterM i (load t)).heap := by
      intro i
      obtain ⟨cs, hc⟩ := iterM_prefix (load t) i n
      have e : iterM (i + n) (load t) = m' := hfin _ (by omega)
      rw [e] at hc
      exact take_of_prefix hc
    refine ⟨m'.heap, fun i => regs (iterM i (load t)), by omega, pre 0, rfl, rfl, rfl, ?_, ?_⟩
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

end Air
