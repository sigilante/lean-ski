import Ski.Circuit.JetTrace
import Ski.Circuit.WitComplete

/-!
# The honest jet tables

The tables a prover builds from a run of `Air.AcceptsJ` (as
`bench/plonky3/src/jets.rs`'s `build_traces` does).  The run may skip rows
(`JRun.skip`) that another part of the circuit accounts for: the probe rows
of a probe run.  `JOK` is what the tables need of the rows not skipped.

- **CPU**: a corpus row is the corpus CPU's row (`cpuCol`), its jet columns
  zero but the counter; an instantiation row has selector 11, its
  registers, and the jet's number, arity, cell count, root operand, root
  argument and rest of the stack.
- **POP**: one row per pop, `clk c i s x s' uses 1` and the bits of
  `c - s - 1`; **INSTW**: one row per written cell, its template row,
  the cell's fields and its arguments.
- **ROOTS**, **HDR**, **TMPL**: each tuple's use count on its first row.
- **Memory**: the cells, each with the count of messages sent to it.
-/

namespace Circuit

open B Air JetTable Mach

/-- A jetted run: memory, public roots and jets, and `k` rows. -/
structure JRun where
  A : List Cell
  roots : List (Nat × Nat)
  jets : List Air.Jet
  k : Nat
  row : Nat → Air.Row
  /-- Rows another part of the circuit accounts for: none in a jetted run,
      the probe rows in a probe run. -/
  skip : Nat → Bool

/-- An argument operand's value. -/
def argVal (ps : List Nat) : Op → Nat
  | .arg i => ps.getD i 0
  | _ => 0

/-- Whether an operand is argument `j`. -/
def isArg (j : Nat) : Op → Nat
  | .arg i => if i = j then 1 else 0
  | _ => 0

/-- How often a template cell reads argument `j`. -/
def cellUses (j : Nat) (cl : Nat × Option (Op × Op)) : Nat :=
  match cl.2 with
  | some (a, b) => isArg j a + isArg j b
  | none => 0

/-- How often a jet reads argument `j`: its cells' operands and its root. -/
def usesOf (J : Air.Jet) (j : Nat) : Nat :=
  ((symCells J J.body 0).1.map (cellUses j)).sum + isArg j (symCells J J.body 0).2

/-- The 24 bits of `n`. -/
def bitsOf (n : Nat) : List F := (List.range RANGE_BITS).map fun b => ofN ((n / 2 ^ b) % 2)

def popRow (i c j s x s' u : Nat) : List F :=
  [ofN i, ofN c, ofN j, ofN s, ofN x, ofN s', ofN u, 1] ++ bitsOf (c - s - 1)

/-- An INSTW row: the counter, the instantiation's counter, the template
    row, the cell's fields, its arguments, active. -/
def instwRow (i c g j : Nat) (ps : List Nat) (cl : Nat × Option (Op × Op)) : List F :=
  [ofN i, ofN c] ++ tmplRow g j cl ++
    [ofN (cellFields (JetTable.cellOf c ps cl)).1, ofN (cellFields (JetTable.cellOf c ps cl)).2,
     ofN (match cl.2 with | some (a, _) => argVal ps a | none => 0),
     ofN (match cl.2 with | some (_, b) => argVal ps b | none => 0), 1]

/-- The rows of a list, as a table's columns (zero past the list). -/
def ofRows (rows : List (List F)) (q c : Nat) : F := (rows.getD q []).getD c 0

namespace JRun

variable (R : JRun)

/-- The jet row `i` instantiates, if any. -/
def instAt (i : Nat) : Option (Nat × Air.Jet) :=
  if R.skip i then none else if i + 1 < R.k then jetOf R.A R.roots R.jets (R.row i) (R.row (i + 1)) else none

def popsR (i : Nat) (J : Air.Jet) : Option (List Nat × Nat) :=
  popR (fun a => R.A[a]?) (R.row i).ctr J.xs.length (R.row i).stk

def ps (i : Nat) (J : Air.Jet) : List Nat := ((R.popsR i J).map Prod.fst).getD []
def rest (i : Nat) (J : Air.Jet) : Nat := ((R.popsR i J).map Prod.snd).getD 0

def rowQ (i : Nat) : Air.Row := Circuit.rowQ R.row R.k i

/-- An instantiation row's columns. -/
def instCol (i g : Nat) (J : Air.Jet) (col : Nat) : F :=
  if col = HD then ofN (R.row i).hd else if col = STK then ofN (R.row i).stk
  else if col = CTR then ofN (R.row i).ctr
  else if col = SEL + 11 then 1
  else if col = J_CLK then ofN i else if col = J_G then ofN g else if col = J_K then ofN J.xs.length
  else if col = J_N then ofN (symCells J J.body 0).1.length
  else if col = J_RL then (opCols (symCells J J.body 0).2).getD 0 0
  else if col = J_RA then (opCols (symCells J J.body 0).2).getD 1 0
  else if col = J_RG then (opCols (symCells J J.body 0).2).getD 2 0
  else if col = J_RV then (opCols (symCells J J.body 0).2).getD 3 0
  else if col = J_XROOT then ofN (argVal (R.ps i J) (symCells J J.body 0).2)
  else if col = J_REST then ofN (R.rest i J)
  else 0

/-- **The honest jet-CPU row.** -/
def cpuCol (i col : Nat) : F :=
  match R.instAt i with
  | none => if col < CPU_WIDTH then Circuit.cpuCol R.A (R.rowQ i) col else if col = J_CLK then ofN i else 0
  | some (g, J) => R.instCol i g J col

def cpuTable (K : Nat) : Table := ⟨K, fun i col => R.cpuCol i col, fun _ _ => 0⟩

/-- The POP rows of row `i`'s instantiation. -/
def popRowsAt (i : Nat) : List (List F) :=
  match R.instAt i with
  | some (_, J) => (popsOf R.A (R.row i).ctr J.xs.length (R.row i).stk).zipIdx.map fun (p, j) =>
      popRow i (R.row i).ctr j p.1 p.2.1 p.2.2 (usesOf J j)
  | none => []

/-- The INSTW rows of row `i`'s instantiation. -/
def instwRowsAt (i : Nat) : List (List F) :=
  match R.instAt i with
  | some (g, J) => (symCells J J.body 0).1.zipIdx.map fun (cl, j) => instwRow i (R.row i).ctr g j (R.ps i J) cl
  | none => []

def popRows (K : Nat) : List (List F) := (List.range K).flatMap R.popRowsAt
def instwRows (K : Nat) : List (List F) := (List.range K).flatMap R.instwRowsAt

def popTable (K HP : Nat) : Table := ⟨HP, ofRows (R.popRows K), fun _ _ => 0⟩
def instwTable (K HW : Nat) : Table := ⟨HW, ofRows (R.instwRows K), fun _ _ => 0⟩

/-- How often the CPU looks up a root, a header; how often INSTW looks up a
    template row. -/
def cntRoots (K : Nat) (v : List F) : Nat :=
  sumTo K fun i => match R.instAt i with
    | some (g, _) => if [ofN (R.row i).hd, ofN g] = v then 1 else 0
    | none => 0

def cntHdr (K : Nat) (v : List F) : Nat :=
  sumTo K fun i => match R.instAt i with
    | some (g, J) => if hdrRow J g = v then 1 else 0
    | none => 0

def cntTmpl (K : Nat) (v : List F) : Nat :=
  sumTo K fun i => match R.instAt i with
    | some (g, J) => ((symCells J J.body 0).1.zipIdx.map fun (cl, j) => if tmplRow g j cl = v then 1 else 0).sum
    | none => 0

end JRun

/-- Row `q` is its tuple's first occurrence. -/
def firstOcc (rows : List (List F)) (q : Nat) : Bool :=
  (List.range q).all fun q' => !(decide (rows.getD q' [] = rows.getD q []))

/-- A provider's table: each tuple's count on its first row. -/
def provTable (rows : List (List F)) (cnt : List F → Nat) : Table :=
  ⟨rows.length, fun q _ => if firstOcc rows q then ofN (cnt (rows.getD q [])) else 0, ofRows rows⟩

/-- The memory table: each cell, with the count of messages sent to it by
    the CPU, the program, POP and INSTW. -/
def memTableJ (A : List Cell) (cpu prog pop instw : AirD) (C Pg Po Iw : Table) : Table :=
  ⟨A.length, fun m col =>
    if col = 0 then ofN m
    else if col = 1 then ofN (cellTag (A.getD m .nil))
    else if col = 2 then ofN (cellFields (A.getD m .nil)).1
    else if col = 3 then ofN (cellFields (A.getD m .nil)).2
    else if col = 4 then tableSends cpu C "mem" (tupleOf A m) + (tableSends prog Pg "mem" (tupleOf A m) +
      (tableSends pop Po "mem" (tupleOf A m) + tableSends instw Iw "mem" (tupleOf A m)))
    else 0, fun _ _ => 0⟩

/-- A machine kind is one of the eleven. -/
theorem kindOf_lt (M : List Cell) (r : Air.Row) : kindOf M r < 11 := by
  unfold kindOf
  repeat' split
  all_goals decide

/-- **What the honest tables need of a jetted run**: every row not skipped
    before the last steps, instantiates or repeats a halt, the last halts,
    and the counters stay in memory. -/
structure JOK (R : JRun) : Prop where
  pos : 0 < R.k
  trans : ∀ i, i + 1 < R.k → R.skip i = false →
    stepRow R.A (R.row i) = some (R.row (i + 1)) ∨
    (∃ g J, ((R.row i).hd, g) ∈ R.roots ∧ R.jets[g]? = some J ∧ instRow R.A J (R.row i) = some (R.row (i + 1))) ∨
    (haltRow R.A (R.row i) = true ∧ R.row (i + 1) = R.row i)
  final : haltRow R.A (R.row (R.k - 1)) = true
  ctr : ∀ i, i < R.k → (R.row i).ctr ≤ R.A.length

/-- A run of `Air.AcceptsJ` is one, skipping no row. -/
theorem AcceptsJ.jok {A : List Cell} {m0 : Mach} {roots : List (Nat × Nat)} {jets : List Air.Jet} {k : Nat}
    {row : Nat → Air.Row} (hA : AcceptsJ A m0 roots jets k row) (hroots : RootsOK m0.heap roots jets) :
    JOK ⟨A, roots, jets, k, row, fun _ => false⟩ :=
  ⟨hA.pos, fun i hi _ => hA.trans i hi, hA.final, fun i hi => (hA.reach hroots i hi).2.1⟩

-- ---------------------------------------------------------------------------
-- The run's facts
-- ---------------------------------------------------------------------------

namespace JRun

variable {R : JRun} (hA : JOK R)
include hA

omit hA in
theorem instAt_some {i g : Nat} {J : Air.Jet} (h : R.instAt i = some (g, J)) :
    i + 1 < R.k ∧ ((R.row i).hd, g) ∈ R.roots ∧ R.jets[g]? = some J ∧
      instRow R.A J (R.row i) = some (R.row (i + 1)) := by
  unfold instAt at h
  split at h
  · cases h
  · split at h
    · next hi => exact ⟨hi, jetOf_some h⟩
    · cases h

omit hA in
theorem instAt_none_of {i : Nat} (hi : R.k ≤ i + 1) : R.instAt i = none := by
  unfold instAt; split
  · rfl
  · rw [if_neg (by omega)]

omit hA in
theorem rowQ_lt {i : Nat} (hi : i < R.k) : R.rowQ i = R.row i := by
  show Circuit.rowQ R.row R.k i = _; unfold Circuit.rowQ; rw [if_pos hi]

omit hA in
theorem rowQ_ge {i : Nat} (hi : R.k ≤ i) : R.rowQ i = R.row (R.k - 1) := by
  show Circuit.rowQ R.row R.k i = _; unfold Circuit.rowQ; rw [if_neg (by omega)]

/-- **A row not skipped that does not instantiate steps, or has halted and
    repeats.** -/
theorem base_trans {i : Nat} (hn : R.instAt i = none) (hs : R.skip i = false) :
    stepRow R.A (R.rowQ i) = some (R.rowQ (i + 1)) ∨
      (haltRow R.A (R.rowQ i) = true ∧ R.rowQ (i + 1) = R.rowQ i) := by
  have hk := hA.pos
  rcases Nat.lt_or_ge (i + 1) R.k with h1 | h1
  · rw [rowQ_lt (Nat.lt_of_succ_lt h1), rowQ_lt h1]
    have hn' : jetOf R.A R.roots R.jets (R.row i) (R.row (i + 1)) = none := by
      unfold instAt at hn; rwa [hs, if_neg Bool.false_ne_true, if_pos h1] at hn
    exact jetOf_none hn' (hA.trans i h1 hs)
  · rcases Nat.lt_or_ge i R.k with h2 | h2
    · have e : i = R.k - 1 := by omega
      rw [rowQ_lt h2, rowQ_ge h1, e]
      exact .inr ⟨hA.final, rfl⟩
    · rw [rowQ_ge h2, rowQ_ge (by omega)]
      exact .inr ⟨hA.final, rfl⟩

theorem base_valid {i : Nat} (hn : R.instAt i = none) (hs : R.skip i = false) : Valid R.A (R.rowQ i) := by
  rcases JRun.base_trans hA hn hs with h | h
  · exact .inl (by rw [h]; rfl)
  · exact .inr h.1

theorem last_halt {K : Nat} (hkK : R.k ≤ K) : haltRow R.A (R.rowQ (K - 1)) = true := by
  have hk := hA.pos
  rcases Nat.lt_or_ge (K - 1) R.k with h | h
  · rw [rowQ_lt h, show K - 1 = R.k - 1 by omega]; exact hA.final
  · rw [rowQ_ge h]; exact hA.final

/-- The counters stay in memory. -/
theorem ctr_le : ∀ i, (R.rowQ i).ctr ≤ R.A.length := by
  have hk := hA.pos
  intro i
  rcases Nat.lt_or_ge i R.k with h | h
  · rw [rowQ_lt h]; exact hA.ctr i h
  · rw [rowQ_ge h]; exact hA.ctr (R.k - 1) (by omega)

omit hA in
/-- **An instantiation, unfolded**: its pops, its writes, and the next row. -/
theorem inst_spec {i g : Nat} {J : Air.Jet} (h : R.instAt i = some (g, J)) :
    R.popsR i J = some (R.ps i J, R.rest i J) ∧ (R.ps i J).length = J.xs.length ∧
    wrs R.A (R.row i).ctr ((symCells J J.body 0).1.map (JetTable.cellOf (R.row i).ctr (R.ps i J))) = true ∧
    R.row (i + 1) = ⟨(symCells J J.body 0).2.res (R.row i).ctr (R.ps i J), R.rest i J,
      (R.row i).ctr + (symCells J J.body 0).1.length⟩ := by
  obtain ⟨_, _, _, hi⟩ := instAt_some h
  unfold instRow instRowG at hi
  cases hp : popR (fun a => R.A[a]?) (R.row i).ctr J.xs.length (R.row i).stk with
  | none => rw [hp] at hi; cases hi
  | some q =>
    obtain ⟨ps, rest⟩ := q
    rw [hp] at hi
    dsimp only at hi
    have hpR : R.popsR i J = some (ps, rest) := hp
    have eps : R.ps i J = ps := by unfold JRun.ps; rw [hpR]; rfl
    have ert : R.rest i J = rest := by unfold JRun.rest; rw [hpR]; rfl
    obtain ⟨σ, ξ, _, _, hps, _⟩ := popsOf_spec (A := R.A) J.xs.length (R.row i).stk hp
    have hl : ps.length = J.xs.length := by rw [hps, List.length_map, List.length_range]
    have hic := symCells_icells J (R.row i).ctr ps hl J.body 0
    rw [Nat.add_zero] at hic
    rw [← hic] at hi
    dsimp only at hi
    split at hi
    · next hw =>
      rw [eps, ert]
      refine ⟨hpR, hl, by rw [wrs_G]; exact hw, ?_⟩
      rw [List.length_map] at hi
      exact (Option.some.inj hi).symm
    · cases hi

end JRun

end Circuit
