import Ski.Circuit.CompPFinal
import Ski.Circuit.CompJComplete

/-!
# The honest tables of the circuit with the Poseidon2 jet

From a run the AIR with segments and the Poseidon2 jet accepts
(`CompM.AcceptsCP`), padded to `K` rows by repeating its last, a Lean model
of the tables `bench/plonky3/src/compp.rs`'s `traces` builds (`lake exe
composed check-p2-tables` compares them with the unblinded traces on a
run that `ski-air compp-dump` writes: every row of each dumped table,
the CPU's read through `P2Run.cpuColP_arr`; gate 5 runs it on `p2pre`
and the hand-off's two runs with the tests' witness):

- the CPU (`P2Run.cpuTableP`): the composed CPU's honest row
  (`cpuTableC`), and on a jet row the selector `P2SEL`, the kinds cleared,
  and the reads of the atom and the two stack cells range-checked;
- P2IN (`pinRow`): per call, a row per input bit, reading its slot and
  summing each element's 31 bits;
- P2OUT (`poutRow`): per call, a row per output bit, reading the stack cell
  the jet wrote and summing the bits, with each element's canonical flags;
- the Poseidon2 table (`p2RowT`): per call, the permutation's trace, every
  round's columns as the specification computes them (`traceAll`);
- the witness table (`witTableP`), on the circuit's own preprocessed rows.

Every blinding flag is clear.  These tables balance on every bus and
carry clear flags (`P2Run.balancedP`, `P2Run.honest_zkP`), and each
satisfies its AIR's constraints (`Ski/Circuit/CompPSat.lean`,
`Ski/Circuit/CompPCpuSat.lean`), so the circuit accepts them
(`compPG_complete_log`).  The Poseidon2 table pads as `p2air.rs` does
(`p2Pad`).

The files: this one (the definitions and the run's rows) → `CompPBal` (the
CPU's messages) → `CompPBits` (P2IN's and P2OUT's) → `CompPTrace` (the
Poseidon2 row's) → `CompPComplete` (the tables' sends, bus by bus) →
`Ski/ZK/CompPHonest.lean` (`balancedP`, `honest_zkP`, `calls_one`) →
`CompPSat` and `CompPCpuSat` (each table's `Sat`) → `CompPCompleteFinal`
(`compPG_complete_log`).
-/

namespace Circuit

open B Air Compose CompM Mach

-- ---------------------------------------------------------------------------
-- The Poseidon2 trace
-- ---------------------------------------------------------------------------

/-- A round's columns, as `P2Air.Round.gen` lays them out: a linear layer's
    sixteen; a full round's cubes, S-box outputs and linear layer; a partial
    round's cube, output and linear layer. -/
def traceR : P2Air.Round → List Nat → List Nat
  | .l0, vs => Poseidon2.extLinear vs
  | .full rc, vs =>
    (List.range 16).map (fun i => (vs.getD i 0 + rc.getD i 0) ^ 3 % Poseidon2.p) ++
      (List.range 16).map (fun i => Poseidon2.sbox (vs.getD i 0 + rc.getD i 0)) ++ Poseidon2.extRound vs rc
  | .part c, vs => [(vs.getD 0 0 + c) ^ 3 % Poseidon2.p, Poseidon2.sbox (vs.getD 0 0 + c)] ++ Poseidon2.intRound vs c

/-- The rounds' columns, each round on the state the previous computed. -/
def traceAll : List P2Air.Round → List Nat → List Nat
  | [], _ => []
  | r :: rs, vs => traceR r vs ++ traceAll rs (r.spec vs)

/-- **The Poseidon2 table's honest row** for the input `s` and the call at
    counter `c`: the inputs, the rounds' columns, the key, active. -/
def p2RowT (c : Nat) (s : List Nat) : List F := (s ++ traceAll P2Air.rounds s).map ofN ++ [ofN c, 1]

/-- **The Poseidon2 table's padding row**, as `p2air.rs`'s `p2_trace_keyed`
    pads: the trace of the zero input's permutation, key `0`, inactive. -/
def p2Pad : List F :=
  (List.replicate 16 0 ++ traceAll P2Air.rounds (List.replicate 16 0)).map ofN ++ [0, 0]

-- ---------------------------------------------------------------------------
-- The jet's bit tables
-- ---------------------------------------------------------------------------

/-- A Boolean in the field. -/
def bF (b : Bool) : F := if b then 1 else 0

/-- A list's bits, by index. -/
def bitF (bs : List Bool) (t : Nat) : Bool := bs.getD t false

/-- The value of level `l`'s element's bits below it (`preB`). -/
def accN (bs : List Bool) (l : Nat) : Nat := BitArith.val (preB (bitF bs) (l - l % 31) (l % 31))

/-- The canonical check's flags at level `l` (`lowB`, `hiB`). -/
def lowL (bs : List Bool) (l : Nat) : Bool := lowB (bitF bs) (l - l % 31) (l % 31)
def hiL (bs : List Bool) (l : Nat) : Bool := hiB (bitF bs) (l - l % 31) (l % 31)

/-- A stack call's input cell at level `l`: `s₁ - l`, the top first. -/
def spAt (s1 : Nat) (l : Nat) : Nat := s1 - l

/-- The stack pointer after level `l`'s cell: the next cell down, or below
    the last the stack under the inputs. -/
def spnAt (s1 rest : Nat) (l : Nat) : Nat := if l = P2_BITS - 1 then rest else s1 - l - 1

/-- **A P2IN row**: `ctr lvl b acc act e pow last islow ilast val nacc em m sp
    spn addr tag f1 f2 ca sa`, level `l` of the call at `c` over the input
    bits `bs`: on the comb (`stk` false) reading the slot `3 + l` with the
    stack pointer `rest` passed along; on the stack reading the cell
    `s₁ - l`. -/
def pinRow (c : Nat) (bs : List Bool) (stk : Bool) (s1 rest : Nat) (l : Nat) : List F :=
  let b := bs.getD l false
  let last := l % 31 = 30
  let v := ofN (accN bs l + 2 ^ (l % 31) * b.toNat)
  let sp := if stk then spAt s1 l else rest
  let spn := if stk then spnAt s1 rest l else rest
  [ofN c, ofN l, bF b, ofN (accN bs l), 1, ofN (l / 31), ofN (2 ^ (l % 31)), bF (decide last),
   bF (decide (l % 31 < 27)), bF (decide (l = P2_BITS - 1)), v, if last then 0 else v, bF (decide last),
   bF stk, ofN sp, ofN spn,
   if stk then ofN sp else ofN (l + 3),
   if stk then 5 else ofN (3 - 2 * b.toNat),
   if stk then ofN (2 - 2 * b.toNat) else 0,
   if stk then ofN spn else ofN (1 - b.toNat),
   bF !stk, bF stk]

/-- **A P2OUT row**: `ctr lvl rest b acc low hi act e pow last islow ilast
    val nacc nlow nhi nlowr nhir em addr prev ptr`, level `l` of the call
    at `c` over the output bits `ob`, pushed over the stack `rest`. -/
def poutRow (c rest : Nat) (ob : List Bool) (l : Nat) : List F :=
  let b := ob.getD l false
  let last := l % 31 = 30
  let islow := decide (l % 31 < 27)
  let v := ofN (accN ob l + 2 ^ (l % 31) * b.toNat)
  let nlow := lowL ob l || (islow && b)
  let nhi := hiL ob l && (islow || b)
  let addr := c + (P2_BITS - 1) - l
  [ofN c, ofN l, ofN rest, bF b, ofN (accN ob l), bF (lowL ob l), bF (hiL ob l), 1, ofN (l / 31),
   ofN (2 ^ (l % 31)), bF (decide last), bF islow, bF (decide (l = P2_BITS - 1)), v, if last then 0 else v,
   bF nlow, bF nhi, if last then 0 else bF nlow, if last then 1 else bF nhi, bF (decide last),
   ofN addr, ofN (if l = P2_BITS - 1 then rest else addr - 1), ofN (P2Jet.bitPtr b)]

-- ---------------------------------------------------------------------------
-- The run
-- ---------------------------------------------------------------------------

/-- **A run of the circuit with the Poseidon2 jet**: the memory `A`, the
    jet's atom `J` and the comb's root `root`, the segments' roots
    `segRoots`, ends `e` and count `n`, and the rows.  Meaningful only for
    a run `AcceptsCP` accepts, which each theorem takes. -/
structure P2Run where
  A : List Cell
  J : Nat
  root : Nat
  segRoots : List Nat
  e : Nat → Nat
  n : Nat
  row : Nat → Air.Row

namespace P2Run

variable (R : P2Run)

/-- The run, padded by repeating its last row. -/
def rowQ (i : Nat) : Air.Row := rowP R.row R.e R.n i

/-- **Row `i` takes the jet's step on the comb**: it is no restart, within
    the run, and the jet's row takes it to the next. -/
def jetCAt (i : Nat) : Bool :=
  !isRestart R.e R.n i && decide (i < R.e (R.n - 1)) &&
    decide (P2Jet.p2Row R.A R.J R.root (R.row i) = some (R.row (i + 1)))

/-- **Row `i` takes the jet's step on the stack**, at the atom `J + 1`. -/
def jetSAt (i : Nat) : Bool :=
  !isRestart R.e R.n i && decide (i < R.e (R.n - 1)) &&
    decide (P2Jet.p2RowS R.A (R.J + 1) (R.row i) = some (R.row (i + 1)))

/-- **Row `i` takes the jet's step**, on the comb or on the stack. -/
def jetAt (i : Nat) : Bool := R.jetCAt i || R.jetSAt i

/-- A jet row's range checks: its reads of the atom and the two stack cells
    lie strictly below the counter, so `ctr - addr - 1` fits 24 bits; its
    fourth read is inactive. -/
def jetRange (r : Air.Row) (j : Nat) : Nat := if j < 3 then r.ctr - addrAt R.A r j - 1 else 0

/-- A jet row's stack below its inputs: on the comb the second stack cell's
    rest, on the stack what is left after the 496 inputs. -/
def jrest (i : Nat) : Nat :=
  if R.jetSAt i then ((popN (R.A.take (R.rowQ i).ctr) 497 (R.rowQ i).stk).getD ([], 0)).2
  else (fieldsAt R.A (R.rowQ i) 2).2

/-- A jet row's first stack cell under `k`: `s₁`. -/
def js1 (i : Nat) : Nat := (fieldsAt R.A (R.rowQ i) 1).2

/-- **The honest CPU row**: the composed CPU's, and on a jet row the
    selector `P2SEL`, the kinds cleared and its reads range-checked, its
    mode, the stack below its inputs and the input chain's start. -/
def cpuColP (i c : Nat) : F :=
  if c = P2SEL then bF (R.jetAt i)
  else if R.jetAt i = true ∧ SEL ≤ c ∧ c < SEL + NKINDS then 0
  else if R.jetAt i = true ∧ BITS ≤ c ∧ c < CPU_WIDTH then
    ofN ((R.jetRange (R.rowQ i) ((c - BITS) / RANGE_BITS) / 2 ^ ((c - BITS) % RANGE_BITS)) % 2)
  else if c = P2MODE then bF (R.jetSAt i)
  else if c = P2REST then (if R.jetAt i then ofN (R.jrest i) else 0)
  else if c = P2CM then bF (R.jetCAt i)
  else if c = P2SP0 then (if R.jetSAt i then ofN (R.js1 i) else if R.jetAt i then ofN (R.jrest i) else 0)
  else cpuColC R.A R.row R.e R.n R.segRoots i c

def cpuTableP (K : Nat) : Table := ⟨K, fun i c => R.cpuColP i c, fun _ _ => 0⟩

/-- A jet row's input bits: the slots' on the comb, the popped pointers' on
    the stack. -/
def jbits (i : Nat) : List Bool :=
  if R.jetSAt i then
    (P2Jet.ptrBits ((popN (R.A.take (R.rowQ i).ctr) 497 (R.rowQ i).stk).getD ([], 0)).1.tail).getD []
  else (P2Jet.bitsAt (R.A.take (R.rowQ i).ctr) P2Jet.slotAddrs).getD []

/-- Row `i`'s P2IN rows: a call's 496, else none. -/
def pinRowsAt (i : Nat) : List (List F) :=
  if R.jetAt i then
    (List.range P2_BITS).map (pinRow (R.rowQ i).ctr (R.jbits i) (R.jetSAt i) (R.js1 i) (R.jrest i))
  else []

/-- Row `i`'s P2OUT rows. -/
def poutRowsAt (i : Nat) : List (List F) :=
  if R.jetAt i then (List.range P2_BITS).map (poutRow (R.rowQ i).ctr (R.jrest i) (P2Jet.outBits (R.jbits i)))
  else []

/-- Row `i`'s Poseidon2 row. -/
def p2RowsAt (i : Nat) : List (List F) :=
  if R.jetAt i then [p2RowT (R.rowQ i).ctr (Poseidon2SKI.valsB (R.jbits i))] else []

def pinRows (K : Nat) : List (List F) := (List.range K).flatMap R.pinRowsAt
def poutRows (K : Nat) : List (List F) := (List.range K).flatMap R.poutRowsAt
def p2Rows (K : Nat) : List (List F) := (List.range K).flatMap R.p2RowsAt

def pinTable (K H : Nat) : Table := ⟨H, ofRows (R.pinRows K), fun _ _ => 0⟩
def poutTable (K H : Nat) : Table := ⟨H, ofRows (R.poutRows K), fun _ _ => 0⟩
/-- The Poseidon2 table: the calls' rows, then the padding row. -/
def p2Table (K H : Nat) : Table :=
  ⟨H, ofRows (R.p2Rows K ++ List.replicate (H - (R.p2Rows K).length) p2Pad), fun _ _ => 0⟩

/-- **The number of jet calls** among the first `K` rows. -/
def calls (K : Nat) : Nat := ((List.range K).filter R.jetAt).length

end P2Run

/-- **The honest witness table** on the circuit's preprocessed rows, the
    private cells from address `3`, after the slots `K`, `I`, `K I`. -/
def witTableP (A : List Cell) (N W : Nat) : Table :=
  ⟨(witRowsP N W).length, fun q col => witColG 3 A N W q col, fun q j => ((witRowsP N W).getD q []).getD j 0⟩

end Circuit

namespace Circuit

open B Air Compose CompM Mach

-- ---------------------------------------------------------------------------
-- The jet's row, inverted
-- ---------------------------------------------------------------------------

theorem rd_of_take {M : List Cell} {c a : Nat} {x : Cell} (h : (M.take c)[a]? = some x) : rd M c a = some x := by
  rw [List.getElem?_take] at h
  unfold rd
  split at h
  · next ha => rw [if_pos ha]; exact h
  · cases h

theorem outBits_length (bs : List Bool) (hl : bs.length = 496) : (P2Jet.outBits bs).length = 496 := by
  unfold P2Jet.outBits
  have hY := Poseidon2SKI.permute_len (Poseidon2SKI.valsB bs) (Poseidon2SKI.valsB_length bs)
  generalize Poseidon2.permute (Poseidon2SKI.valsB bs) = ys at hY ⊢
  have : ∀ ys : List Nat, (ys.flatMap (BitArith.bitsOf 31)).length = 31 * ys.length := fun ys => by
    induction ys with
    | nil => rfl
    | cons y ys ih => rw [List.flatMap_cons, List.length_append, Poseidon2SKI.bitsOf_length, ih, List.length_cons]; omega
  rw [this, hY]

/-- **What a jet row reads and writes**: the atom at the head, the stack
    cells `cons k s₁` and `s₁ ↦ cons root rest`, the slots, the bits, the
    outputs' stack cells, and the next row. -/
theorem p2Row_inv {M : List Cell} {j root : Nat} {r r' : Air.Row} (h : P2Jet.p2Row M j root r = some r') :
    rd M r.ctr r.hd = some (.atom j) ∧ ∃ k s1 rest bs, rd M r.ctr r.stk = some (.cons k s1) ∧
      rd M r.ctr s1 = some (.cons root rest) ∧ P2Jet.slotsOK (M.take r.ctr) = true ∧
      P2Jet.bitsAt (M.take r.ctr) P2Jet.slotAddrs = some bs ∧ bs.length = 496 ∧
      wrs M r.ctr (P2Jet.pushR r.ctr rest (P2Jet.outBits bs).reverse) = true ∧
      r' = ⟨k, r.ctr + 495, r.ctr + 496⟩ := by
  unfold P2Jet.p2Row at h
  dsimp only at h
  cases hhd : (M.take r.ctr)[r.hd]? with
  | none => rw [hhd] at h; cases h
  | some cell =>
    rw [hhd] at h
    cases cell with
    | atom j' =>
      dsimp only at h
      by_cases hcond : j' = j ∧ P2Jet.slotsOK (M.take r.ctr) = true
      · rw [if_pos hcond] at h
        obtain ⟨rfl, hs⟩ := hcond
        cases hpop : popN (M.take r.ctr) 2 r.stk with
        | none => rw [hpop] at h; cases h
        | some q =>
          obtain ⟨qs, rest⟩ := q
          rw [hpop] at h
          match qs, h with
          | [k, β], h =>
            dsimp only at h
            by_cases hβ : β = root
            · rw [if_pos hβ] at h
              cases hbits : P2Jet.bitsAt (M.take r.ctr) P2Jet.slotAddrs with
              | none => rw [hbits] at h; cases h
              | some bs =>
                rw [hbits] at h
                dsimp only at h
                have hbl : bs.length = 496 := by
                  rw [P2Jet.bitsAt_length hbits, P2Jet.slotAddrs, List.length_range']
                cases hw : wrs M r.ctr (P2Jet.pushR r.ctr rest (P2Jet.outBits bs).reverse) with
                | false => rw [hw] at h; cases h
                | true =>
                  rw [hw] at h
                  cases h
                  -- the stack's two cells
                  unfold popN at hpop
                  cases hc1 : (M.take r.ctr)[r.stk]? with
                  | none => rw [hc1] at hpop; cases hpop
                  | some c1 =>
                    rw [hc1] at hpop
                    cases c1 with
                    | cons x s1 =>
                      dsimp only at hpop
                      unfold popN at hpop
                      cases hc2 : (M.take r.ctr)[s1]? with
                      | none => rw [hc2] at hpop; cases hpop
                      | some c2 =>
                        rw [hc2] at hpop
                        cases c2 with
                        | cons y s2 =>
                          simp only [popN, Option.map_some, Option.some.injEq, Prod.mk.injEq, List.cons.injEq,
                            and_true] at hpop
                          obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hpop
                          subst hβ
                          refine ⟨rd_of_take hhd, x, s1, s2, bs, rd_of_take hc1, rd_of_take hc2, hs, rfl, hbl, hw, ?_⟩
                          rw [outBits_length bs hbl]
                          rfl
                        | _ => cases hpop
                    | _ => cases hpop
            · rw [if_neg hβ] at h; cases h
          | [], h => cases h
          | [_], h => cases h
          | _ :: _ :: _ :: _, h => cases h
      · rw [if_neg hcond] at h; cases h
    | _ => cases h

/-- A jet row halts, to the base classification: its head is an atom. -/
theorem p2Row_halt {M : List Cell} {j root : Nat} {r r' : Air.Row} (h : P2Jet.p2Row M j root r = some r') :
    haltRow M r = true := by
  have h1 := (p2Row_inv h).1
  simp only [haltRow, h1]

theorem popN_len {H : List Cell} : ∀ {n s : Nat} {ps : List Nat} {r : Nat}, popN H n s = some (ps, r) →
    ps.length = n
  | 0, _, ps, r, h => by simp [popN] at h; rw [h.1]; rfl
  | n + 1, s, ps, r, h => by
    unfold popN at h
    cases hc : H[s]? with
    | none => rw [hc] at h; cases h
    | some c =>
      rw [hc] at h
      cases c with
      | cons x s' =>
        dsimp only at h
        cases hq : popN H n s' with
        | none => rw [hq] at h; cases h
        | some q =>
          rw [hq] at h
          simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
          rw [← h.1, List.length_cons, popN_len hq]
      | _ => cases h

/-- **What a stack row reads and writes**: the atom at the head, the stack
    cell `cons k s₁`, the slots, the 496 inputs in consecutive cells from
    `s₁`, their bits, the outputs' stack cells, and the next row. -/
theorem p2RowS_inv {M : List Cell} {j : Nat} {r r' : Air.Row} (h : P2Jet.p2RowS M j r = some r') :
    rd M r.ctr r.hd = some (.atom j) ∧ ∃ k ps rest bs,
      popN (M.take r.ctr) 497 r.stk = some (k :: ps, rest) ∧ P2Jet.slotsOK (M.take r.ctr) = true ∧
      P2Jet.stackRun (M.take r.ctr) r.stk = true ∧ P2Jet.ptrBits ps = some bs ∧ bs.length = 496 ∧
      wrs M r.ctr (P2Jet.pushR r.ctr rest (P2Jet.outBits bs).reverse) = true ∧
      r' = ⟨k, r.ctr + 495, r.ctr + 496⟩ := by
  unfold P2Jet.p2RowS at h
  dsimp only at h
  cases hhd : (M.take r.ctr)[r.hd]? with
  | none => rw [hhd] at h; cases h
  | some cell =>
    rw [hhd] at h
    cases cell with
    | atom j' =>
      dsimp only at h
      by_cases hcond : j' = j ∧ P2Jet.slotsOK (M.take r.ctr) = true ∧ P2Jet.stackRun (M.take r.ctr) r.stk = true
      · rw [if_pos hcond] at h
        obtain ⟨rfl, hs, hrun⟩ := hcond
        cases hpop : popN (M.take r.ctr) 497 r.stk with
        | none => rw [hpop] at h; cases h
        | some q =>
          obtain ⟨qs, rest⟩ := q
          rw [hpop] at h
          match qs, h with
          | k :: ps, h =>
            dsimp only at h
            cases hbits : P2Jet.ptrBits ps with
            | none => rw [hbits] at h; cases h
            | some bs =>
              rw [hbits] at h
              dsimp only at h
              have hpl : ps.length = 496 := by
                have := popN_len hpop
                simp only [List.length_cons] at this; omega
              have hbl : bs.length = 496 := by rw [P2Jet.ptrBits_length hbits, hpl]
              cases hw : wrs M r.ctr (P2Jet.pushR r.ctr rest (P2Jet.outBits bs).reverse) with
              | false => rw [hw] at h; cases h
              | true =>
                rw [hw] at h
                cases h
                refine ⟨rd_of_take hhd, k, ps, rest, bs, rfl, hs, hrun, hbits, hbl, hw, ?_⟩
                rw [outBits_length bs hbl]
                rfl
          | [], h => cases h
      · rw [if_neg hcond] at h; cases h
    | _ => cases h

/-- A stack row's two stack reads: `cons k s₁`, and the first input's cell at `s₁`. -/
theorem p2RowS_reads {M : List Cell} {j : Nat} {r r' : Air.Row} (h : P2Jet.p2RowS M j r = some r') :
    ∃ k s1 x s2, rd M r.ctr r.stk = some (.cons k s1) ∧ rd M r.ctr s1 = some (.cons x s2) := by
  obtain ⟨_, k, ps, rest, bs, hpop, _⟩ := p2RowS_inv h
  unfold popN at hpop
  cases hc1 : (M.take r.ctr)[r.stk]? with
  | none => rw [hc1] at hpop; cases hpop
  | some c1 =>
    rw [hc1] at hpop
    cases c1 with
    | cons x1 s1 =>
      dsimp only at hpop
      unfold popN at hpop
      cases hc2 : (M.take r.ctr)[s1]? with
      | none => rw [hc2] at hpop; cases hpop
      | some c2 =>
        rw [hc2] at hpop
        cases c2 with
        | cons x2 s2 => exact ⟨x1, s1, x2, s2, rd_of_take hc1, rd_of_take hc2⟩
        | _ => cases hpop
    | _ => cases hpop

/-- A stack row halts, to the base classification: its head is an atom. -/
theorem p2RowS_halt {M : List Cell} {j : Nat} {r r' : Air.Row} (h : P2Jet.p2RowS M j r = some r') :
    haltRow M r = true := by
  have h1 := (p2RowS_inv h).1
  simp only [haltRow, h1]

end Circuit

namespace Circuit

open B Air Compose CompM Mach

-- ---------------------------------------------------------------------------
-- The run's rows
-- ---------------------------------------------------------------------------

namespace P2Run

variable {R : P2Run} {m0 : Mach} {nilA : Nat}
  (hA : AcceptsCP R.A m0 [] [] R.J R.root R.segRoots nilA R.n R.e R.row) {K : Nat} (hK : R.e (R.n - 1) < K)
include hA

/-- A row within the run, no restart, steps plainly or by the jet. -/
theorem norm_row {i : Nat} (hi : i < R.e (R.n - 1)) (hr : isRestart R.e R.n i = false) :
    NormRowP R.A [] [] R.J R.root (R.row i) (R.row (i + 1)) := by
  refine hA.trans i hi (fun j hj h' => ?_)
  rw [isRestart_iff.2 ⟨j, hj, h'.symm⟩] at hr; cases hr

include hK in
/-- **The run gives what the composed CPU's lemmas use**: every padded row
    steps or halts, a jet row halting to the base classification. -/
theorem runC : RunC R.A R.n R.e R.row K := by
  have hn := hA.npos
  refine ⟨hn, hA.emono, hA.ends, hK, fun i _ => ?_⟩
  unfold rowP
  split
  · next hle =>
    rcases Nat.lt_or_ge i (R.e (R.n - 1)) with hlt | hge
    · cases hr : isRestart R.e R.n i with
      | false =>
        rcases norm_row hA hlt hr with (h | ⟨_, _, hm, _, _⟩ | h) | h | h
        · exact .inl (by rw [h]; rfl)
        · exact absurd hm List.not_mem_nil
        · exact .inr h.1
        · exact .inr (p2Row_halt h)
        · exact .inr (p2RowS_halt h)
      | true =>
        obtain ⟨j, hj, rfl⟩ := isRestart_iff.1 hr
        obtain ⟨h1, h2⟩ := hA.ends j (by omega)
        exact .inr (by simp only [haltRow, h1, short, h2])
    · rw [show i = R.e (R.n - 1) by omega]
      obtain ⟨h1, h2⟩ := hA.ends (R.n - 1) (by omega)
      exact .inr (by simp only [haltRow, h1, short, h2])
  · obtain ⟨h1, h2⟩ := hA.ends (R.n - 1) (by omega)
    exact .inr (by simp only [haltRow, h1, short, h2])

omit hA in
theorem rowQ_of_le {i : Nat} (hi : i ≤ R.e (R.n - 1)) : R.rowQ i = R.row i := by
  unfold rowQ rowP; rw [if_pos hi]

omit hA in
/-- **A comb jet row**: no restart, within the run, the jet's row to the
    next. -/
theorem jetCAt_spec {i : Nat} (h : R.jetCAt i = true) :
    isRestart R.e R.n i = false ∧ i < R.e (R.n - 1) ∧
      P2Jet.p2Row R.A R.J R.root (R.rowQ i) = some (R.rowQ (i + 1)) := by
  unfold jetCAt at h
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at h
  obtain ⟨⟨hr, hi⟩, hp⟩ := h
  refine ⟨hr, hi, ?_⟩
  rw [rowQ_of_le (by omega), rowQ_of_le (by omega)]
  exact hp

omit hA in
/-- **A stack jet row**: no restart, within the run, the stack row to the
    next. -/
theorem jetSAt_spec {i : Nat} (h : R.jetSAt i = true) :
    isRestart R.e R.n i = false ∧ i < R.e (R.n - 1) ∧
      P2Jet.p2RowS R.A (R.J + 1) (R.rowQ i) = some (R.rowQ (i + 1)) := by
  unfold jetSAt at h
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at h
  obtain ⟨⟨hr, hi⟩, hp⟩ := h
  refine ⟨hr, hi, ?_⟩
  rw [rowQ_of_le (by omega), rowQ_of_le (by omega)]
  exact hp

omit hA in
/-- A row is not both a comb and a stack jet row: their atoms differ. -/
theorem not_jetC_jetS {i : Nat} (hc : R.jetCAt i = true) (hs : R.jetSAt i = true) : False := by
  have h1 := (p2Row_inv (R.jetCAt_spec hc).2.2).1
  have h2 := (p2RowS_inv (R.jetSAt_spec hs).2.2).1
  rw [h1] at h2
  injection h2 with h3
  injection h3 with h4
  omega

omit hA in
/-- **A jet row**: no restart, within the run, the jet's row on the comb or
    on the stack to the next. -/
theorem jetAt_spec {i : Nat} (h : R.jetAt i = true) :
    isRestart R.e R.n i = false ∧ i < R.e (R.n - 1) ∧
      (P2Jet.p2Row R.A R.J R.root (R.rowQ i) = some (R.rowQ (i + 1)) ∨
        P2Jet.p2RowS R.A (R.J + 1) (R.rowQ i) = some (R.rowQ (i + 1))) := by
  unfold jetAt at h
  rcases Bool.or_eq_true _ _ ▸ h with hc | hs
  · obtain ⟨a, b, c⟩ := R.jetCAt_spec hc; exact ⟨a, b, .inl c⟩
  · obtain ⟨a, b, c⟩ := R.jetSAt_spec hs; exact ⟨a, b, .inr c⟩

/-- **A row within the run that is no jet row and no restart steps
    plainly.** -/
theorem plain_row {i : Nat} (hi : i < R.e (R.n - 1)) (hr : isRestart R.e R.n i = false) (hj : R.jetAt i = false) :
    NormRow R.A [] [] (R.row i) (R.row (i + 1)) := by
  rcases norm_row hA hi hr with h | h | h
  · exact h
  · exfalso
    have : R.jetAt i = true := by
      unfold jetAt jetCAt
      simp only [hr, Bool.not_false, Bool.true_and, decide_eq_true hi, decide_eq_true h, Bool.true_or]
    rw [hj] at this; cases this
  · exfalso
    have : R.jetAt i = true := by
      unfold jetAt jetSAt
      simp only [hr, Bool.not_false, Bool.true_and, decide_eq_true hi, decide_eq_true h, Bool.or_true]
    rw [hj] at this; cases this

end P2Run

-- ---------------------------------------------------------------------------
-- The honest CPU's columns
-- ---------------------------------------------------------------------------

namespace P2Run

variable (R : P2Run)

theorem cpuP_col {K i : Nat} (hi : i < K) (c : Nat) : (col c).eval ((R.cpuTableP K).env i) = R.cpuColP i c := by
  show (R.cpuTableP K).main ((i + 0) % K) c = _
  rw [Nat.add_zero, Nat.mod_eq_of_lt hi]; rfl

/-- Off the jet rows, the honest CPU row is the composed one. -/
theorem cpuColP_plain {i : Nat} (hj : R.jetAt i = false) (c : Nat) :
    R.cpuColP i c = cpuColC R.A R.row R.e R.n R.segRoots i c := by
  have hc0 : R.jetCAt i = false := by
    unfold jetAt at hj; cases h : R.jetCAt i <;> simp_all
  have hs0 : R.jetSAt i = false := by
    unfold jetAt at hj; cases h : R.jetSAt i <;> simp_all
  have zc : ∀ c', ROOT + 1 ≤ c' → cpuColC R.A R.row R.e R.n R.segRoots i c' = 0 := fun c' hc' => by
    unfold cpuColC
    simp only [ROOT, CNT, RS] at hc'
    rw [if_neg (by omega), if_neg (by simp only [RS]; omega), if_neg (by simp only [CNT, RS]; omega),
      if_neg (by simp only [ROOT, RS]; omega)]
  unfold cpuColP
  by_cases hc : c = P2SEL
  · subst hc; rw [if_pos rfl, hj, zc _ (by unfold P2SEL; omega)]; rfl
  rw [if_neg hc, hj, if_neg (fun h => nomatch h.1), if_neg (fun h => nomatch h.1)]
  by_cases hm : c = P2MODE
  · subst hm; rw [if_pos rfl, hs0, zc _ (by unfold P2MODE P2SEL; omega)]; rfl
  rw [if_neg hm]
  by_cases hr : c = P2REST
  · subst hr; rw [if_pos rfl, zc _ (by unfold P2REST P2SEL; omega)]; rfl
  rw [if_neg hr]
  by_cases hcm : c = P2CM
  · subst hcm; rw [if_pos rfl, hc0, zc _ (by unfold P2CM P2SEL; omega)]; rfl
  rw [if_neg hcm]
  by_cases hsp : c = P2SP0
  · subst hsp; rw [if_pos rfl, hs0, zc _ (by unfold P2SP0 P2SEL; omega)]; rfl
  rw [if_neg hsp]

/-- Off the jet rows, the two tables read the same at the current row. -/
theorem cpuP_env_plain {K i : Nat} (hi : i < K) (hj : R.jetAt i = false) :
    ∀ a, nowAtom a = true → (R.cpuTableP K).env i a = (cpuTableC R.A R.row R.e R.n R.segRoots K).env i a := by
  intro a ha
  cases a with
  | main o c =>
    cases o with
    | zero =>
      show (R.cpuTableP K).main ((i + 0) % K) c = (cpuTableC R.A R.row R.e R.n R.segRoots K).main ((i + 0) % K) c
      rw [Nat.add_zero, Nat.mod_eq_of_lt hi]
      exact R.cpuColP_plain hj c
    | succ o => simp [nowAtom] at ha
  | _ => simp [nowAtom] at ha

end P2Run

end Circuit
