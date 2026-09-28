import Ski.Corpus
import Ski.Air
open Term

/-!
The AIR's size on the conformance corpus.  Run with
`lake build aircost && lake exe aircost`.

The machine here is the proved rule table `Air.stepG` with the heap held in
an `Array` rather than a `List`; the loaded heap is `Mach.load`'s.  Before
printing a row, its contraction count must equal the reference reducer's,
and the final state's spine (head combinator and argument count) must be
the spine of `runF`'s value.

Per row: the term's leaves; contractions and unwinds; the AIR's rows at the
least budget, one per transition plus the final halt row (`n + 1`); the
memory table, the loaded heap and the cells the run writes; rows per
contraction.  Nothing prints a reduced term.
-/

def leaves : Term → Nat
  | .app f a => leaves f + leaves a
  | _ => 1

/-- A term's head combinator and argument count. -/
def spine : Term → Option Nat × Nat
  | .app f _ => let (h, n) := spine f; (h, n + 1)
  | .S => (some 0, 0)
  | .K => (some 1, 0)
  | .I => (some 2, 0)

def headOf : Cell → Option Nat
  | .S => some 0
  | .K => some 1
  | .I => some 2
  | _ => none

/-- The stack's length, following cons cells (bounded by the heap size). -/
def stackLen (heap : Array Cell) : Nat → Nat → Nat
  | _, 0 => 0
  | s, f + 1 =>
    match heap[s]? with
    | some (.cons _ r) => stackLen heap r f + 1
    | _ => 0

/-- Run to a halt: transitions, contractions, final heap, head, stack. -/
partial def run (heap : Array Cell) (hd stk n c : Nat) : Nat × Nat × Array Cell × Nat × Nat :=
  match Air.stepG (fun a => heap[a]?) heap.size hd stk with
  | none => (n, c, heap, hd, stk)
  | some (h, s, ws) =>
    let contraction := match heap[hd]? with
      | some (.app _ _) => 0
      | _ => 1
    run (heap ++ ws.toArray) h s (n + 1) (c + contraction)

def main : IO Unit := do
  IO.println "row              leaves  contr  unwind    rows  loaded  written  memory  rows/contr"
  for r in corpus do
    let m := Mach.load r.term
    let (n, c, heap, hd, stk) := run m.heap.toArray m.hd m.stk 0 0
    if c != r.steps then
      throw (IO.userError s!"{r.name}: {c} contractions, reference {r.steps}")
    -- the final state's spine must be runF's value's: the same head
    -- combinator and the same number of arguments (a full read-back would
    -- unfold the shared heap, exponentially)
    match runF (r.steps + 1) r.term with
    | some (u, _) =>
      if spine u != (heap[hd]?.bind headOf, stackLen heap stk heap.size) then
        throw (IO.userError s!"{r.name}: final spine differs from runF's value")
    | none => throw (IO.userError s!"{r.name}: runF has no value")
    let loaded := m.heap.length
    let written := heap.size - loaded
    let ratio := (Float.ofNat (n + 1)) / (Float.ofNat c)
    IO.println s!"{r.name.pushn ' ' (16 - r.name.length)} {leaves r.term}  {c}  {n - c}  {n + 1}  {loaded}  {written}  {heap.size}  {ratio}"
