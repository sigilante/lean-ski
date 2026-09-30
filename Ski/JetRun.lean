import Ski.JetTable

/-!
# Running a heap with jets

`runJ` runs a machine to a halt, instantiating at every licensed root that
has enough arguments, with the constraint's own definitions (`Air.popR`,
`Air.icells`), and counts the planned tables' rows: one CPU row per
transition or instantiation, one POP row per argument, one INSTW row per
written cell.  Its rows, as a table, are what `Air.checkJA` checks.  Used
by `lake exe jetcost` over the corpus and by `lake exe skilark` over a
composed heap.
-/

namespace JetRun

open Mach Air

structure Cost where
  cpu : Nat := 0
  pop : Nat := 0
  instw : Nat := 0
  insts : Nat := 0
  cells : Nat := 0

def Cost.rows (c : Cost) : Nat := c.cpu + c.pop + c.instw

/-- `Air.stepG` over an array heap, the counter its size. -/
def stepA (heap : Array Cell) (hd stk : Nat) : Option (Nat × Nat × List Cell) :=
  stepG (fun a => heap[a]?) heap.size hd stk

/-- Run to a halt within `fuel` steps, instantiating at every root that has
    enough arguments.  The heap is its own mutable variable, so pushes do
    not copy it. -/
def runJ (roots : Std.HashMap Nat Jet) (heap0 : Array Cell) (hd0 stk0 : Nat) (fuel : Nat) :
    Option ((Array Cell × Nat × Nat) × Cost × Array Air.Row) := Id.run do
  let mut heap := heap0
  let mut hd := hd0
  let mut stk := stk0
  let mut c : Cost := {}
  let mut rows : Array Air.Row := #[]
  for _ in [0:fuel] do
    rows := rows.push ⟨hd, stk, heap.size⟩
    let inst? := match roots[hd]? with
      | some J => (popR (fun a => heap[a]?) heap.size J.xs.length stk).map
          fun (p : List Nat × Nat) => (J, p.1, p.2)
      | none => none
    match inst? with
    | some (J, ps, r) =>
      let (cs, root) := icells (overrideN J.genv J.xs ps) heap.size J.body
      for w in cs do
        heap := heap.push w
      c := { c with cpu := c.cpu + 1, pop := c.pop + J.xs.length, instw := c.instw + cs.length,
                    insts := c.insts + 1, cells := c.cells + cs.length }
      hd := root
      stk := r
    | none =>
      match stepA heap hd stk with
      | some (hd', stk', ws) =>
        for w in ws do
          heap := heap.push w
        c := { c with cpu := c.cpu + 1, cells := c.cells + ws.length }
        hd := hd'
        stk := stk'
      | none => return some ((heap, hd, stk), c, rows)
  return none

/-- The halted state's head cell and number of arguments. -/
def shape (s : Array Cell × Nat × Nat) : Option Cell × Nat := Id.run do
  let (heap, hd, stk) := s
  let mut n := 0
  let mut p := stk
  for _ in [0:heap.size] do
    match heap[p]? with
    | some (.cons _ r) => n := n + 1; p := r
    | _ => break
  return (heap[hd]?, n)

def rootMap (roots : List (Nat × Nat)) (jets : List Jet) : Std.HashMap Nat Jet :=
  roots.foldl (fun m (a, j) => match jets[j]? with
    | some J => m.insert a J
    | none => m) {}

def pct (a b : Nat) : String :=
  if b == 0 then "-" else s!"{(a * 1000 / b : Nat) / 10}.{(a * 1000 / b : Nat) % 10}%"

end JetRun
