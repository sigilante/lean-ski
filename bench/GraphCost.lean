import Ski.Graph
import Ski.Corpus
open Term Graph

/-!
# Graph reduction against L1 on the corpus

Runs every corpus row on the update-in-place machine (`Graph.gstep`, the
step `graph_sound` and `graph_complete` are proved for) and prints its
contractions beside L1's, with the transitions and cells it allocated,
and whether its value has L1's head and arity.  `graph_sound` bounds its contractions by L1's;
this measures how far below.
-/

/-- The run, tail-recursive: halted state, contractions, transitions. -/
def loop : Nat → GM → Nat → Nat → Option (GM × Nat × Nat)
  | 0, _, _, _ => none
  | k + 1, m, c, s =>
    match gstep m with
    | none => some (m, c, s)
    | some (m', b) => loop k m' (if b then c + 1 else c) (s + 1)

/-- The head combinator under an address and its number of arguments;
    a decoding of a shared graph can be exponentially larger, so the value
    is compared by its spine, which `graph_sound` fixes (`u ↠ v` between
    weak head normal forms keeps the head and the arity). -/
def spineG (h : Heap) : Nat → Nat → Option (Term × Nat)
  | 0, _ => none
  | f + 1, a =>
    match h[a]? with
    | some .S => some (.S, 0)
    | some .K => some (.K, 0)
    | some .I => some (.I, 0)
    | some (.app x _) => (spineG h f x).map fun (t, k) => (t, k + 1)
    | some (.ind p) => spineG h f p
    | none => none

def spineT : Term → Term × Nat
  | .app f _ => let (t, k) := spineT f; (t, k + 1)
  | t => (t, 0)

def main : IO UInt32 := do
  let out ← IO.getStdout
  let mut bad := 0
  for row in corpus do
    let m0 := gload row.term
    let cells0 := m0.heap.length
    match loop 50_000_000 m0 0 0, runF 5_000_000 row.term with
    | some (m, c, s), some (u, n) =>
      let same := spineG m.heap (m.heap.length + 1) m.root == some (spineT u)
      let ok := c ≤ n && same
      out.putStrLn s!"{if ok then "ok  " else "FAIL"} {row.name}: {c} contractions (L1 {n}), {s} transitions, {m.heap.length - cells0} cells allocated, head and arity {if same then "L1's" else "DIFFER"}  -- {row.joy}"
      out.flush
      if !ok then bad := bad + 1
    | _, _ =>
      out.putStrLn s!"FAIL {row.name}: out of fuel"
      bad := bad + 1
  return if bad == 0 then 0 else 1
