import Ski.JetRun
open Term

/-!
What supercombinator jets save on the corpus.

Each corpus term is loaded and run to a halt three ways, and the rows of
the planned tables are counted (`bench/plonky3/DESIGN.md` §2):

- *plain*: machine transitions only, one CPU row each;
- *whole bodies*: instantiations at licensed roots of jets whose bodies
  keep their closed subterms, so each instantiation writes them;
- *globals*: the jet table `lake exe jets emit` publishes
  (`JetTable.jetTable`), whose bodies name closed subterms as globals.

An instantiation is executed with the constraint's own definitions
(`Air.popR`, `Air.icells`), at every licensed root with enough arguments.
It costs one CPU row, one POP row per argument and one INSTW row per
written cell; a machine transition costs one CPU row.  Memory is the cells
written.  Each jetted run must halt with the plain run's head and number
of arguments (`jet_run_shape`), and its rows and memory, as a table, must
pass `Air.checkJA` against the published jet table.

Run with `lake build jetcost && lake exe jetcost`.
-/

open Mach Air JetTable JetRun

def line (label : String) (c p : Cost) (same : Bool) : String :=
  s!"  {label}  rows {c.rows} = {c.cpu} cpu + {c.pop} pop + {c.instw} instw ({pct c.rows p.rows})  cells {c.cells} ({pct c.cells p.cells})  {c.insts} insts  {if same then "same head and arity" else "SHAPE DIFFERS"}"

def main : IO UInt32 := do
  let tmpls := allTemplates
  let fuel := 10000000
  let mut bad := 0
  for row in corpus do
    let m := load row.term
    let heap := m.heap.toArray
    let some (sp, cp, _) := runJ {} heap m.hd m.stk fuel
      | IO.println s!"{row.name}: the plain run did not halt"; bad := bad + 1; continue
    let (rw, jw) := jetTable m.heap tmpls (globals := false)
    let (rg, jg) := jetTable m.heap tmpls
    let some (sw, cw, _) := runJ (rootMap rw jw) heap m.hd m.stk fuel
      | IO.println s!"{row.name}: the whole-body run did not halt"; bad := bad + 1; continue
    let some (sg, cg, rowsg) := runJ (rootMap rg jg) heap m.hd m.stk fuel
      | IO.println s!"{row.name}: the jetted run did not halt"; bad := bad + 1; continue
    let okw := shape sw == shape sp
    let okg := shape sg == shape sp
    -- The jetted table, checked against the AIR with instantiation rows.
    let accepted := checkJA sg.1 m rg jg rowsg.toList
    if !(okw && okg && accepted) then bad := bad + 1
    IO.println s!"{row.name}: {rg.length} licensed roots, {jg.length} jets, a {heap.size}-cell loaded heap"
    IO.println s!"  plain          rows {cp.rows}  cells {cp.cells}"
    IO.println (line "whole bodies" cw cp okw)
    IO.println (line "globals     " cg cp okg)
    IO.println s!"  the jetted table ({rowsg.size} rows): {if accepted then "accepted by Air.checkJA" else "REJECTED by Air.checkJA"}"
  return (if bad == 0 then 0 else 1)
