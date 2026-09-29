import Ski.WitnessExamples
import Ski.WitnessText
open Term

/-!
Statements over a hidden term, for the Plonky3 prover, and the check of
their tables (`Ski/Witness.lean`).

- `witness emit DIR` writes, for each example atom (`neg`, `sat`,
  `Ski/WitnessExamples.lean`), `DIR/<name>/`: `public.txt`, the witness
  machine with the region blank, which the verifier sees; `witness.txt`,
  the region of the honest realizer, which only the prover sees; and
  two regions for the tamper tests: `witness_wrong.txt`, a well-formed
  region holding a term that fails the atom, and `witness_forged.txt`,
  the honest region with its first cell an application pointing forward,
  which the run never reads.
- `witness statement PUBLIC` checks that a statement file is exactly the
  witness machine of the atom it names, for the region size it names:
  what the verifier must check before it trusts `public.txt`.  `-` reads
  stdin.
- `witness check PUBLIC TABLE...` checks tables the prover wrote with
  `Wit.witCheck`, against the statement's atom and region size.  `ACCEPT`
  means the table's region holds a realizer of the atom
  (`Wit.witCheck_realizes`).

**`public.txt`**: `V <term>`, `x <term>` (prefix form, `` ` `` for
application), `W <size>`, then `hd stk ctr`, then `ctr` cells, one per
line, a region cell as `W`.  **A region**: `W` cells, one per line.
**A table**: the `V`, `x` and `W` lines, then the number of memory cells
and the cells, then the number of rows and `hd stk ctr` per row.
-/

open Mach Wit WitEx

open WitnessText

def regionText (ws : List Cell) : String :=
  ws.foldl (fun s c => s ++ cellText c ++ "\n") ""

/-- The examples: name, verifier, input, region size, the honest realizer,
    and a term that fails the atom (`neg_not_I`, `sat_not_TTT`). -/
def examples : List (String × Term × Term × Nat × Term × Term) :=
  [("neg", negV, x0, 32, negW, I), ("sat", satV, x0, 32, satW, triple T T T)]

def emit (dir : String) : IO UInt32 := do
  for (name, V, x, W, w, bad) in examples do
    let d := s!"{dir}/{name}"
    IO.FS.createDirAll d
    let some good := regionOf W w | do IO.println s!"{name}: the witness does not fit"; return 1
    let some wrong := regionOf W bad | do IO.println s!"{name}: the wrong witness does not fit"; return 1
    -- The honest region with its first cell pointing forward: never read.
    let forged := good.set 0 (.app (W - 1) (W - 1))
    IO.FS.writeFile s!"{d}/public.txt" (publicText V x W)
    IO.FS.writeFile s!"{d}/witness.txt" (regionText good)
    IO.FS.writeFile s!"{d}/witness_wrong.txt" (regionText wrong)
    IO.FS.writeFile s!"{d}/witness_forged.txt" (regionText forged)
    let m := wMachine good (V ⬝ x)
    IO.println s!"{name}: region {W} cells (witness {(build [] w).1.length}); heap {m.heap.length} cells"
  return 0

def statement (path : String) : IO UInt32 := do
  let text ← if path == "-" then (← IO.getStdin).readToEnd else IO.FS.readFile path
  match statementOfText text with
  | some (V, x, W) =>
    IO.println s!"STATEMENT {path}: a realizer of atom {termText V} {termText x}, in {W} cells"
    return 0
  | none =>
    IO.println s!"NOT A STATEMENT {path}"
    return 1

/-- A table: its statement lines, the memory and the rows. -/
def parseTable (ls : List String) : Option (Term × Term × Nat × Array Cell × List Air.Row) := do
  match ls with
  | vl :: xl :: wl :: nl :: rest =>
    let V ← match words vl with
      | ["V", t] => parseTerm t
      | _ => none
    let x ← match words xl with
      | ["x", t] => parseTerm t
      | _ => none
    let W ← match words wl with
      | ["W", n] => n.toNat?
      | _ => none
    let n ← nl.trimAscii.toString.toNat?
    let cells ← (rest.take n).mapM (fun l => parseCell (words l))
    if cells.length != n then none
    match rest.drop n with
    | kl :: rest2 =>
      let k ← kl.trimAscii.toString.toNat?
      let rows ← (rest2.take k).mapM (fun l => parseRow (words l))
      if rows.length != k then none
      if !(rest2.drop k).isEmpty then none
      some (V, x, W, cells.toArray, rows)
    | [] => none
  | _ => none

def check (pub : String) (paths : List String) : IO UInt32 := do
  let some (V, x, W) := statementOfText (← IO.FS.readFile pub)
    | do IO.println s!"NOT A STATEMENT {pub}"; return 1
  let mut bad := 0
  for path in paths do
    let text ← match ← (IO.FS.readFile path).toBaseIO with
      | .ok t => pure t
      | .error _ => pure ""
    let ls := (text.splitOn "\n").filter (fun l => !l.trimAscii.toString.isEmpty)
    match parseTable ls with
    | none =>
      IO.println s!"MALFORMED {path}"
      bad := bad + 1
    | some (V', x', W', A, rows) =>
      if V' != V || x' != x || W' != W then
        IO.println s!"REJECT {path} (not the statement of {pub})"
        bad := bad + 1
      else if witCheck (V ⬝ x) W A rows then
        IO.println s!"ACCEPT {path}: its region holds a realizer of atom {termText V} {termText x} ({rows.length} rows, {A.size} cells)"
      else
        IO.println s!"REJECT {path}"
        bad := bad + 1
  return (if bad == 0 then 0 else 1)

def main (args : List String) : IO UInt32 := do
  match args with
  | ["emit", dir] => emit dir
  | ["statement", pub] => statement pub
  | "check" :: pub :: paths => check pub paths
  | _ =>
    IO.eprintln "usage: witness emit DIR | witness statement PUBLIC | witness check PUBLIC TABLE..."
    return 2
